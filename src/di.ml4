(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Refiner
open Tactics
open Term
open Names
open Tacmach
open Declarations
open Tacexpr
open Pp
open Genarg
open Misctypes

DECLARE PLUGIN "di"

exception DIPatError of string

let get_inductive (c:constr) =
  match kind_of_term c with
  | Ind i -> Some i
  | App (ac, _) ->
    (match kind_of_term ac with
     | Ind i -> Some i
     | _ -> None)
  | _ -> None

let is_dependent (c:constr) =
  match kind_of_term c with
  | App _ -> true
  | _ -> false

let get_des_ids (hyp_type:constr) (id:identifier) (num_params:int) =
  match kind_of_term hyp_type with
  | Ind _ -> []
  | App (_, a) ->
    let len = Array.length a in
    let rec extract_id c =
      (
      match kind_of_term c with
      | (Rel _ | Sort _ | Const _ | Construct _ | Ind _ | Prod _ | LetIn _ | Lambda _
         | Cast _ | Evar _ | Meta _ | Case _ | Fix _ | CoFix _ | Proj _) -> None
      | Var id -> Some id
      | App (_,al) ->
                      (Array.fold_left
                             (fun a c ->
                                match a with
                                | None -> (extract_id c)
                                | Some id -> Some id
                             )
                             None al)
      )
    in
    let cl = Array.to_list (Array.sub a num_params (len - num_params)) in
    let il = List.fold_left (fun a c -> match c with |None -> a |Some id -> id::a) [] (List.map extract_id cl) in
    il
  | _ -> assert false

let get_current_context () =
    try Pfedit.get_current_goal_context ()
    with e when Logic.catchable_exception e ->
      (Evd.empty, Global.env())

let get_constructors (i:inductive) n =
  let rec iter buf k =
    if k = 0 then buf
    else iter ((mkConstruct (i, k))::buf) (k-1)
  in
  iter [] n

let is_recursive (ind:inductive) (c:constr) =
  let rec count_ind (c:constr) =
    (
    match kind_of_term c with
    | (Rel _ | Var _   | Sort _ | Const _ | Construct _
       | Cast _ | Evar _ | Meta _ | LetIn _ | Case _ | Fix _ | CoFix _ | Proj _) -> 0

    | Ind (i, _) -> if eq_ind i ind then 1 else 0

    | Prod (na,t,c) -> (count_ind t) + (count_ind c)
    | Lambda (na,t,c) -> (count_ind t) + (count_ind c)
    | App (c,al) -> (count_ind c) + (Array.fold_left (fun a c -> (count_ind c) + a) 0 al)
    )
  in
  if (count_ind c) = 1 then false else true

let rec find_index (id:identifier) (l:identifier list) current =
  match l with
  | [] -> -1
  | i::rest -> if id = i then current else (find_index id rest (current+1))


(* get the sublist, first index is 0 *)
let rec sublist l starting_index length =
  let rec iter ind l =
    if ind = 0 then l
    else
      match l with
      | _::rest -> iter (ind-1) rest
      | [] -> raise (Invalid_argument "sublist starting index too big")
  in
  let rec iter2 len l =
    if len = 0 then []
    else
      match l with
      | x::rest -> x::(iter2 (len-1) rest)
      | [] -> raise (Invalid_argument "sublist length too big")
  in
  iter2 length (iter starting_index l)

let rec ids_of_pattern (_,ip) =
  match ip with
  | IntroOrAndPattern oap -> (List.fold_left (fun a pl -> List.append a ((List.fold_left (fun a p-> List.append a (ids_of_pattern p)) [] pl))) [] oap)
  | IntroWildcard -> []
  | IntroRewrite b -> []
  | IntroIdentifier id -> [id]
  | IntroFresh id -> [id]
  | IntroAnonymous -> []
  | IntroInjection _ | IntroForthcoming _ -> []


(* This function returns the list of hypotheses that are related to the
   hypothesis with the id "id". Two hypotheses are related to each other
   if one of them contains a reference to another or they both contain
   references to the same variable.
*)

let find_ids_to_revert hyps id :identifier list=
  let rec occurs_in id c =
    (
    match kind_of_term c with
    | (Rel _ | Sort _ | Const _ | Construct _ | Ind _
       | Cast _ | Evar _ | Meta _ | Case _ | Fix _ | CoFix _ | Proj _) -> false
    | LetIn (_,_,_,c) -> occurs_in id c
    | Var v -> v = id
    | Prod (_,_,c) -> occurs_in id c
    | Lambda (_,_,c) -> occurs_in id c
    | App (c,al) -> (occurs_in id c) || (Array.fold_left (fun a c -> (occurs_in id c) || a) false al)
    )
  in
  let rec ids_occur_in ids c =
    match ids with
    | [] -> false
    | id::rest ->
      if (occurs_in id c) then true
      else (ids_occur_in rest c)
  in
  let rec false_list n =
    if n = 0 then [] else false::(false_list (n-1))
  in
  let rec mark (ids:identifier list) hyps flags =
    match (hyps, flags) with
    | ([],[]) -> (false, [], [])
    | ((n, _, c)::rest, flag::rest_flags) ->
      let (change_flag, new_ids, new_flags) = mark ids rest rest_flags in
      if flag then
        (change_flag, new_ids, true::new_flags)
      else if (List.mem n ids) then
        (true, new_ids, true::new_flags)
      else if (ids_occur_in ids c) then
        (change_flag, n::new_ids, true::new_flags)
      else (change_flag, new_ids, false::new_flags)
    | _ -> assert false
   in
   let rec mark_till_no_change ids hyps flags :bool list=
     let (change_flag, new_ids, new_flags) = mark ids hyps flags in
     if change_flag then
       mark_till_no_change (List.append ids new_ids) hyps new_flags
     else new_flags
   in
   let (_, _, c) = List.find (fun (n,_,_) -> n=id) hyps in
   let (hyp_ids:identifier list) = List.map (fun (n,_,_) -> n) hyps in
   let ids = id::(List.fold_left (fun a n -> if (occurs_in n c) then n::a else a) [] hyp_ids) in
   let (flags:bool list) = mark_till_no_change ids hyps (false_list (List.length hyps)) in
   List.fold_left (fun a (flag,n) -> if flag then n::a else a) [] ((List.combine flags hyp_ids):(bool*identifier) list)

let rec destruct_to_depth id rec_flags fixid to_depth current_dep de_ids ids_to_apply itfs tac_opt gl =
  if current_dep = to_depth then
                     (match tac_opt with
                      | None -> (clear [fixid]) gl
                      | Some tac -> tclTHEN tac (clear [fixid]) gl)
  else
    let rec_intro_flags = List.combine rec_flags itfs in
    let (pl, tacs) =
      List.split
        (
        List.map
          (fun (f, fl) ->
             if f then
               let avoid_ids_ref = ref [] in
               let fresh = List.map
                            (fun f ->
                              let new_id = fresh_id (!avoid_ids_ref) (id_of_string "x") gl in
                              avoid_ids_ref := new_id::(!avoid_ids_ref);
                              (f, new_id))
                            fl in
               let subterms = List.rev (List.fold_left (fun a (f, id) -> if f then (id::a) else a) [] fresh) in
               let fresh_ids = snd (List.split fresh) in
               let com_list = try (List.combine de_ids (sublist fresh_ids 0 (List.length de_ids)))
                                   with e -> print_string "list combine error at destruct_to_depth 1\n";
                                             raise e in
               let replacement_map = List.fold_left
                                          (fun m (old_id,new_id) -> Idmap.add old_id new_id m)
                                          (Idmap.empty) com_list in
               let replaced = List.map
                                   (fun x ->
                                        try
                                            (Idmap.find x replacement_map)
                                        with _ -> x) ids_to_apply in
               let rep_arr = Array.of_list replaced in
               let hypids_ref = ref [] in
               let forward_tacs =
                 List.map
                   (fun st ->
                      let ids_to_app = Array.map (fun x -> mkVar x) (Array.append rep_arr [|st|]) in
                      let term = mkApp ((mkVar fixid), ids_to_app) in
                      let hyp_id = fresh_id (!hypids_ref) (id_of_string "IH") gl in
                      hypids_ref := hyp_id::(!hypids_ref);
                      let tac = Tactics.forward None (Some (Loc.ghost, IntroIdentifier hyp_id)) term in
                      tac
                   )
                   subterms
               in
               let for_tac = tclTHENLIST (List.map Proofview.V82.of_tactic forward_tacs) in
               let tac = destruct_to_depth (List.hd subterms) rec_flags fixid to_depth (current_dep+1)
                         de_ids ids_to_apply itfs (Some for_tac) in
               let pl = List.map (fun id -> (Loc.ghost, IntroIdentifier id)) fresh_ids in
               (pl, tac)
             else ([], clear [fixid])
          )
          rec_intro_flags
        )
    in
    let pat = (Loc.ghost, IntroOrAndPattern pl) in
    tclTHENS
      (Proofview.V82.of_tactic
         (destruct false [ElimOnIdent (Loc.ghost, id)] None (None, Some pat) None))
      tacs gl

(* find out whether the variables that are going to be introed by "destruct" are of
   the same type as the decreasing argument
 *)
let rec get_introtypeflags ind is_dep constype nparams =
  match kind_of_term constype with
  | Prod (_,t,b) ->
      if nparams > 0 then get_introtypeflags ind is_dep b (nparams - 1)
      else
        if is_dep then
          (
          match kind_of_term t with
          | App (c, _) -> (c = mkInd ind)::(get_introtypeflags ind is_dep b (nparams - 1))
          | _ -> false::(get_introtypeflags ind is_dep b (nparams - 1))
          )
        else (t=mkInd ind)::(get_introtypeflags ind is_dep b (nparams - 1))
  | _ -> []


(* this function returns the sublist of l which starts from the first element of l
   and ends at the element which is equal to x *)
let rec cut_list_at x l =
  match l with
  | [] -> []
  | id::rest ->
        if id = x then [id] else id::(cut_list_at x rest)


let di_tac3 id k gl =
  let (evmap, env) = get_current_context () in
  let hyps = pf_hyps gl in
  let ids_to_rev = find_ids_to_revert hyps id in
  let index = (find_index id ids_to_rev 0)+1 in
  let fixid = fresh_id [] (id_of_string "circ") gl in
  let dec_arg_type = pf_type_of gl (mkVar id) in
  let io = get_inductive dec_arg_type in
  match io with
  | None -> print_string "not an inductive product\n"; tclIDTAC gl
  | Some (ind, ctx) ->
    let numcons = Array.length (snd (Global.lookup_inductive ind)).mind_consnames in
    let num_params = (fst (Global.lookup_inductive ind)).mind_nparams in
    let constructors = get_constructors ind numcons in
    let constypes = List.map (Typing.type_of env evmap) constructors in
    let rec_flags = List.map (is_recursive ind) constypes in
    let de_ids = get_des_ids dec_arg_type id num_params in
    let is_dep = is_dependent dec_arg_type in
    let temp_ids = cut_list_at id ids_to_rev in
    let ids_to_apply = sublist temp_ids 0 ((List.length temp_ids) - 1) in
    let itfs = List.map (fun ct -> get_introtypeflags ind is_dep ct num_params) constypes in
    (tclTHEN (revert ids_to_rev) (tclTHEN (fix (Some fixid) index) (tclTHEN (Proofview.V82.of_tactic intros)

     (destruct_to_depth id rec_flags fixid k 0 de_ids ids_to_apply itfs None)

    ))) gl



let rec destruct_on_pattern2 id ids_to_avoid ((loc,pat),(loc2,pat2)) fixid des_ids ids_to_rev gl =
  let idref = ref None in
  let rec iter_and_branch pl patbuf tacbuf replace_ids =
    match pl with
    | [] -> (List.rev patbuf, List.rev tacbuf)
    | ((loc,p),(loc2,p2))::rest ->
           (
           match (p, p2) with
           | (IntroOrAndPattern ioap, _) -> (* if it's another pattern at one level below, we need to find a name for it one level above *)
               let new_id = fresh_id !ids_to_avoid id gl in
                 ids_to_avoid := new_id::!ids_to_avoid;
                 idref := Some (new_id, (loc,p), (loc2,p2));
                 iter_and_branch rest ((loc, IntroIdentifier new_id)::patbuf) tacbuf replace_ids

           | (IntroIdentifier id1, IntroAnonymous) ->
               iter_and_branch rest ((loc,p)::patbuf) tacbuf (id1::replace_ids)

           | (IntroIdentifier id1, IntroIdentifier id2) ->
               let rep_ids = List.rev (id1::replace_ids) in
               let com_list = try (List.combine des_ids rep_ids)
                                   with e -> print_string "list combine error at destruct_on_pattern2 1\n";
                                             raise e in
               let replacement_map = List.fold_left
                                          (fun m (old_id,new_id) -> Idmap.add old_id new_id m)
                                          (Idmap.empty) com_list in
               let replaced = List.map
                                   (fun x ->
                                        try
                                            (Idmap.find x replacement_map)
                                        with _ -> x) ids_to_rev in
               let app_arg = List.map (fun x -> mkVar x) (cut_list_at id1 replaced) in
               let term = mkApp ((mkVar fixid), (Array.of_list app_arg)) in
               let tac = Tactics.forward None (Some (Loc.ghost, IntroIdentifier id2)) term in
                 iter_and_branch rest ((loc,p)::patbuf) (tac::tacbuf) replace_ids

           | _ -> raise (DIPatError "unexpected pattern")
           )
  in
  let rec iter_or_branch pllf =
    match pllf with
    | [] -> ([], [])
    | (pl, pl2)::rest ->
      idref := None;
      let com_list = try List.combine pl pl2
                     with e -> print_string "list combine error at destruct_on_pattern2 2\n"; raise e in
      let (patlist, taclist) = iter_and_branch com_list [] [] [] in
      let (l1, l2) = iter_or_branch rest in
      match (!idref) with
      | Some (nid, patt, patt2) ->
             idref := None;
             let tac = tclTHENLIST (List.map Proofview.V82.of_tactic taclist) in
                ((tclTHEN tac (destruct_on_pattern2 nid ids_to_avoid (patt,patt2) fixid des_ids ids_to_rev))::l1, patlist::l2)
      | None ->
          let tac = tclTHENLIST (List.append (List.map Proofview.V82.of_tactic taclist) [clear [fixid]]) in
          (tac::l1, patlist::l2)
  in
  match (pat, pat2) with
  | (IntroOrAndPattern ipll, IntroOrAndPattern ipll2) ->
      let com_list = try List.combine ipll ipll2
                     with e -> print_string "list combine error at destruct_on_pattern2 3\n"; raise e in
      let (taclist, pl) = iter_or_branch com_list in
      let dp = (loc, IntroOrAndPattern pl) in
      tclTHENS (Proofview.V82.of_tactic (destruct false [ElimOnIdent (Loc.ghost, id)] None (None, Some dp) None)) taclist gl

  | _ -> print_string "wrong pattern"; tclIDTAC gl


let di_tac4 id ip ip2 gl =
  let (evmap, env) = get_current_context () in
  let hyps = pf_hyps gl in
  let ids_to_rev = find_ids_to_revert hyps id in
  let index = (find_index id ids_to_rev 0)+1 in
  let ids_to_avoid = ref (List.append (ids_of_pattern ip) (ids_of_pattern ip2)) in
  let fixid = fresh_id [] (id_of_string "circ") gl in
  let dec_arg_type = pf_type_of gl (mkVar id) in
  let io = get_inductive dec_arg_type in
  match io with
  | None -> print_string "not an inductive product\n"; tclIDTAC gl
  | Some (ind, ctx) ->
    let num_params = (fst (Global.lookup_inductive ind)).mind_nparams in
    let tmp = get_des_ids dec_arg_type id num_params in
    let des_ids = List.append tmp [id] in
    (tclTHEN (revert ids_to_rev) (tclTHEN (fix (Some fixid) index) (tclTHEN (Proofview.V82.of_tactic (intros_using ids_to_rev))

     (destruct_on_pattern2 id ids_to_avoid (ip,ip2) fixid des_ids ids_to_rev)

    ))) gl

let di_tac5 ce ip ip2 gl =
  match kind_of_term ce with
  | Var id -> di_tac4 id ip ip2 gl
  | _ -> tclIDTAC gl

let di_tac6 ce k gl =
  match kind_of_term ce with
  | Var id -> di_tac3 id k gl
  | _ -> tclIDTAC gl

(* grammar declarations which hook the tactic to the proof engine *)
TACTIC EXTEND di
| ["di" constr(ce) natural(k)] -> [Proofview.V82.tactic (di_tac6 ce k)]
| ["di" constr(ce) "as" simple_intropattern(ip) "hyps" simple_intropattern(ip2)] -> [Proofview.V82.tactic (di_tac5 ce ip ip2)]
END
