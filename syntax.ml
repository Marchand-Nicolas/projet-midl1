(* Symbols : ⊤ ⊥ ∧ ∨ ¬ = < ⩽ > ⩾ ∀ ∃ *)

module SyntaxTree = struct

  type compar_op =
    | Equal
    | Lt
  ;;

  type bool_const =
    | Top     (*"true"*)
    | Bottom (*"false"*)
  ;; 

  type bool_op =
    | Conj 
    | Disj
  ;;

  type quantif =
    | Exists
    | Forall
  ;;

  type term = 
    | Var of string
    | Val of float

  type formula =
    | Const of bool_const
    | ComparF of term * compar_op * term
    | BoolF of formula * bool_op * formula
    | NotF of formula
    | QuantifF of quantif * string * formula
  ;;

  let rep_quantif = function
    | Exists -> "∃"
    | Forall -> "∀"
  ;;

  let rep_const = function
    | Top -> "Τ"
    | Bottom -> "⊥"
  ;;

  let rep_comp_op = function
    | Equal -> "="
    | Lt -> "<"

  let rep_bool_op = function
    | Conj -> "∧"
    | Disj -> "∨"
  ;;

  let rep_not = "¬";;

  let rep_number = string_of_float;;

  let top = Const(Top);;
let bottom = Const(Bottom);;
let forall v f = QuantifF(Forall, v, f);;
let exists v f = QuantifF(Exists, v, f);;
let equal f g = ComparF(f,Equal,g);;
let lt f g = ComparF(f,Lt, g);;
let notf f = NotF(f);;
let conj f g = BoolF(f,Conj,g);;
let disj f g = BoolF(f,Disj,g);;
let implies f g = BoolF(notf f,Disj, g);;
let var x = Var(x);;

let _val x = Val(x);;

end;;

open Printf
open SyntaxTree

let rep_term = function
  | Var x -> x
  | Val x -> string_of_float x

let rec rep_formula = function
  | Const c -> rep_const c
  | ComparF(f, op, g) -> sprintf
  "(%s %s %s)" (rep_term f) (rep_comp_op op) (rep_term g)
  | BoolF(f, op, g) -> sprintf
  "(%s %s %s)" (rep_formula f) (rep_bool_op op) (rep_formula g)
  | NotF f -> sprintf
  "%s%s" rep_not (rep_formula f)
  | QuantifF(q, v, f) -> sprintf
    "(%s%s.%s)" (rep_quantif q) v (rep_formula f)
;;

let rec print_formula f = print_string (rep_formula f ^ "\n");;

(*
signature :
  dual : formula -> formula

Cette fonction renvoie la forme duale de la formule passée en paramètres.
*)
let dual f =
  let dual_op = function
    | Conj -> Disj
    | Disj -> Conj
  in
  let rec aux = function
    | QuantifF(Forall, v, f') -> QuantifF(Forall,v, aux f')
    | QuantifF(Exists, v, f') -> QuantifF(Exists, v, aux f')
    | NotF(f') -> NotF(aux f')
    | BoolF(f', op, g') -> BoolF(f', dual_op op, g') 
    | _ -> f
  in aux f;;

(* 
signature : 
  is_prenex : formula -> bool

Cette fonction renvoie vrai si la formule passée en paramètres est sous forme prénexe, faux sinon.
*)

let is_prenex f =
  let rec aux f met_smth = match (f, met_smth) with
    | (QuantifF(q, _, f'),false) -> aux f' false
    | (QuantifF(q, _, f'), true) -> false
    | (BoolF(f', _, g'),_) ->  aux f' true && aux g' true
    | (NotF(f'),_) -> aux f' true
    | (Const _, _) | (ComparF _, _) -> true
  in aux f false
  ;;


  let example_1 = 
    forall "x" (
      exists "y" (
        lt (var "x") (var "y")
      )
    );;
  
  let example_2 = 
    forall "x" (
      forall "y" (
        forall "z" (
          exists "u" (
            implies (
              conj (
                lt (var "x") (var "y")
              )
              (
                lt (var "x") (var "z")
              )
            )
            (
              conj(
                lt (var "y") (var "u")
              )
              (
                lt (var "z") (var "u")
              )
            )
          )
        ) 
      )
    )
  ;;
  
  print_string "Example 1: ";;
  print_formula example_1;;
  
  print_string "Example 2: ";;
  print_formula example_2;;


  (* Step 1: We assume all formulas are in prenex form *)
  (* Step 2: Convert universal quantifier to existential quantifier while preserving the formula meaning *)
  let rec univ_to_exist = function 
    | QuantifF(Forall, v, f') -> notf (exists v (notf (univ_to_exist f')))
    | f -> f
  ;;

let example_univ =
  forall "x" (
    exists "y" (
      lt (var "x") (var "y")
    )
  )
;;

print_string "Example univ: ";;
print_formula example_univ;;

print_string "Example univ to exist: ";;
print_formula (univ_to_exist example_univ);;

(* Step 2.1 Put negations inside the formula (negation normal form) *)
let rec neg_nf = function
  | NotF(QuantifF(Exists, v, f')) -> QuantifF(Forall, v, neg_nf (NotF(f')))
  | NotF(QuantifF(Forall, v, f')) -> QuantifF(Exists, v, neg_nf (NotF(f')))
  | NotF(NotF(f')) -> neg_nf f'
  | QuantifF(q, v, f') -> QuantifF(q, v, neg_nf f')
  | NotF(BoolF(g, Conj, h)) -> BoolF(neg_nf (NotF g), Disj, neg_nf (NotF h)) (* Loi de De Morgan *)
  | NotF(BoolF(g, Disj, h)) -> BoolF(neg_nf (NotF g), Conj, neg_nf (NotF h)) (* Loi de De Morgan *)
  | BoolF(g, op, h) -> BoolF(neg_nf g, op, neg_nf h)
  | f -> f
;;

let example_neg_exist =
  notf (exists "x" (
    lt (var "x") (var "y")
  ))
;;

print_string "Example neg exist: ";;
print_formula example_neg_exist;;

print_string "Example neg inside: ";;
print_formula (neg_nf example_neg_exist);;

let example_neg_exist_2 =
  notf (exists "x" (
    notf (exists "y" (
      lt (var "x") (var "y")
    ))
  ))
;;

print_string "Example neg exist 2: ";;
print_formula example_neg_exist_2;;

print_string "Example neg inside 2: ";;
print_formula (neg_nf example_neg_exist_2);;


(* Step 2.2: Eliminate negations in front of relations *)
let rec neg_elim = function
  | NotF(ComparF(g, Equal, h)) -> disj (lt g h) (lt h g)
  | NotF(ComparF(g, Lt, h)) -> disj (lt h g) (equal g h)
  | QuantifF(q, v, f') -> QuantifF(q, v, neg_elim f')
  | BoolF(f, op, g) -> BoolF(neg_elim f, op, neg_elim g)
  | f -> f
;;

let example_relation_formula =
  notf (ComparF(var "x", Equal, var "y"))
;;

print_string "Example relation formula: ";;
print_formula example_relation_formula;;

print_string "Example neg elim: ";;
print_formula (neg_elim example_relation_formula);;

let example_relation_formula_2 =
  BoolF(NotF(ComparF(var "x", Equal, var "y")), Conj, NotF(ComparF(var "x", Lt, var "y")))
;;

print_string "Example relation formula 2: ";;
print_formula example_relation_formula_2;;

print_string "Example neg elim 2: ";;
print_formula (neg_elim example_relation_formula_2);;


(* Step 2.3: Transform into disjunctive normal form *)
let rec disj_nf = function
  | QuantifF (q, v, f') -> QuantifF (q, v, disj_nf f')
  | BoolF(g, op, h) ->
      let g_nf = disj_nf g in
      let h_nf = disj_nf h in
        (
          match (g_nf, op, h_nf) with
          | (BoolF(g1, Disj, g2), Conj, _) -> (* Cas 1 : (A or B) and C  ~> (A and C) or (B and C) *) 
            disj_nf (BoolF(BoolF(g1, Conj, h_nf), Disj, BoolF(g2, Conj, h_nf)))
          
          | (_, Conj, BoolF(h1, Disj, h2)) -> (* Cas 2 : A and (B or C) ~> (A and B) or (A and C) *)
            disj_nf (BoolF(BoolF(g_nf, Conj, h1), Disj, BoolF(g_nf, Conj, h2)))

          | _ -> BoolF(g_nf, op, h_nf)
        )
      
  | f -> f  
;;

let example_distributive_law =
  BoolF(ComparF(var "x", Equal, var "y"), Conj, BoolF(ComparF(var "x", Lt, var "z"), Disj, ComparF(var "y", Lt, var "z")))
;;

print_string "Example distributive law: ";;
print_formula example_distributive_law;;

print_string "Example disj_nf: ";;
print_formula (disj_nf example_distributive_law);;

let example_conj_nf =
  BoolF(
    BoolF(ComparF(var "x", Equal, var "y"), Disj, ComparF(var "x", Lt, var "y")),
      Conj,
    BoolF(ComparF(var "y", Equal, var "z"), Disj, ComparF(var "y", Lt, var "z"))
  )
;;

print_string "Example conjunctive normal form: ";;
print_formula example_conj_nf;;

print_string "Example disj_nf from conjunctive normal form: ";;
print_formula (disj_nf example_conj_nf);;

(* Step 2.4 : Pushing exists within the disjunction *)
let rec push_exists = function
  | QuantifF(Exists, x, BoolF(g, Disj, h)) -> (* Cas où la propagation s'effectue *) 
      let new_g = push_exists (exists x g) in
      let new_h = push_exists (exists x h) in
      disj new_g new_h

  | QuantifF(Exists, x, f') -> (*On regarde si après avoir poussé un exists on a pas une disjonction qui apparait*)
      let inside = push_exists f' in
      (
        match inside with
        | BoolF(_, Disj, _) -> push_exists (QuantifF(Exists, x, inside))
        | _ -> QuantifF(Exists, x, inside)
      )
  
  | BoolF(g, op, h) -> BoolF(push_exists g, op, push_exists h)
  | f -> f
;;

let example_exist_outside_disj =
  exists "x" (
    (disj_nf example_conj_nf)
  )
  ;;

print_string "Example exists outside disj: ";;
print_formula example_exist_outside_disj;;

print_string "Example push_exists: ";;
print_formula (push_exists example_exist_outside_disj);;

(* Step 3: Remove variable *)

(* 
signature : 
  check_var : string -> formula -> int

Cette fonction vérifie la présence de la variable v (supposément introduite dans un quantificateur) dans une comparaison
Cette fonction renvoie:
  2 si la comparaison est v < v
  1 si v est présent d'une autre manière dans la comparaison
  0 sinon (v absent)
*)

let check_var v = function
  | ComparF(x, Lt, y) -> if (x = var v || y = var v) then
      if (x = y) then 2 else 1
      else 0
  | ComparF(x, Equal, y) -> if (x = var v || y = var v) then 1 else 0
  | f -> 0
;;

print_string (sprintf "Example check_var (x < x): %d" (check_var "x" (lt (var "x") (var "x"))) ^ "\n");;
print_string (sprintf "Example check_var (x < y): %d" (check_var "x" (lt (var "x") (var "y"))) ^ "\n");;
print_string (sprintf "Example check_var (x = y): %d" (check_var "x" (equal (var "x") (var "y"))) ^ "\n");;
print_string (sprintf "Example check_var (without x): %d" (check_var "x" (lt (var "y") (var "z"))) ^ "\n");;

(* 
signature : 
  check_conj : string -> formula -> int

Cette fonction vérifie la présence de la variable v (supposément introduite dans un quantificateur) dans une conjonction
Cette fonction renvoie:
  2 si la conjonction contient v < v
  1 si v est présent d'une autre manière dans la conjonction
  0 sinon (v absent)
*)

let rec check_conj v = function
  | BoolF(f, Conj, g) -> 
    let fres = check_conj v f in
    let gres = check_conj v g in
    if (fres = 2 || gres = 2) then 2
    else if (fres = 1 || gres = 1) then 1 
    else 0
  | f -> check_var v f  (* Cas de base : vérifier l'atome *)
;;

print_string (sprintf "Exemple check_conj (x < x) : %d" (check_conj "x" (conj (lt (var "x") (var "x")) (lt (var "x") (var "y")))) ^ "\n");;
print_string (sprintf "Exemple check_conj (x present) : %d" (check_conj "x" (conj (equal (var "x") (var "x")) (lt (var "x") (var "y")))) ^ "\n");;
print_string (sprintf "Exemple check_conj (x absent) : %d" (check_conj "x" (conj (equal (var "y") (var "y")) (lt (var "z") (var "y")))) ^ "\n");;

(* Steps 3.3+: non triviaux. On convertit la disjonction tableau, pour réaliser les étapes suivantes plus facilement *)

(* Structure stockant les disjonctions classées par type de contrainte sur la variable quantifiée *)
type step3_result = {
  inf: formula list;  (* Cas a < x *)
  sup: formula list;  (* Cas x < b *)
  eq: formula list;    (* Cas x = c *)
  independent: formula list;   (* Conditions ne dépendant pas de x *)
}

let empty_step3_result = { inf = []; sup = []; eq = []; independent = [] }

(* Détermine la catégorie d'une contrainte sur x (x < b, a < x, ou x = c) *)
let rec classify_x_constraint target_var formula =
  match formula with
  | ComparF(Var x, Lt, _) when x = target_var -> `Sup   (* x < b *)
  | ComparF(_, Lt, Var x) when x = target_var -> `Inf   (* a < x *)
  | ComparF(Var x, Equal, _) when x = target_var -> `Eq (* x = c *)
  | ComparF(_, Equal, Var x) when x = target_var -> `Eq (* c = x *)
  | BoolF(left, Conj, _) -> classify_x_constraint target_var left (* On descend pour trouver la variable *)
  | _ -> `Other

(* Transforme une structure de conjonctions imbriquées en une liste plate *)
let rec flatten_conjunctions = function
  | BoolF(left, Conj, right) ->
      (flatten_conjunctions left) @ (flatten_conjunctions right)
  | formula -> [formula]

(* Transforme une structure de disjonctions imbriquées en une liste plate *)
let rec flatten_disjunctions = function
  | BoolF(left, Disj, right) ->
      (flatten_disjunctions left) @ (flatten_disjunctions right)
  | formula -> [formula]

(*
  convert_single_conj : string -> formula -> step3_result
  
  Prend une variable cible et une conjonction de relations,
  et regroupe les termes selon la procédure A.2.3 :
  - inf : termes de la forme v < x (bornes inférieures)
  - sup : termes de la forme x < u (bornes supérieures)  
  - eq : termes de la forme w = x (égalités)
  - independent : termes χ où x n'apparaît pas
*)
let convert_single_conj target_var body =
  let conjunct_list = flatten_conjunctions body in
  List.fold_left (fun acc current_atom ->
    (* On vérifie si l'atome contient la variable cible *)
    (* Note: il faut gérer le cas où les deux côtés sont des variables *)
    let contains_var = match current_atom with
      | ComparF(Var x, _, Var y) -> x = target_var || y = target_var
      | ComparF(Var x, _, _) -> x = target_var
      | ComparF(_, _, Var x) -> x = target_var
      | _ -> false
    in
    if not contains_var then
      (* L'atome ne dépend pas de x, va dans 'independent' *)
      { acc with independent = current_atom :: acc.independent }
    else
      (* L'atome dépend de x, on le classe selon sa forme *)
      match classify_x_constraint target_var current_atom with
      | `Inf -> { acc with inf = current_atom :: acc.inf }
      | `Sup -> { acc with sup = current_atom :: acc.sup }
      | `Eq -> { acc with eq = current_atom :: acc.eq }
      | `Other -> { acc with independent = current_atom :: acc.independent }
  ) empty_step3_result conjunct_list

(*
  convert_conj_to_list : formula -> step3_result list
  
  Prend une formule qui est une disjonction de ∃x. v_j (résultat de push_exists),
  et retourne une liste de step3_result, un pour chaque disjonct.
*)
let convert_conj_to_list formula =
  let disjuncts = flatten_disjunctions formula in
  List.map (fun disjunct ->
    match disjunct with
    | QuantifF(Exists, target_var, body) -> convert_single_conj target_var body
    | _ -> { empty_step3_result with independent = [disjunct] }
  ) disjuncts

(* Debug functions *)
let print_formula_list_line f = print_string (rep_formula f ^ "," ^ "\n");;
let print_formula_list l = print_string "["; List.iter (print_formula_list_line) l; print_string "]";;

let print_step3_result res =
  print_string "  {\n";
  print_string "    inf: "; print_formula_list (List.rev res.inf); print_string "\n";
  print_string "    sup: "; print_formula_list (List.rev res.sup); print_string "\n";
  print_string "    eq:  "; print_formula_list (List.rev res.eq); print_string "\n";
  print_string "    independent:  "; print_formula_list (List.rev res.independent); print_string "\n";
  print_string "  }";;

let print_step3_result_list results =
  print_string "[\n";
  List.iter (fun res -> print_step3_result res; print_string ",\n") results;
  print_string "]\n";;



(* Exemple : résultat de push_exists (disjonction de ∃x. v_j) *)
print_string "Exemple convert_conj_to_list sur push_exists result :\n";;
print_string "Input : ";;
print_formula (push_exists example_exist_outside_disj);;
print_string "\nOutput : ";;
print_step3_result_list (convert_conj_to_list (push_exists example_exist_outside_disj));;

(* Step 3.4, 3.5, 3.6 : Élimination de la variable quantifiée *)

(* Helper: construit une conjonction à partir d'une liste de formules *)
let rec make_conj_from_list = function
  | [] -> top
  | [a] -> a
  | a :: l' -> BoolF(a, Conj, (make_conj_from_list l'))
;;

(* Tests make_conj_from_list *)
print_string "Example make_conj_from_list (empty): ";;
print_formula (make_conj_from_list []);;
print_string "Example make_conj_from_list (one element): ";;
print_formula (make_conj_from_list [ComparF(var "x", Equal, var "y")]);;
print_string "Example make_conj_from_list (multiple): ";;
print_formula (make_conj_from_list [ComparF(var "x", Equal, var "y"); ComparF(var "x", Lt, var "z"); ComparF(var "y", Lt, var "z")]);;

(* Helper: extrait le terme "de l'autre côté" d'une comparaison avec x *)
let get_other_term target_var = function
  | ComparF(Var x, _, other) when x = target_var -> other
  | ComparF(other, _, Var x) when x = target_var -> other
  | _ -> failwith "Formula doesn't contain target variable"

(*
  Step 3.4 : Si (w_k = x) est présent
  
  On choisit w_0 parmi les w_k, et on substitue
*)
let step3_4 target_var groups =
  match groups.eq with
  | [] -> None  (* Pas d'égalités, étape 3.4 ne s'applique pas *)
  | first_eq :: _ ->
    let w0 = get_other_term target_var first_eq in  (* Choix de w_0 *)
    (* Construire w_0 < u_i pour toutes les bornes supérieures *)
    let new_sup = List.map (fun f ->
      let u = get_other_term target_var f in
      lt w0 u
    ) groups.sup in
    (* Construire v_j < w_0 pour toutes les bornes inférieures *)
    let new_inf = List.map (fun f ->
      let v = get_other_term target_var f in
      lt v w0
    ) groups.inf in
    (* Construire w_k = w_0 pour toutes les égalités *)
    let new_eq = List.map (fun f ->
      let w = get_other_term target_var f in
      equal w w0
    ) groups.eq in
    (* Combiner tout *)
    Some (make_conj_from_list (new_sup @ new_inf @ new_eq @ groups.independent))

(*
  Step 3.5 : Si (x < u_i) ET (v_j < x) sont présents (mais pas d'égalité)
*)
let step3_5 target_var groups =
  if groups.eq <> [] then None  (* Étape 3.4 s'applique à la place *)
  else if groups.sup = [] || groups.inf = [] then None  (* Étape 3.5 ne s'applique pas *)
  else
    (* Construire v_j < u_i pour toutes les paires (produit cartésien) *)
    let pairs = List.flatten (List.map (fun inf_f ->
      let v = get_other_term target_var inf_f in
      List.map (fun sup_f ->
        let u = get_other_term target_var sup_f in
        lt v u
      ) groups.sup
    ) groups.inf) in
    Some (make_conj_from_list (pairs @ groups.independent))

(*
  Step 3.6 : Si uniquement (x < u_i) OU uniquement (v_j < x) est présent
*)
let step3_6 groups =
  if groups.eq <> [] then None  (* Étape 3.4 s'applique *)
  else if groups.sup <> [] && groups.inf <> [] then None  (* Étape 3.5 s'applique *)
  else
    (* Seules des contraintes unilatérales ou aucune contrainte sur x *)
    match groups.independent with
    | [] -> Some top
    | _ -> Some (make_conj_from_list groups.independent)

(*
  eliminate_exists_from_result : string -> step3_result -> formula
  
  Applique l'étape appropriée (3.4, 3.5, ou 3.6) pour éliminer x
*)
let eliminate_exists_from_result target_var groups =
  match step3_4 target_var groups with
  | Some f -> f
  | None -> (
    match step3_5 target_var groups with
    | Some f -> f
    | None -> (
      match step3_6 groups with
      | Some f -> f
      | None -> failwith "No elimination rule applies"
    )
  )
  
(*
  eliminate_exists : formula -> formula
  
  Élimine un quantificateur existentiel d'une formule en forme normale disjonctive.
  Applique les étapes 1 à 6 de l'algorithme de suppression de variable.
*)
let eliminate_exists formula =
  let disjuncts = flatten_disjunctions formula in
  let eliminated = List.map (fun disjunct ->
    match disjunct with
    | QuantifF(Exists, target_var, body) ->
      let result = check_conj target_var body in
      if result = 2 then bottom           (* Étape 2: x < x présent *)
      else if result = 0 then body        (* Étape 1: x absent de fv *)
      else
        let groups = convert_single_conj target_var body in  (* Étape 3 *)
        eliminate_exists_from_result target_var groups       (* Étapes 4, 5, 6 *)
    | f -> f  (* Pas de quantificateur, on garde tel quel *)
  ) disjuncts in
  match eliminated with
  | [] -> bottom
  | [f] -> f
  | f :: rest -> List.fold_left disj f rest

(*
debug : formula -> formula

Affiche f avant de la renvoyer, non-changée.
*)
let debug f =
  print_string "[DEBUG] ";
  print_formula f;
  f
;;

(*
preprocess : formula -> formula

Effectue le prétraitement sur f 
*)
let preprocess f =
  f 
  |> neg_nf
  |> neg_elim
  |> disj_nf
  |> push_exists
;;

(*
  preprocess_debug : formula -> formula

  Effectue le même processus que preprocess en appelant debug à chaque étape.
*)
let preprocess_debug f =
  f
  |> neg_nf
  |> debug
  |> neg_elim
  |> debug
  |> disj_nf
  |> debug
  |> push_exists
  |> debug
(*
formula -> formula

Renvoie la formule simplifiée au maximum 
par les règles de base sur les opérations booléennes
*)
let rec simplify f = match f with
  | BoolF(g, op, h) -> 
      let gs = simplify g in
      let hs = simplify h in
      begin 
        match (gs, op, hs) with
        (* Forme "A ∧ B" *)
        | (Const Top, Conj, x) -> x
        | (x, Conj, Const Top) -> x
        | (Const Bottom, Conj, _) -> bottom
        | (_, Conj, Const Bottom) -> bottom
        (* Forme "A V B" *)
        | (Const Bottom, Disj, x) | (x, Disj, Const Bottom) -> x
        | (Const Top, Disj, _) -> top
        | (_, Disj, Const Top) -> top
        | _ -> BoolF(gs, op, hs)
      end
  | NotF(Const Top) -> bottom
  | NotF(Const Bottom) -> top
  | NotF(f) -> NotF(simplify f)
  | _ -> f;;

(* 
eliminate_quantifiers : formula -> formula

Renvoie la formule finale, sans simplifications
*)
let rec eliminate_quantifiers f = match f with
  | QuantifF(Forall, v, g) ->
    eliminate_quantifiers (notf (exists v (notf g)))
  
  | QuantifF(Exists, v, g) ->
    (* Approche bottom-up : on nettoie de l'intérieur *)
    let clean_g = eliminate_quantifiers g in
    let to_process = exists v clean_g in
    let prepared = preprocess to_process in    
    simplify (eliminate_exists prepared)
  | BoolF(g,op, h) -> BoolF(eliminate_quantifiers g, op, eliminate_quantifiers h)
  | NotF(g) -> NotF(eliminate_quantifiers g)
  | _ -> f;;

(* 
solve : formula -> formula

Processus final d'élimination de quantificateurs
*)
let solve f =
  f
  |> eliminate_quantifiers
  |> simplify

(* === Tests === *)

(* Test Step 3.4 : cas avec égalité *)
let test_step3_4 =
  exists "x" (
    conj (equal (var "x") (var "w"))
      (conj (lt (var "x") (var "u"))
        (lt (var "v") (var "x")))
  );;

print_string "\n=== Test Step 3.4 (avec égalité) ===\n";;
print_string "Input : ";;
print_formula test_step3_4;;
print_string "Output : ";;
print_formula (eliminate_exists test_step3_4);;

(* Test Step 3.5 : cas sans égalité mais avec bornes inf et sup *)
let test_step3_5 =
  exists "x" (
    conj (lt (var "x") (var "u1"))
      (conj (lt (var "x") (var "u2"))
        (conj (lt (var "v1") (var "x"))
          (lt (var "v2") (var "x"))))
  );;

print_string "\n=== Test Step 3.5 (bornes inf et sup) ===\n";;
print_string "Input : ";;
print_formula test_step3_5;;
print_string "Output : ";;
print_formula (eliminate_exists test_step3_5);;

(* Test Step 3.6 : cas avec uniquement des bornes supérieures *)
let test_step3_6_sup =
  exists "x" (
    conj (lt (var "x") (var "u1"))
      (conj (lt (var "x") (var "u2"))
        (lt (var "a") (var "b")))  (* condition indépendante *)
  );;

print_string "\n=== Test Step 3.6 (uniquement bornes sup) ===\n";;
print_string "Input : ";;
print_formula test_step3_6_sup;;
print_string "Output : ";;
print_formula (eliminate_exists test_step3_6_sup);;

(* Test Step 3.6 : cas avec uniquement des bornes inférieures *)
let test_step3_6_inf =
  exists "x" (
    conj (lt (var "v1") (var "x"))
      (lt (var "v2") (var "x"))
  );;

print_string "\n=== Test Step 3.6 (uniquement bornes inf) ===\n";;
print_string "Input : ";;
print_formula test_step3_6_inf;;
print_string "Output : ";;
print_formula (eliminate_exists test_step3_6_inf);;

(* Test complet sur l'exemple avec disjonction *)
print_string "\n=== Test complet sur exemple push_exists ===\n";;
print_string "Input (après push_exists) : ";;
print_formula (push_exists example_exist_outside_disj);;
print_string "Output (après eliminate_exists): ";;
print_formula (eliminate_exists (push_exists example_exist_outside_disj));;

let final_test f name =
  printf "Nom de la formule : \"%s\"\n" name;
  print_string "Input initial : ";
  print_formula f;
  print_string "Output final : ";
  print_formula (solve f)
;;

print_string "\n=== TEST FINAL : Exemple de Prise de décision ===\n";;
final_test example_1 "Exemple 1"