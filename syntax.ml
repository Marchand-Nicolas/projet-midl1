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

  type formula =
    | Const of bool_const
    | Variable of string
    | Number of float
    | ComparF of formula * compar_op * formula
    | BoolF of formula * bool_op * formula
    | NotF of formula
    | QuantifF of quantif * formula * formula
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
let var x = Variable(x);;

end;;

open Printf
open SyntaxTree

let rec rep_formula = function
  | Const c -> rep_const c
  | ComparF(f, op, g) -> sprintf
  "(%s %s %s)" (rep_formula f) (rep_comp_op op) (rep_formula g)
  | BoolF(f, op, g) -> sprintf
  "(%s %s %s)" (rep_formula f) (rep_bool_op op) (rep_formula g)
  | NotF f -> sprintf
  "%s%s" rep_not (rep_formula f)
  | QuantifF(q, Variable v, f) -> sprintf
  "(%s%s.%s)" (rep_quantif q) v (rep_formula f)
  | Variable v -> v
  | Number n -> rep_number n
  | _ -> failwith("Erreur dans la représentation de la formule")
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
    | Variable _ | Const _ | Number _ -> f
    | QuantifF(Forall, v, f') -> QuantifF(Forall,v, aux f')
    | QuantifF(Exists, v, f') -> QuantifF(Exists, v, aux f')
    | NotF(f') -> NotF(aux f')
    | ComparF(f',Equal,g') -> ComparF(aux f', Equal, aux g')
    | ComparF(f',Lt, g') -> ComparF(aux f', Lt, aux g')
    | BoolF(f', op, g') -> BoolF(f', dual_op op, g') 
  in aux f;;

  let rec univ_to_exist = function
    | QuantifF(Forall, v, f') -> notf (exists v (notf (univ_to_exist f')))
    | f -> f
  ;;


(* 
signature : 
  is_prenex : formula -> bool

Cette fonction renvoie vrai si la formule passée en paramètres est sous forme prénexe, faux sinon.
*)

let is_prenex f =
  let rec aux f met_smth = match (f, met_smth) with
    | (QuantifF(q, Variable v, f'),false) -> aux f' false
    | (QuantifF(q, Variable v, f'), true) -> false
    | (ComparF(f',_,g'), _ ) | (BoolF(f', _, g'),_) ->  aux f' true && aux g' true
    | (NotF(f'),_) -> aux f' true
    | (Variable(_),_) | (Number(_), _) | (Const(_),_) -> true
    | _, _ -> false
  in aux f false
  ;;


  let example_1 = 
    forall (var "x") (
      exists (var "y") (
        lt (var "x") (var "y")
      )
    );;
  
  let example_2 = 
    forall (var "x") (
      forall (var "y") (
        forall (var "z") (
          exists (var "u") (
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
  forall (var "x") (
    exists (var "y") (
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

let example_neg_nf =
  notf (exists (var "x") (
    lt (var "x") (var "y")
  ))
;;

let example_neg_exist =
  notf (exists (var "x") (
    lt (var "x") (var "y")
  ))
;;

print_string "Example neg exist: ";;
print_formula example_neg_exist;;

print_string "Example neg inside: ";;
print_formula (neg_nf example_neg_exist);;

let example_neg_exist_2 =
  notf (exists (var "x") (
    notf (exists (var "y") (
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