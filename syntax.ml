(* Symbols : ⊤ ⊥ ∧ ∨ ¬ = < ⩽ > ⩾ ∀ ∃ *)

open Printf

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
  | Impl
;;

type quantif =
  | Exists
  | Forall

type formula =
  | Const of bool_const
  | Variable of string
  | Number of float
  | ComparF of formula * compar_op * formula
  | BoolF of formula * bool_op * formula
  | NotF of formula
  | Quantif of quantif * formula * formula
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
  | Impl -> "->"
;;

let rep_not = "¬";;

let rep_number = string_of_float;;

let rec rep_formula = function
  | Const c -> rep_const c
  | ComparF(f, op, g) -> sprintf
  "(%s %s %s)" (rep_formula f) (rep_comp_op op) (rep_formula g)
  | BoolF(f, op, g) -> sprintf
  "(%s %s %s)" (rep_formula f) (rep_bool_op op) (rep_formula g)
  | NotF f -> sprintf
  "%s%s" rep_not (rep_formula f)
  | Quantif(q, Variable v, f) -> sprintf
  "(%s %s %s)" (rep_quantif q) v (rep_formula f)
  | Variable v -> v
  | Number n -> rep_number n
  | _ -> failwith("Erreur dans la représentation de la formule")
;;

let top = Const(Top);;
let bottom = Const(Bottom);;
let forall v f = Quantif(Forall, v, f);;
let exists v f = Quantif(Exists, v, f);;
let equal f g = ComparF(f,Equal,g);;
let lt f g = ComparF(f,Lt, g);;
let notf f = NotF(f);;
let conj f g = BoolF(f,Conj,g);;
let disj f g = BoolF(f,Disj,g);;
let implies f g = BoolF(f,Impl, g);;
let var x = Variable(x);;

let rec print_formula f = print_string (rep_formula f ^ "\n");;

let dual f =
  let dual_op = function
    | Conj -> Disj
    | Disj -> Conj
    | x -> x
  in
  let rec aux f = match f with
    | Variable _ | Const _ | Number _ -> f
    | Quantif(Forall, v, f') -> Quantif(Forall,v, aux f')
    | Quantif(Exists, v, f') -> Quantif(Exists, v, aux f')
    | NotF(f') -> NotF(aux f')
    | ComparF(f',Equal,g') -> ComparF(aux f', Equal, aux g')
    | ComparF(f',Lt, g') -> ComparF(aux f', Lt, aux g')
    | BoolF(f', op, g') -> BoolF(f', dual_op op, g') 
  in aux f;;

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
  let rec univ_to_exist f = match f with
    | Quantif(Forall, v, f') -> notf (exists v (notf (univ_to_exist f')))
    | _ -> f
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

(* Step 2.1 Put negations inside the formula *)
let rec neg_inside f = match f with
  | NotF(Quantif(Exists, v, f')) -> Quantif(Forall, v, neg_inside (NotF(f')))
  | NotF(Quantif(Forall, v, f')) -> Quantif(Exists, v, neg_inside (NotF(f')))
  | NotF(NotF(f')) -> neg_inside f'
  | Quantif(q, v, f') -> Quantif(q, v, neg_inside f')
  | _ -> f
;;

let example_neg_inside =
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
print_formula (neg_inside example_neg_exist);;

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
print_formula (neg_inside example_neg_exist_2);;