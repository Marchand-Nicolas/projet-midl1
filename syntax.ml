(* Symbols : ⊤ ⊥ ∧ ∨ ¬ = < ⩽ > ⩾ ∀ ∃ *)

module Rational = struct
  type t = { num : int; denom : int }

  let rec pgcd a b =
    if b = 0 then abs a else pgcd b (a mod b)
  
  let make n d =
    if d = 0 then failwith "division par zero"
    else
      let g = pgcd n d in
      let signed_n = if d < 0 then -n else n in
      let signed_d = abs d in
      { num = signed_n / g; denom = signed_d / g }

  let zero = { num = 0; denom = 1 }
  let one = { num = 1; denom = 1 }
  let minus_one = { num = -1; denom = 1 }

  let add f1 f2 =
    make (f1.num * f2.denom + f2.num * f1.denom) (f1.denom * f2.denom)

  let sub f1 f2 =
    make (f1.num * f2.denom - f2.num * f1.denom) (f1.denom * f2.denom)

  let mul f1 f2 =
    make (f1.num * f2.num) (f1.denom * f2.denom)

  (* Division : a/b / c/d = a/b * d/c *)
  let div f1 f2 =
    if f2.num = 0 then failwith "Division par fraction nulle"
    else make (f1.num * f2.denom) (f1.denom * f2.num)
    
  let neg f = { num = -f.num; denom = f.denom }

  let equal f1 f2 = (f1.num = f2.num) && (f1.denom = f2.denom)
  
  let lt f1 f2 = 
    (f1.num * f2.denom) < (f2.num * f1.denom)

  let to_string f =
    if f.denom = 1 then string_of_int f.num
    else Printf.sprintf "(%d/%d)" f.num f.denom
    
  let of_int k = make k 1
end

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

  (*
  bien que l'on travaille sur des entiers, 
  il est plus simple de mettre des flottants 
  pour diviser lors de l'isolation de variables
  *)
  type term = 
    | Var of string
    | Val of Rational.t
    | Add of term * term
    | Sub of term * term
    | Mult of Rational.t * term

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
  let var x = Var x;;
  let val_ k = Val (Rational.of_int k);;
  let frac p q = Val (Rational.make p q);;
  let add t1 t2 = Add(t1, t2);;
  let sub t1 t2 = Sub(t1, t2);;
  let mul k t = Mult(Rational.of_int k, t);;
  let mul_frac p q t = Mult(Rational.make p q, t);;

let add t1 t2 = Add(t1, t2);;
let sub t1 t2 = Sub(t1, t2);

end;;

open Printf
open SyntaxTree
(*
rep_term : term -> string
renvoie la représentation de l'expression algébrique en chaîne de caractères
*)
let rec rep_term t = match t with
  | Var x -> x
  | Val v -> Rational.to_string v

  | Add(t1, t2) -> rep_term t1 ^ " + " ^ rep_term t2
  
  | Sub(t1, t2) -> 
      let right = match t2 with
        | Add _ | Sub _ -> "(" ^ rep_term t2 ^ ")"
        | _ -> rep_term t2
      in
      rep_term t1 ^ " - " ^ right

  | Mult(k, t) ->
      if Rational.equal k Rational.one then rep_term t
      else if Rational.equal k Rational.minus_one then 
        match t with
        | Var _ | Val _ | Mult _ -> "-" ^ rep_term t
        | _ -> "-(" ^ rep_term t ^ ")"
      else if Rational.equal k Rational.zero then "0"
      else 
        let k_str = Rational.to_string k in
        match t with
        | Var _ -> k_str ^ rep_term t 
        | _ -> k_str ^ "(" ^ rep_term t ^ ")"
;;
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


  (* Étape 1: On suppose que la formule est déjà en forme prénexe *)
  (* Étape 2: Conversion des quantificateurs unversels en existentiels  *)
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

print_string "Exemple univ: ";;
print_formula example_univ;;

print_string "Exemple univ to exist: ";;
print_formula (univ_to_exist example_univ);;

(* Étape 2.1 Tirer les négations à l'intérieur de la formule (forme normale négative) *)
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


(* Étape 2.2: Élimination des négations devant les relations *)
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


(* Étape 2.3: Transforme en forme normale disjonctive *)
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

(* Étape 2.4 : Tirer les quantifications existentielles dans la disjonction *)
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

(* Étape 3: Suppression des variables *)

(*
signature :
  get_vars_in_term : term -> string list

  Renvoie la liste des variables dans l'(in)équation
*)
let rec get_vars_in_term t = match t with
  | Var x -> [x]
  | Val _ -> []
  | Add(t1, t2) | Sub(t1, t2) -> (get_vars_in_term t1) @ (get_vars_in_term t2)
  | Mult(_, t1) -> get_vars_in_term t1
;;

(* 
signature : 
  check_var : string -> formula -> int

Cette fonction vérifie la présence de la variable v (supposément introduite dans un quantificateur) dans une comparaison
Cette fonction renvoie:
  1 si v est présent
  0 sinon (v absent)
*)
let check_var v formula = match formula with
  | ComparF(lhs, _, rhs) -> 
      let vars = (get_vars_in_term lhs) @ (get_vars_in_term rhs) in
      if List.mem v vars then 1 else 0
  | _ -> 0
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
  1 si v est présent d'une autre manière dans la conjonction
  0 sinon (v absent)
*)

let rec check_conj v = function
  | BoolF(f, Conj, g) -> 
      let fres = check_conj v f in
      let gres = check_conj v g in
      if (fres = 1 || gres = 1) then 1 else 0
  | f -> check_var v f
;;

print_string (sprintf "Exemple check_conj (x < x) : %d" (check_conj "x" (conj (lt (var "x") (var "x")) (lt (var "x") (var "y")))) ^ "\n");;
print_string (sprintf "Exemple check_conj (x present) : %d" (check_conj "x" (conj (equal (var "x") (var "x")) (lt (var "x") (var "y")))) ^ "\n");;
print_string (sprintf "Exemple check_conj (x absent) : %d" (check_conj "x" (conj (equal (var "y") (var "y")) (lt (var "z") (var "y")))) ^ "\n");;

(* Étape 3.3+: non triviaux. On convertit la disjonction tableau, pour réaliser les étapes suivantes plus facilement *)

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

(* === DEBUT FONCTIONS LOT 2 === *)

(* expand_term : term -> term
   Distribue les multiplications : k * (a + b)  --->  k*a + k*b 
*)
let rec expand_term t = match t with
  (* On descend récursivement d'abord *)
  | Add(t1, t2) -> Add(expand_term t1, expand_term t2)
  | Sub(t1, t2) -> Sub(expand_term t1, expand_term t2)
  
  | Mult(k, t') ->
      (* On regarde ce qu'il y a à l'intérieur après expansion *)
      let expanded_inner = expand_term t' in
      begin match expanded_inner with
      (* k(A + B) = kA + kB *)
      | Add(a, b) -> Add(expand_term (Mult(k, a)), expand_term (Mult(k, b)))
      (* k(A - B) = kA - kB *)
      | Sub(a, b) -> Sub(expand_term (Mult(k, a)), expand_term (Mult(k, b)))
      | Val v -> Val (Rational.mul k v)
      (* k1 * (k2 * x) = (k1*k2) * x *)
      | Mult(k2, x) -> Mult(Rational.mul k k2, x)
      | _ -> Mult(k, expanded_inner)
      end
  | _ -> t
;;

(*
simplify_term : term -> term

simplifie algèbriquement l'équation afin qu'elle soit le plus simple possible
*)
let rec simplify_term t = 
  match t with
  | Val v -> Val v
  | Var x -> Var x
  | Add(t1, t2) -> 
    let s1 = simplify_term t1 in
    let s2 = simplify_term t2 in
    begin match (s1, s2) with
    | (Val a, Val b) -> Val (Rational.add a b) 
    | (Val v, t) when Rational.equal v Rational.zero -> t
    | (t, Val v) when Rational.equal v Rational.zero -> t
    | (t, Val v) when Rational.lt v Rational.zero -> 
          Sub(t, Val (Rational.neg v))
    | (Add(sub_t, Val a), Val b) -> Add(sub_t, Val (Rational.add a b))
    | (Val a, Add(Val b, sub_t)) -> Add(Val (Rational.add a b), sub_t)
    | _ -> Add(s1, s2)
    end
  | Sub(t1, t2) ->
    let s1 = simplify_term t1 in
    let s2 = simplify_term t2 in
    begin match (s1, s2) with
    | (Val a, Val b) -> Val (Rational.sub a b)
    | (t, Val v) when Rational.equal v Rational.zero -> t
    | (Val v, t) when Rational.equal v Rational.zero -> Mult(Rational.minus_one, t)
    | (t, Val v) when Rational.lt v Rational.zero -> 
          Add(t, Val (Rational.neg v))
    | (t1, t2) when t1 = t2 -> Val Rational.zero
    | _ -> Sub(s1, s2)
    end
  | Mult(k, t) ->
    let s = simplify_term t in
    match s with
    | Val v -> Val (Rational.mul k v)
    | Mult(k2, sub_t) -> Mult(Rational.mul k k2, sub_t)
    | _ -> if Rational.equal k Rational.zero then Val Rational.zero
      else if Rational.equal k Rational.one then s
      else Mult(k, s)
;;

(*
get_coeff : string -> term -> (int * term)

Peut s'apparenter à une division euclidienne de t par v :
On renvoie le couple (coefficient,reste) de la "division euclidienne" de t par v.
En le voyant comme un polynôme de degré 1 à n+1 inconnues, on pourrait le voir comme :
P(v,x1,...,xn) = Q(v) + R(x1,...,xn)
*)
let rec get_coeff v t = match t with
  | Var x when x = v -> (Rational.one, Val Rational.zero)
  | Var _ | Val _ -> (Rational.zero, t)
  
  | Add(t1, t2) ->
      let (c1, r1) = get_coeff v t1 in
      let (c2, r2) = get_coeff v t2 in
      (Rational.add c1 c2, Add(r1, r2))

  | Sub(t1, t2) ->
      let (c1, r1) = get_coeff v t1 in
      let (c2, r2) = get_coeff v t2 in
      (Rational.sub c1 c2, Sub(r1, r2))

  | Mult(k, t1) ->
      let (c, r) = get_coeff v t1 in
      (Rational.mul k c, Mult(k, r))
;;

(*
  isolate : string -> formula -> formula

  Isole v dans la formule afin d'obtenir une égalité ou une borne par rapport aux autres variables, ou à une constante
*)
let rec isolate x formula = match formula with
  | ComparF(lhs, Lt, rhs) -> (* A < B ---> Fourier-Motzkin *)
    let diff = simplify_term (Sub(lhs, rhs)) in (* A - B < 0*)
    let q, r = get_coeff x diff in (* qx + r < 0*)
    
    if Rational.equal q Rational.zero then (* r < 0, condition indépendante *)
        ComparF(simplify_term r, Lt, Val Rational.zero)
    else
      let new_rhs = Mult(Rational.div Rational.minus_one q, r) in
      if Rational.lt Rational.zero q then (* x < -r/q *)
        ComparF(Var x, Lt, simplify_term new_rhs) 
      else  (* x > -r/q car q négatif *)
        ComparF(simplify_term new_rhs, Lt, Var x) 

  | ComparF(lhs, Equal, rhs) -> (* ---> classiquement, Pivot de Gauss *)
    let diff = simplify_term (Sub (lhs, rhs)) in (* A - B = 0 *)
    let q, r = get_coeff x diff in (* qx + r = 0 *)
    if Rational.equal q Rational.zero then (* r = 0 *)
      ComparF(simplify_term r, Equal, Val Rational.zero)
    else
      let minus_r = Mult(Rational.minus_one, r) in (* x = -r/q *)
      ComparF(Var x, Equal, simplify_term (Mult(Rational.div Rational.one q, minus_r)))
  | _ -> formula
;;
(* === FIN FONCTIONS LOT 2 === *)

(*
  convert_single_conj : string -> formula -> step3_result
  
  Prend une variable cible et une conjonction de relations,
  et regroupe les termes selon la procédure A.2.3 :
  - inf : termes de la forme v < x (bornes inférieures)
  - sup : termes de la forme x < u (bornes supérieures)  
  - eq : termes de la forme w = x (égalités)
  - independent : termes χ où x n'apparaît pas

  *Adaptée pour le Lot 2 : contains_var est remplacé par isolate
*)
let convert_single_conj target_var body =
  let conjunct_list = flatten_conjunctions body in
  List.fold_left (fun acc current_atom ->
    (* Si x n'est pas présent, ça renvoie juste l'atome simplifié *)
    let isolated_atom = isolate target_var current_atom in

    match classify_x_constraint target_var isolated_atom with
      | `Inf -> { acc with inf = isolated_atom :: acc.inf }
      | `Sup -> { acc with sup = isolated_atom :: acc.sup }
      | `Eq -> { acc with eq = isolated_atom :: acc.eq }
      (* x n'est pas là (ou coeff = 0) *)
      | `Other -> { acc with independent = isolated_atom :: acc.independent }
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

(* Étape 3.4, 3.5, 3.6 : Élimination de la variable quantifiée *)

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
  Étape 3.4 : Si (w_k = x) est présent
  
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
  Étape 3.5 : Si (x < u_i) ET (v_j < x) sont présents (mais pas d'égalité)
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
  Étape 3.6 : Si uniquement (x < u_i) OU uniquement (v_j < x) est présent
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
      if result = 0 then body (* Étape 1: x absent de fv *)
      else
        let groups = convert_single_conj target_var body in (* Étape 3 *)
        eliminate_exists_from_result target_var groups (* Étapes 4, 5, 6 *)

    | f -> f
  ) disjuncts in
  
  match eliminated with
  | [] -> bottom
  | [f] -> f
  | f :: rest -> List.fold_left disj f rest
;;

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
  | ComparF(Val v1, Lt, Val v2) ->
    if v1 < v2 then top else bottom
  | ComparF(Val v1, Equal, Val v2) ->
    if v1 = v2 then top else bottom
  | ComparF(t1, op, t2) ->
      let e1 = expand_term t1 in
      let e2 = expand_term t2 in
      let s1 = simplify_term e1 in
      let s2 = simplify_term e2 in
      if s1 <> t1 || s2 <> t2 then simplify (ComparF(s1, op, s2)) (* On relance si qlqc a changé *)
      else f
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
  | NotF(f) ->
      let sf = simplify f in
      begin match sf with
      | Const Top -> bottom
      | Const Bottom -> top
      | _ -> NotF(sf)
      end
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

(* Test Étape 3.4 : cas avec égalité *)
let test_step3_4 =
  exists "x" (
    conj (equal (var "x") (var "w"))
      (conj (lt (var "x") (var "u"))
        (lt (var "v") (var "x")))
  );;

print_string "\n=== Test Étape 3.4 (avec égalité) ===\n";;
print_string "Input : ";;
print_formula test_step3_4;;
print_string "Output : ";;
print_formula (eliminate_exists test_step3_4);;

(* Test Étape 3.5 : cas sans égalité mais avec bornes inf et sup *)
let test_step3_5 =
  exists "x" (
    conj (lt (var "x") (var "u1"))
      (conj (lt (var "x") (var "u2"))
        (conj (lt (var "v1") (var "x"))
          (lt (var "v2") (var "x"))))
  );;

print_string "\n=== Test Étape 3.5 (bornes inf et sup) ===\n";;
print_string "Input : ";;
print_formula test_step3_5;;
print_string "Output : ";;
print_formula (eliminate_exists test_step3_5);;

(* Test Étape 3.6 : cas avec uniquement des bornes supérieures *)
let test_step3_6_sup =
  exists "x" (
    conj (lt (var "x") (var "u1"))
      (conj (lt (var "x") (var "u2"))
        (lt (var "a") (var "b")))  (* condition indépendante *)
  );;

print_string "\n=== Test Étape 3.6 (uniquement bornes sup) ===\n";;
print_string "Input : ";;
print_formula test_step3_6_sup;;
print_string "Output : ";;
print_formula (eliminate_exists test_step3_6_sup);;

(* Test Étape 3.6 : cas avec uniquement des bornes inférieures *)
let test_step3_6_inf =
  exists "x" (
    conj (lt (var "v1") (var "x"))
      (lt (var "v2") (var "x"))
  );;

print_string "\n=== Test Étape 3.6 (uniquement bornes inf) ===\n";;
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
  if is_prenex f then begin
    printf "Nom de la formule : \"%s\"\n" name;
    print_string "Input initial : ";
    print_formula f;
    print_string "Output final : ";
    print_formula (solve f);
    end
  else 
    printf "La formule %s doit être sous forme prénexe" name;
;;

print_string "\n=== TEST FINAL : Exemple de Prise de décision ===\n";;
final_test example_1 "Exemple 1";;

print_string "\n=== LOT 2 ===\n";;

let test_arith_1 = (*∃x ∈ ℤ, 2x < 10 ∧ 3 < x*)
  exists "x" (
    conj 
      (lt (mul 2 (var "x")) (val_ 10))
      (lt (val_ 3) (var "x"))           
  );;

final_test test_arith_1 "TEST Arithmétique 1";;

let test_arith_2 = (* ∃ x ∈ ℤ, -2x < -10 ∧ x < 8 *)
  exists "x" (
    conj 
      (lt (mul (-2) (var "x")) (val_ (-10)))
      (lt (var "x") (val_ 8))
  );;

final_test test_arith_2 "TEST Arithmétique 2";;

let test_arith_3 = (* ∃ x ∈ ℤ, x + 5 < x + 2 *)
  exists "x" (
    lt (add (var "x") (val_ 5)) (add (var "x") (val_ 2))
  );;

final_test test_arith_3 "TEST Arithmétique 3";;

let test_arith_4 = (* ∃ x ∈ ℤ, 2x + y < 10 ∧ z < 3x *)
  exists "x" (
    conj
      (lt (add (mul 2 (var "x")) (var "y")) (val_ 10))
      (lt (var "z") (mul 3 (var "x")))
  );;

final_test test_arith_4 "TEST Arithmétique 4";;

let test_5 = NotF (NotF (Const Bottom));;

final_test test_5 "TEST négation de constante";;

let test_precision = 
  exists "x" (
    lt 
      (add (var "x") (frac 3 10))            (* x + 0.3 *)
      (add (var "x") (add (frac 1 10) (frac 2 10))) (* x + 0.1 + 0.2 *)
  );;

final_test test_precision "TEST Précision (0.3 < 0.1 + 0.2)";;