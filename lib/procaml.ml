include Ast

module Parser = Parser
module Lexer = Lexer

let parse_expression (s: string) : expression =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.expression_eof
      Lexer.token lexbuf in ast

let parse (s : string) : declaration list =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.main Lexer.token lexbuf in
     ast

let rec string_of_pattern (p : pattern) : string =
  match p with
  | Constructor (name, []) -> name
  | Constructor (name, patterns) -> name ^ " (" ^ (String.concat ", " (List.map string_of_pattern patterns)) ^ ")"
  | Variable (name, type_name) -> name ^ " : " ^ type_name

let rec string_of_expression (e : expression) : string =
  match e with
  (* If you're confused about the structure of the AST,
     you can use this code to print more parentheses
     (besides using utop):
  | Application (Application (Identifier ",", e), arg) ->
    (string_of_expression_paren e) ^ ", " ^ (string_of_expression_paren arg)
  | Application (e, arg) ->
    (string_of_expression_paren e) ^ " " ^ string_of_expression_paren arg
     
     *)
  | Application (Application (Identifier ",", e), arg) ->
    (string_of_expression e) ^ ", " ^ (string_of_expression arg)
  | Application (e, arg) ->
    (string_of_expression e) ^ " " ^ string_of_expression_paren arg
  | Identifier name -> name
  | Match (e, cases) ->
    let case_strings = List.map (fun (pattern, body) ->
      let pattern_string = match pattern with
        | Constructor (name, []) -> name
        | Constructor (name, patterns) -> name ^ " (" ^ (String.concat ", " (List.map string_of_pattern patterns)) ^ ")"
        | Variable (name, type_name) -> name ^ " : " ^ type_name
      in
      (* the outer parentheses are redundant if the body does not end in a match, but better to be safe then sorry *)
      pattern_string ^ " -> " ^ (string_of_expression_paren body)
    ) cases in
    "match " ^ (string_of_expression e) ^ " with " ^ (String.concat " | " case_strings)

and string_of_expression_paren (e : expression) : string =
  match e with
  | Identifier name -> name
  | e -> "(" ^ string_of_expression e ^ ")"

let string_of_hint (h : hint option) : string =
  match h with
  | Some Axiom -> "\n(*hint: axiom *)"
  | Some (Induction name) -> "\n(*hint: induction " ^ name ^ " *)"
  | None -> ""
let string_of_equality (e : equality) : string =
  match e with
  | Equality (e1, e2) -> "(" ^ (string_of_expression e1) ^ " = " ^ (string_of_expression e2) ^ ")"
let string_of_typedvariable (TypedVariable (name, type_name) : typedVariable) : string =
  "(" ^ name ^ " : " ^ type_name ^ ")"
let string_of_declaration (d : declaration) : string =
  match d with
  | TypeDeclaration (name, variants) ->
    let variant_strings = List.map (function Variant (name, []) -> name
      | Variant (name, types) -> name ^ " of (" ^ (String.concat "*" types) ^ ")"
    ) variants in
    "type " ^ name ^ " = " ^ (String.concat " | " variant_strings)
  | FunctionDeclaration (TypedVariable (name, type_name), args, body) ->
    let arg_strings = List.map (function TypedVariable (name, type_name) -> "(" ^ name ^ " : " ^ type_name ^ ")") args in
    "let rec " ^ name ^ " " ^ (String.concat " " arg_strings) ^ " : " ^ type_name ^ " = " ^ (string_of_expression body)
  | ProofDeclaration (name, args, equality, hint) ->
    let arg_strings = List.map string_of_typedvariable args in
    "let (*prove*) " ^ name ^ " " ^ (String.concat " " arg_strings) ^ " = "
     ^ string_of_equality equality ^ string_of_hint hint


module Substitution = struct 

  exception MergeError
  exception SubstitutionError

  module Smap = Map.Make(String)

  type t = expression Smap.t

  let empty = Smap.empty

  let singleton = Smap.singleton

  let merge map1 map2 = 
    let helper _ v1 v2 = 
    match v1, v2 with
    | None, None -> None
    | Some mm1, None -> Some mm1
    | None, Some mm2 -> Some mm2
    | Some mm1, Some mm2 -> if mm1 = mm2 then Some mm1 else raise MergeError
    in Smap.merge helper map1 map2

  let find = Smap.find

 (*substitute ["a","b","c"], bar x y, foo (bar a b) c*)
  let rec substitute (vars: string list) (sub: t) (expr: expression) = 

    match expr with
    | Identifier x -> if List.mem x vars then try (find x sub) with Not_found -> raise SubstitutionError
                      else Identifier x
    | Application (expr1, expr2) -> Application (substitute vars sub expr1, substitute vars sub expr2)
    | _ -> assert false
  (*
  Application(foo(bar a b), c)
  foo(bar a b)
  
  *)
  let print_subst (s : t) =
    Smap.iter (fun k v -> print_endline (k ^ " -> " ^ string_of_expression v)) s

end

let rec match_expression (vars: string list) (pattern: expression) (goal: expression) =
  match pattern, goal with
  | Identifier x, Identifier g when x = g -> Some Substitution.empty 
  | Identifier x, _ when (List.mem x vars) -> Some (Substitution.singleton x g)
  | Application (patExpr1, patExpr2), Application (goalExpr1, goalExpr2) -> 
    let sub1 = (match_expression vars patExpr1 goalExpr1) in
    let sub2 = (match_expression vars patExpr2 goalExpr2) in
    (match sub1, sub2 with
    | Some x, Some y -> (match (Substitution.merge x y) with
       | a -> Some a
       | exception Substitution.MergeError -> None)
    | _, _ -> None)
  | _, _ -> None
(*attempt_rewrite ["a","b","c"] Equality(parse "bar x y", parse "y") (parse "foo (bar a b) c")*)
let rec attempt_rewrite (vars: string list) (Equality(lhs, rhs)) (expr: expression) =
  let () = print_string ("EXPR: " ^ string_of_expression expr ^ "\n") in
  match (match_expression vars lhs expr) with
  | Some s -> let () = print_string (string_of_expression lhs ^ "\n") in Some (Substitution.substitute vars s expr) (*["a","b","c"], bar x y, foo (bar a b) c*)
  | None -> (match expr with
            | Application (e1, e2) -> (match (attempt_rewrite vars (Equality(lhs,rhs)) e1) with
                                      | None ->(match (attempt_rewrite vars (Equality(lhs,rhs)) e2) with
                                                | None -> let () = print_string ("LHSNone: " ^ string_of_expression lhs ^ "\n") in None 
                                                | Some e2' ->  let () = print_string ("LHSSome: " ^ string_of_expression lhs ^ "\n") in Some (Application (e1, e2')))
                                      | Some e1' -> Some (Application (e1', e2)))  
            | _ -> None)
       
let rec tryEqualities (eqs) (expr: expression) = 
  match eqs with
  | [] -> None
  | (name,var,lhs,rhs)::tl -> let () = print_string ("LHS: " ^ string_of_expression lhs ^ "\n" ^ "RHS: " ^ string_of_expression rhs ^ "\n") in match (attempt_rewrite var (Equality(lhs, rhs)) expr) with
                              | None -> (tryEqualities tl expr)
                              | Some(e) -> Some(name, e)

  let rec extractvars (lst: typedVariable list) =
    match lst with
    | [] -> []
    | TypedVariable (s1, _)::t -> s1::extractvars t

let rec extractAxioms (lst: declaration list) =
  match lst with
  | [] -> []
  | ProofDeclaration(name, typedVarLst, Equality(lhs, rhs), Some Axiom)::t -> (name, (extractvars typedVarLst), lhs, rhs)::extractAxioms t
  | _::t -> extractAxioms t

let rec proofs_of_simple eqs (lst : declaration list) =
  match lst with
  | [] -> []
  | (ProofDeclaration (nm,vars,eq,hint))::decls  -> (match hint with
                                                    | None -> (("Proof of " ^ nm ^ ": ") :: ["TODO"]):: (proofs_of_simple ((nm,extractvars vars,eq)::eqs) decls)
                                                    | _ -> proofs_of_simple ((nm,extractvars vars,eq)::eqs)
                                                    decls)
  | _ -> assert false
  

  (*
tryEqualities a (parse_expression "foo (bar a b) c");;
LHS: foo x x
RHS: bar x
EXPR: foo (bar a b) c
EXPR: foo (bar a b)
EXPR: foo
EXPR: bar a b
EXPR: bar a
EXPR: bar
EXPR: a
LHSNone: foo x x
EXPR: b
LHSNone: foo x x
LHSNone: foo x x
EXPR: c
LHSNone: foo x x
LHS: bar x y
RHS: y
EXPR: foo (bar a b) c
- : (string * expression) option = Some ("eq2", Identifier "c")   
*)

(*
tryEqualities a
(parse_expression "bozo (bar a) (foo (bar a))");;
- : (string * expression) option =
Some
 ("eq2",
  Application
   (Identifier "foo", Application (Identifier "bar", Identifier "a")))
   *)


(* 
   attempt_rewrite ["a";"b";"c"] (Equality(parse_expression "bar x y", parse_expression "y")) (parse_expression "foo (bar a b) c");;   
EXPR: foo (bar a b) c
- : expression option = Some (Identifier "y")

*)