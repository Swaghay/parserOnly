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

let rec string_of_expression (e : expression) : string =
  match e with
  | Application (e, arg) ->
    (string_of_expression e) ^ " (" ^ string_of_expression arg ^ ")"
  | Identifier name -> name

let string_of_hint (h : hint option) : string =
  match h with
  | Some Axiom -> "\n(*hint: axiom *)"
  | None -> ""
let string_of_equality (e : equality) : string =
  match e with
  | Equality (e1, e2) -> "(" ^ (string_of_expression e1) ^ " = " ^ (string_of_expression e2) ^ ")"
let string_of_typedvariable (TypedVariable (name, type_name) : typedVariable) : string =
  "(" ^ name ^ " : " ^ type_name ^ ")"
let string_of_declaration (d : declaration) : string =
  match d with
  | ProofDeclaration (name, args, equality, hint) ->
    let arg_strings = List.map string_of_typedvariable args in
    "let (*prove*) " ^ name ^ " " ^ (String.concat " " arg_strings) ^ " = "
     ^ string_of_equality equality ^ string_of_hint hint

module Substitution = struct 

  exception MergeError

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

  let rec substitute (vars: string list) (substitution: t) (e: expression) = 
    match e with
    | Identifier s -> if (List.mem s vars) then (find s substitution) else Identifier s
    | Application (e1, e2) -> Application (substitute vars substitution e1, substitute vars substitution e2)

  let print_subst (s : t) =
    Smap.iter (fun k v -> print_endline (k ^ " -> " ^ string_of_expression v)) s

end

let rec extractvars (lst: typedVariable list) =
  match lst with
  | [] -> []
  | TypedVariable (s1, _)::t -> s1::extractvars t

let rec proofs_of_simple eqs (lst : declaration list) =
  match lst with
  | [] -> []
  | (ProofDeclaration (nm,vars,eq,hint))::decls  -> (match hint with
                                                    | None -> (("Proof of " ^ nm ^ ": ") :: ["TODO"]):: (proofs_of_simple ((nm,extractvars vars,eq)::eqs) decls)
                                                    | _ -> proofs_of_simple ((nm,extractvars vars,eq)::eqs)
                                                    decls)
  

  