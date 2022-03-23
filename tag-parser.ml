#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
  | [] -> ScmNil
  | hd::[] -> ScmPair (hd, ScmNil)
  | hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
  | [] -> raise X_proper_list_error
  | hd::[] -> hd
  | hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
  match scm_list with
  | ScmNil -> sexpr
  | ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
  | _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
  match sexpr with
  | ScmNil -> ScmNil
  | ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
  | _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
  match sexpr1, sexpr2 with
  | ScmNil, ScmNil -> ScmNil
  | ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
  | _, _ ->
     let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
     raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
  | ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
  | ScmNil -> []
  | sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;


(*let rec improperList_to_array= function*)
(*|ScmSymbol(sym)->sym*)
(*|ScmPair(ScmSymbol(sym), tl)->sym:: improperList_to_array tl*)

let rec scm_improper_list_to_list= function
  |ScmPair(ScmSymbol(s1), ScmSymbol(s2))->[ScmSymbol(s1);ScmSymbol(s2)]
  |ScmPair(h,t)->h::scm_improper_list_to_list t
  |_->raise X_proper_list_error

let rec scm_is_list = function
  | ScmPair (hd, tl) -> scm_is_list tl
  | ScmNil -> true
  | _ -> false

let rec scm_list_length = function
  | ScmPair (hd, tl) -> 1 + (scm_list_length tl)
  | ScmNil -> 0
  | sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
  let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
  let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

  let untag_lambda_opt vars var body =
    let vars = match vars with
      | [] -> ScmSymbol var
      | _ -> list_to_improper_list (untag_vars (vars@[var])) in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

  match expr with
  | (ScmConst (ScmSymbol(_) as sexpr)
     | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
  | ScmConst s -> s
  | ScmVar (name) -> ScmSymbol(name)
  | ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
  | ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
  | ScmSeq(exprs) -> untag_tagged_list "begin" exprs
  | ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
  | ScmDef (var, value) -> untag_tagged_list "define" [var; value]
  | ScmOr (exprs) -> untag_tagged_list "or" exprs
  | ScmLambdaSimple (vars, ScmSeq(body)) ->
     let vars = list_to_proper_list (untag_vars vars) in
     let body = List.map untag body in
     list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
  | ScmLambdaSimple (vars, body) ->
     let vars = list_to_proper_list (untag_vars vars) in
     list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
  | ScmLambdaOpt (vars, var, ScmSeq(body)) ->
     let body = List.map untag body in
     untag_lambda_opt vars var body
  | ScmLambdaOpt (vars, var, body) ->
     let body = [untag body] in
     untag_lambda_opt vars var body
  | ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
  string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
  match n1, n2 with
  | ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
     numerator1 = numerator2 && denominator1 = denominator2
  | ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
  | _, _ -> false

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
  | ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
  | ScmChar(char1), ScmChar(char2) -> char1 = char2
  | ScmString(string1), ScmString(string2) -> String.equal string1 string2
  | ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
  | ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
  | ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
  | ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                                             (expr_eq dit1 dit2) &&
                                                               (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
     List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
     (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;


exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;


module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;;

module Tag_Parser (* : TAG_PARSER *) = struct


  let reserved_word_list =
    ["and"; "begin"; "cond"; "define"; "else";
     "if"; "lambda"; "let"; "let*"; "letrec"; "or";
     "quasiquote"; "quote"; "set!"; "unquote";
     "unquote-splicing"];;

  let unsymbolify = function
    | ScmSymbol str -> str
    | sexpr -> raise (X_syntax_error (sexpr, "not a symbol"));;

  let rec contains element = function
      a::c -> if (a = element) then true else (contains element c)
    | []   -> false;;

  let rec scheme_list = function
    | ScmPair(car, cdr) ->
       let (left, right) = scheme_list cdr in
       (car :: left, right)
    | sexpr -> ([], sexpr);;

  let rec tag_parse_expression sexpr =
    let sexpr = macro_expand sexpr in
    (match sexpr with
     | ScmVoid -> ScmConst ScmVoid
     | ScmNil -> (ScmConst ScmVoid)
     | ScmBoolean(b) -> (ScmConst (ScmBoolean(b)))
     | ScmChar(ch) -> (ScmConst (ScmChar(ch)))
     | ScmString(str) -> (ScmConst (ScmString(str)))
     | ScmNumber(num) -> (ScmConst (ScmNumber(num)))
     | ScmPair(ScmSymbol "quote" , (ScmPair (sexpr,ScmNil)))-> (ScmConst sexpr)

     | ScmSymbol(sym) when (not (List.mem sym reserved_word_list)) ->
        ScmVar sym
     |ScmPair (ScmSymbol "if",
               (ScmPair (a,
                        ScmPair (b,
                                 ScmPair(c,
                                         ScmNil))))) ->
       ScmIf(tag_parse_expression a,
             tag_parse_expression b,
             tag_parse_expression c)
     |ScmPair(ScmSymbol "if",
              (ScmPair (a,
                        ScmPair (b,
                                 ScmNil)))) ->
       ScmIf(tag_parse_expression a,
             tag_parse_expression b,
             tag_parse_expression ScmVoid)
     | ScmPair(ScmSymbol "or", ScmNil) ->
        tag_parse_expression (ScmBoolean false)
     | ScmPair(ScmSymbol "or", ScmPair (expr,ScmNil)) ->
        tag_parse_expression expr
     | ScmPair (ScmSymbol "or", exprs) ->
        (match (scheme_list exprs) with
         | exprs, ScmNil -> 
            ScmOr(List.map tag_parse_expression exprs)
         | _, _ -> raise (X_syntax_error(exprs, "invalid or-fieds")))
     | ScmPair (ScmSymbol "lambda", ScmPair (params, exprs)) ->
        let body = tag_parse_expression (ScmPair (ScmSymbol "begin", exprs)) in
        (match (scheme_list params) with
         | left, ScmNil ->
            ScmLambdaSimple(List.map unsymbolify left, body)
         | left, ScmSymbol opt ->
            ScmLambdaOpt(List.map unsymbolify left, opt, body)
         | _, _ -> raise (X_syntax_error (params, "invalid param list")))
     |ScmPair(ScmSymbol "define", ScmPair(ScmSymbol (sym),ScmPair(x,ScmNil)))->ScmDef((tag_parse_expression (ScmSymbol(sym))),(tag_parse_expression x))
     |ScmPair(ScmSymbol "define", ScmPair(ScmPair(ScmSymbol (sym),y),x))->ScmDef((tag_parse_expression (ScmSymbol(sym))),(tag_parse_expression(ScmPair((ScmSymbol "lambda"),(ScmPair (y,x))))))
     |ScmPair(ScmSymbol "set!", ScmPair(x,ScmPair(y,ScmNil)))->ScmSet((tag_parse_expression x),(tag_parse_expression y))

     | ScmPair (ScmSymbol "begin", ScmNil) -> tag_parse_expression ScmVoid
     | ScmPair (ScmSymbol "begin", ScmPair (expr, ScmNil)) ->
        tag_parse_expression expr
     | ScmPair (ScmSymbol "begin", exprs) ->
        (match (scheme_list exprs) with
         | (exprs, ScmNil) -> ScmSeq (List.map tag_parse_expression exprs)
         | _ -> raise (X_syntax_error (exprs, "not a proper list")))

     |ScmPair(x,y)->
       let rec list_to_tp= function
         |[]->[]
         |h::t->tag_parse_expression h :: list_to_tp t in
       ScmApplic((tag_parse_expression x),(list_to_tp(scm_list_to_list y)))
     |_ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized")))



  and expand_and expr =
    (match expr with
     |ScmNil -> ScmBoolean(true)
     |ScmPair(exp , ScmNil)->exp
     |ScmPair(carExp ,cdrExp)->	ScmPair(ScmSymbol("if"),ScmPair(carExp , ScmPair(expand_and cdrExp , ScmPair(ScmBoolean(false),ScmNil))))
     |_ -> raise (X_syntax_error(expr , "errorAnd")))

  and make_lambda body=
    list_to_proper_list[ScmSymbol("lambda");ScmNil;body]

  and extract_params ribs =
    (match ribs with
     | ScmPair(ScmPair(ScmSymbol(sym),value),ScmNil)-> ScmPair(ScmSymbol(sym) , ScmNil)
     | ScmPair(ScmPair(ScmSymbol(sym),ScmPair(value, ScmNil)), rest) -> ScmPair(ScmSymbol(sym) , (extract_params rest))
     | _ -> raise (X_syntax_error (ribs, "error in extract params")))

  and extract_values ribs =
    (match ribs with
     | ScmPair(ScmPair(ScmSymbol(sym),ScmPair(value,ScmNil)),ScmNil) -> ScmPair(value , ScmNil)
     | ScmPair(ScmPair(ScmSymbol(sym),ScmPair(value, ScmNil) ), rest) -> ScmPair(value , extract_values rest)
     | _ -> raise (X_syntax_error (ribs, "error in extract params")))

  and expand_let expr=
    (match expr with
     |ScmPair(ScmNil,ScmPair(body,ScmNil))->ScmPair(ScmPair(ScmSymbol "lambda",ScmPair(ScmNil,ScmPair(body,ScmNil))),ScmNil)
     |ScmPair(ribs,body)->ScmPair(ScmPair(ScmSymbol "lambda",ScmPair(extract_params ribs,body)),extract_values ribs)
     | _ -> raise (X_syntax_error (expr, "error in expand_let")))


  and expand_letrec ribs exprs =
    match (scheme_list ribs) with
    | ribs, ScmNil ->
       let name_vals =
         List.map
           (function
            | ScmPair (name, ScmPair (expr, ScmNil)) -> (name, expr)
            | rib -> raise (X_syntax_error (rib,
                                           "improper letrec-rib structure")))
           ribs in
       let names = List.map (fun (name, value) -> name) name_vals in
       let vals = List.map (fun (name, value) -> value) name_vals in
       let whatevers =
         List.map
           (fun name -> ScmPair (name,
                              ScmPair (ScmPair (ScmSymbol "quote",
                                                ScmPair (ScmSymbol "whatever",
                                                         ScmNil)),
                                       ScmNil)))
           names in
       let new_ribs =
         List.fold_right
           (fun car cdr -> ScmPair (car, cdr))
           whatevers
           ScmNil in
       let sets =
         List.map2
           (fun name value ->
             ScmPair (ScmSymbol "set!",
                      ScmPair (name,
                               ScmPair (value, ScmNil))))
           names
           vals in
       let exprs =
         List.fold_right
           (fun car cdr -> ScmPair (car, cdr))
           sets
           exprs in
       ScmPair (ScmSymbol "let",
                ScmPair (new_ribs, exprs))
    | _, _ -> raise (X_syntax_error (ribs, "letrec-ribs are imporoper!"))

  and make_set expr=
    (match expr with
     |ScmPair(ScmPair(ScmSymbol(sym),ScmPair(value,ScmNil)),ScmNil)->ScmPair(list_to_proper_list[ScmSymbol "set";ScmSymbol (sym);value],ScmNil)
     |ScmPair(ScmPair(ScmSymbol(sym),ScmPair(value,ScmNil)),rest)->ScmPair(list_to_proper_list[ScmSymbol "set";ScmSymbol (sym)],make_set rest)
     | _ -> raise (X_syntax_error (expr, "error in make_set")))

  and make_whatever expr=
    (match expr with
     |ScmPair(ScmPair(ScmSymbol(sym),value),ScmNil)->ScmPair(list_to_proper_list[ScmSymbol(sym); list_to_proper_list[ScmSymbol "quote"; ScmSymbol "whatever"]], ScmNil)
     |ScmPair(ScmPair(ScmSymbol(sym),value),rest)->ScmPair(list_to_proper_list[ScmSymbol(sym); list_to_proper_list[ScmSymbol "quote"; ScmSymbol "whatever"]],make_whatever rest)
     | _ -> raise (X_syntax_error (expr, "error in make_whatever")))

  and expand_quasiquote sexpr =
    match sexpr with
    | ScmPair (ScmSymbol "unquote", ScmPair (sexpr', ScmNil)) -> sexpr'
    | ScmPair (ScmSymbol "unquote-splicing", ScmPair (sexpr', ScmNil)) ->
       ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
    | ScmPair (ScmPair (ScmSymbol "unquote",
                        ScmPair (car, ScmNil)),
               cdr) ->
       ScmPair (ScmSymbol "cons",
                ScmPair (car, ScmPair (expand_quasiquote cdr,
                                       ScmNil)))
    | ScmPair (ScmPair (ScmSymbol "unquote-splicing",
                        ScmPair (car, ScmNil)),
               cdr) ->
       ScmPair (ScmSymbol "append",
                ScmPair (car,
                         ScmPair (expand_quasiquote cdr, ScmNil)))
    | ScmPair (car, cdr) ->
       ScmPair (ScmSymbol "cons",
                ScmPair (expand_quasiquote car,
                         ScmPair (expand_quasiquote cdr,
                                  ScmNil)))
    | ScmNil -> ScmPair (ScmSymbol "quote", ScmPair (ScmNil, ScmNil))
    | ScmSymbol _ -> ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
    | ScmVector sexprs ->
       let sexpr =
         expand_quasiquote
           (List.fold_right (fun car cdr -> ScmPair (car, cdr)) sexprs ScmNil) in
       ScmPair (ScmSymbol "list->vector", ScmPair (sexpr, ScmNil))
    | _ -> sexpr

  and expand_cond = function
    |ScmNil->ScmNil
    | ScmPair (ScmPair (ScmSymbol "else", exprs), _ribs) ->
       ScmPair (ScmSymbol "begin", exprs)
    | ScmPair (ScmPair (proc,
                        ScmPair (ScmSymbol "=>",
                                 ScmPair (expr, ScmNil))),
               ribs) ->
       let remaining = expand_cond ribs in
       ScmPair
         (ScmSymbol "let",
          ScmPair
            (ScmPair
               (ScmPair (ScmSymbol "value", ScmPair (proc, ScmNil)),
                ScmPair
                  (ScmPair
                     (ScmSymbol "f",
                      ScmPair
                        (ScmPair
                           (ScmSymbol "lambda",
                            ScmPair (ScmNil,
                                     ScmPair (expr, ScmNil))),
                         ScmNil)),
                   ScmPair
                     (ScmPair
                        (ScmSymbol "rest",
                         ScmPair
                           (ScmPair
                              (ScmSymbol "lambda",
                               ScmPair (ScmNil,
                                        ScmPair (remaining, ScmNil))),
                            ScmNil)),
                      ScmNil))),
             ScmPair
               (ScmPair
                  (ScmSymbol "if",
                   ScmPair
                     (ScmSymbol "value",
                      ScmPair
                        (ScmPair
                           (ScmPair (ScmSymbol "f", ScmNil),
                            ScmPair (ScmSymbol "value", ScmNil)),
                         ScmPair (ScmPair (ScmSymbol "rest", ScmNil),
                                  ScmNil)))),
                ScmNil)))
    | ScmPair (ScmPair (test, exprs), ribs) ->
       let remaining = expand_cond ribs in
       macro_expand(ScmPair(ScmSymbol  "if",
                                       ScmPair
                                       (test,
                                        ScmPair
                                        (ScmPair(ScmSymbol "begin" , exprs),
                                         ScmPair(remaining,ScmNil)))))
    | sexpr -> raise (X_syntax_error (sexpr, "invalid cond ribs!"))

  and macro_expand sexpr =
    match sexpr with
    (* Handle macro expansion patterns here *)
    | ScmPair(ScmSymbol "quasiquote", ScmPair(exp, ScmNil)) ->
           macro_expand (expand_quasiquote exp)
    | ScmPair(ScmSymbol "cond", ribs) -> macro_expand (expand_cond ribs)
    | ScmPair(ScmSymbol "and", exp) -> expand_and exp
    | ScmPair(ScmSymbol "let",exp) -> expand_let exp

    | ScmPair (ScmSymbol "let*", ScmPair (ScmNil, exprs)) ->
       macro_expand (ScmPair (ScmSymbol "let", ScmPair (ScmNil, exprs)))

    |  ScmPair (ScmSymbol "let*",
                     ScmPair
                            (ScmPair
                                 (ScmPair (name,
                                               ScmPair (arg, ScmNil)), ScmNil), exprs)) ->
                               macro_expand(ScmPair (ScmSymbol "let",
                                                                  ScmPair
                                                                    (ScmPair
                                                                       (ScmPair (name,
                                                                                 ScmPair (arg, ScmNil)), ScmNil),
                                                                     exprs)))
    | ScmPair (ScmSymbol "let*",
                ScmPair
                       (ScmPair
                               (ScmPair (name,
                                        ScmPair (arg, ScmNil)), ribs), exprs)) ->
                 macro_expand
             (ScmPair (ScmSymbol "let",
                       ScmPair
                         (ScmPair
                            (ScmPair (name,
                                      ScmPair (arg, ScmNil)), ScmNil),
                          ScmPair
                            (ScmPair
                               (ScmSymbol "let*", ScmPair (ribs, exprs)),
                             ScmNil))))



    | ScmPair (ScmSymbol "letrec", ScmPair (ribs, exprs)) ->
       macro_expand (expand_letrec ribs exprs)

    | _ -> sexpr

end;;

