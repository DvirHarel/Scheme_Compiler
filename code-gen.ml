#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second
     argument is the fvars table type, and the third is an expr' that has been annotated
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

let counter_L = ref 0;;

let the_next_one ()=
  let next ()= counter_L:= !counter_L + 1 in
begin next (); !counter_L end;;

let rec get_the_sexps expr =
  match expr with
  | ScmConst'(ScmVoid) -> []
  | ScmConst'(a) -> [a]
  | ScmIf'(test,dit,dif) -> (((get_the_sexps test) @ (get_the_sexps dit)) @ (get_the_sexps dif))
  | ScmLambdaSimple'(args,body) -> get_the_sexps body
  | ScmLambdaOpt'(args, arg, body) -> get_the_sexps body
  | ScmOr'(list_of_subtrees) -> List.fold_left (fun acc x -> (acc @ (get_the_sexps x))) [] list_of_subtrees
  | ScmSet'(var,value_for_var) -> get_the_sexps value_for_var
  | ScmSeq'(seq) ->  List.fold_left (fun acc x -> List.append acc (get_the_sexps x)) [] seq
  | ScmDef'(var,value_for_var) -> get_the_sexps value_for_var
  | ScmApplic'(body,args) -> ((get_the_sexps body)@ (List.fold_left (fun acc arg -> (acc @ (get_the_sexps arg))) [] args))
  | ScmApplicTP'(body,args) -> ((get_the_sexps body) @ (List.fold_left (fun acc arg -> (acc @ (get_the_sexps arg))) [] args))
  | ScmVar'(x) -> []
  | ScmBoxSet'(var,value_for_var) -> get_the_sexps value_for_var
  | ScmBoxGet'(var) -> []
  | ScmBox'(var) -> [] ;;


  let rec eliminate_the_dups lst =
    let acc = [] in
    let rec aux acc = function
        | [] -> acc
        | car::rest -> if (List.mem car acc)
                         then (aux rest acc )
                         else (aux rest (acc @ [car])) in
                     aux lst acc;;


  let expand_the_sexprs list_of_exps =
    let rec inner_expand expr =
      match expr with
      | ScmPair(a,b) -> (((inner_expand a) @ (inner_expand b)) @ [((ScmPair(a,b)))])
      | ScmSymbol(sym) -> [(ScmString(sym))] @ [(ScmSymbol(sym))]
      | ScmVector(exp) -> (List.fold_left (fun x y -> x @ (inner_expand y)) [] exp) @ [((ScmVector(exp)))]
      | sexp -> [(sexp)] in
    List.concat (List.map (fun sexpr -> inner_expand sexpr) list_of_exps);;


  let rec find_offset sexp const_tbl =
    match const_tbl with
        | car::rest ->
            let (this_sexpr, (offset, _)) = car in
            if (this_sexpr = sexp)
                then (string_of_int offset)
                else find_offset sexp rest
        | [] -> "X_this_should_not_happen";;

  let rec find_offset_from_fvars name fvars =
    match fvars with
        |car::rest ->
            let (this_name, offset) = car in
                if(name = this_name)
                    then string_of_int offset
                    else find_offset_from_fvars name rest
        |[] -> "X_this_should_not_happen";;

  let rec build_const_tbl sexprs const_tbl current_offset =
    let find_const_entry_point sexpr const_tbl current_offset =
      match sexpr with
      | ScmChar(ch) -> (current_offset + 2 , (sexpr , (current_offset , "MAKE_LITERAL_CHAR (" ^ (string_of_int (int_of_char ch)) ^ ")\n")))
      | ScmBoolean(false) -> (current_offset + 2 ,(sexpr, (current_offset , "db T_BOOL, 0\n") ))
      | ScmBoolean(true) -> (current_offset + 2 ,(sexpr, (current_offset , "db T_BOOL, 1\n") ))
      | ScmNil -> (current_offset + 1 ,(sexpr, (current_offset , "db T_NIL\n") ) )
      | ScmVoid -> (current_offset + 1 ,(sexpr, (current_offset , "db T_VOID\n") ) )
      | ScmNumber(ScmRational(number,number2)) -> (current_offset + 17 ,(sexpr, (current_offset , "MAKE_LITERAL_RATIONAL(" ^ (string_of_int number) ^ "," ^ (string_of_int number2) ^ ")\n")))
      | ScmNumber(ScmReal(real)) -> (current_offset + 9 ,(sexpr, (current_offset , "MAKE_LITERAL_FLOAT(" ^ (string_of_float real) ^ ")\n")))
      | ScmString(str) -> (current_offset + 9 + (String.length str) ,(sexpr, (current_offset, "MAKE_LITERAL_STRING {\"" ^str^ "\""^"}") ) )
      | ScmSymbol(sym) -> (current_offset + 9 ,(sexpr , (current_offset  , "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (find_offset (ScmString(sym)) const_tbl) ^ ")\n")))
      | ScmPair(a,b) -> (current_offset + 17, (sexpr , (current_offset  , "MAKE_LITERAL_PAIR(const_tbl+" ^ (find_offset (a) const_tbl) ^ ",const_tbl+" ^ (find_offset (b) const_tbl) ^")\n")))
      | ScmVector(exp) ->
              begin match exp with
              | [] -> (current_offset + 9 + 8*(List.length exp), (ScmVector(exp) , (current_offset  , "MAKE_LITERAL_VECTOR ")))
              | first :: rest ->
                      (current_offset + 9 + 8*(List.length exp), (ScmVector(exp) , (current_offset  , "MAKE_LITERAL_VECTOR "^ (List.fold_left(fun x y -> x^",const_tbl+" ^ (find_offset y const_tbl)) ("const_tbl+" ^ (find_offset first const_tbl)) rest)))) end
      in
    match sexprs with
    | sexpr::rest ->
        let (the_offset, start_point) = (find_const_entry_point sexpr const_tbl current_offset) in
                        build_const_tbl rest ((const_tbl)@[start_point]) the_offset
    | [] -> const_tbl


  let rec select_free_vars expr =
    match expr with
    | ScmConst'(ScmVoid) -> []
    | ScmConst'(var) -> []
    | ScmIf'(test,dit,dif) ->  ((select_free_vars test) @ (select_free_vars dit))@ (select_free_vars dif)
    | ScmLambdaSimple'(args,body) -> select_free_vars body
    | ScmLambdaOpt'(args, arg, body) -> select_free_vars body
    | ScmOr'(list_of_subtrees) -> List.fold_left (fun acc z ->  (acc @ (select_free_vars z))) [] list_of_subtrees
    | ScmSet'(var,value_for_var) ->  ((select_free_vars (ScmVar' (var)))@ (select_free_vars value_for_var))
    | ScmSeq'(seq) ->  List.fold_left (fun acc e -> (acc @ (select_free_vars e))) [] seq
    | ScmDef'(var,value_for_var) -> ((select_free_vars (ScmVar' (var))) @ (select_free_vars value_for_var))
    | ScmApplic'(sub_exp1,sub_exps) -> ((select_free_vars sub_exp1) @ (List.fold_left (fun acc arg ->  (acc @ (select_free_vars arg))) [] sub_exps))
    | ScmApplicTP'(sub_exp1,sub_exps) -> ((select_free_vars sub_exp1)@ (List.fold_left (fun acc arg ->  (acc @ (select_free_vars arg))) [] sub_exps))
    | ScmVar'(VarFree(var)) -> [var]
    | ScmVar'(var) -> []
    | ScmBoxSet'(var,value_for_var) ->  ((select_free_vars (ScmVar'(var))) @ (select_free_vars value_for_var))
    | ScmBoxGet'(var) -> (select_free_vars (ScmVar'(var)))
    | ScmBox'(var) -> (select_free_vars (ScmVar'(var)));;


  let rec build_fvars_tbl fvars index=
      match fvars with
      | first::rest -> (first, index)::(build_fvars_tbl rest (index+8))
      | [] -> [];;


  let rec expr_to_string consts fvars e depth=
    match e with
     | ScmIf'(test,dit,dif) ->
            let num = the_next_one () in
            let the_else_L = "Lelse" ^ (string_of_int num) in
            let the_exit_L = "Lexit" ^ (string_of_int num) in
            (expr_to_string consts fvars test depth) ^ "cmp rax, SOB_FALSE_ADDRESS\nje " ^ the_else_L ^ "\n" ^
            (expr_to_string consts fvars dit depth) ^ "jmp " ^ the_exit_L ^ "\n" ^
            the_else_L ^ ":\n" ^
            (expr_to_string consts fvars dif depth) ^
            the_exit_L ^ ":\n"

    | ScmLambdaSimple'(args,body) ->
            let number= the_next_one () in
            let cont_L = "Lcont" ^ (string_of_int number) in
            let code_L = "Lcode" ^ (string_of_int number) in
            "MAKE_EXT_ENV " ^ (string_of_int depth) ^
            "\nmov rbx, rax\n"^
            "MAKE_CLOSURE(rax, rbx, "  ^ code_L ^ ")\n"^
            "jmp " ^ cont_L ^ "\n" ^
            code_L ^ ":\n" ^
            "push rbp\n" ^
            "mov rbp, rsp\n" ^
            expr_to_string consts fvars body (depth + 1) ^
            "leave\n" ^
            "ret\n" ^
            cont_L ^ ":\n"

    | ScmLambdaOpt'(args, arg, body) ->
            let number= the_next_one () in
            let cont_L = "Lcont" ^ (string_of_int number) in
            let code_L = "Lcode" ^ (string_of_int number) in
            let number_of_args = (string_of_int ((List.length args) + 1)) in
            "MAKE_EXT_ENV " ^ (string_of_int depth) ^
            "\nmov rbx, rax\n"^
            "MAKE_CLOSURE(rax, rbx, "  ^ code_L ^ ")\n"^
            "jmp " ^ cont_L ^ "\n" ^
            code_L ^ ":\n" ^
            "FIX_STACK_LAMBDA_OPT " ^ number_of_args ^"\n" ^
            "push rbp\n" ^
            "mov rbp, rsp\n" ^
            expr_to_string consts fvars body (depth + 1) ^
            "leave\n" ^
            "ret\n" ^
            cont_L ^ ":\n"

     | ScmOr'(list_of_subtrees) ->
          let the_exit_L = "Lexit" ^ (string_of_int (the_next_one ()))  in
          (List.fold_left (fun acc x -> acc ^ (expr_to_string consts fvars x depth)  ^"cmp rax, SOB_FALSE_ADDRESS\njne " ^ the_exit_L ^ "\n" ) "" list_of_subtrees) ^ the_exit_L ^":\n"

     | ScmSet'(VarBound(_,major,minor), value_for_var) ->
             (expr_to_string consts fvars value_for_var depth) ^
              "mov rbx, qword [rbp + 8 * 2]\nmov rbx, qword [rbx + 8 *"^(string_of_int major)^
              "]\nmov qword [rbx + 8 *" ^ (string_of_int minor) ^
              "], rax\nmov rax, SOB_VOID_ADDRESS\n"

     | ScmSet'(VarFree(var),value_for_var) ->
          (expr_to_string consts fvars value_for_var depth) ^
          "mov qword [fvar_tbl+" ^ (find_offset_from_fvars var fvars) ^
          "],rax\nmov rax,SOB_VOID_ADDRESS\n"

     | ScmSet'(VarParam(_, minor), value_for_var) ->
          (expr_to_string consts fvars value_for_var depth) ^
          "mov qword [rbp + 8*(4+" ^ (string_of_int minor) ^
           ")], rax\nmov rax, SOB_VOID_ADDRESS\n"

     | ScmSeq'(seq) ->
            String.concat "" (List.map (fun expr -> expr_to_string consts fvars expr depth) seq)

    | ScmDef'(VarFree(name), value_for_var) ->
            expr_to_string consts fvars value_for_var depth ^
            "mov qword[fvar_tbl+" ^ (find_offset_from_fvars name fvars) ^"], rax\n" ^
            "mov rax, SOB_VOID_ADDRESS\n"

    | ScmApplic'(body,args) ->
        let insert_code = List.fold_right (fun arg acc-> acc ^ (expr_to_string consts fvars arg depth) ^ "push rax\n")  args "" in
        insert_code ^
        "push " ^ (string_of_int (List.length args)) ^ "\n" ^
        (expr_to_string consts fvars body depth) ^
        "CLOSURE_ENV rbx, rax\n" ^
        "push rbx\n" ^
        "CLOSURE_CODE rbx, rax\n" ^
        "call rbx\n" ^
        "add rsp,8*1 ;pop env\n" ^
        "pop rbx     ;pop arg count\n" ^
        "shl rbx,3   ;rbx = rbx*8\n" ^
        "add rsp,rbx ;pop args\n"

    | ScmApplicTP'(body,args) ->
        List.fold_right (fun arg acc-> acc ^ (expr_to_string consts fvars arg depth) ^ "push rax\n")  args "" ^
        "push " ^ string_of_int (List.length args) ^ "\n" ^
        (expr_to_string consts fvars body depth) ^
        "CLOSURE_ENV rbx, rax\n" ^
        "push rbx\n" ^
        "push qword[rbp + 8 * 1] ;old ret addr\n" ^
        "FIX_STACK_APPLICTP " ^ (string_of_int (3 + (List.length args))) ^ "\n" ^
        "CLOSURE_CODE rbx, rax\n" ^
        "jmp rbx\n"


    | ScmBoxSet'(var,value_for_var) ->
        expr_to_string consts fvars value_for_var depth ^
        "push rax\n" ^
        expr_to_string consts fvars (ScmVar'(var)) depth ^
        "push rax\n" ^
        "push 2\n" ^
        "push SOB_NIL_ADDRESS\n" ^
        "call set_car\n" ^
        "add rsp, 8              ;pop env\n" ^
        "pop rbx                 ;pop argc\n\n" ^
        "shl rbx, 3              ;rbx=rbx*8\n" ^
        "add rsp, rbx            ;pop args\n" ^
        "mov rax,SOB_VOID_ADDRESS\n"


    | ScmConst'(c) ->
        "mov rax,const_tbl+" ^ (find_offset c consts) ^ "\n"

    | ScmVar'(VarParam(_,minor)) ->
        "mov rax, qword[rbp + 8*(4+" ^ (string_of_int minor) ^ ")]\n"

    | ScmVar'(VarBound(_,major,minor)) ->
         "mov rax, qword[rbp + 8*2]\nmov rax, qword[rax + 8 * " ^
         (string_of_int major) ^ "]\nmov rax, qword[rax + 8 * " ^
         (string_of_int minor) ^ "]\n"

    | ScmVar'(VarFree(name)) ->
        "mov rax, qword[fvar_tbl+" ^
         (find_offset_from_fvars name fvars) ^
         "]\n"

    | ScmBox'(VarParam(_,minor)) ->
        "mov rax, qword[rbp + 8 * (4 + " ^ (string_of_int minor) ^ ")]\n" ^
        "push SOB_NIL_ADDRESS ; something for the cdr\n" ^
        "push rax             ; car\n" ^
        "push 2               ; argc\n" ^
        "push SOB_NIL_ADDRESS ;fake env\n" ^
        "call cons\n" ^
        "add rsp,8*1          ;pop env\n" ^
        "pop rbx              ;pop argc\n" ^
        "shl rbx,3            ;rbx=rbx*8\n" ^
        "add rsp,rbx          ;pop args\n" ^
        "mov qword[rbp + 8 * (4 + " ^ (string_of_int minor) ^ ")],rax\n"

    | ScmBoxGet'(var) ->
        expr_to_string consts fvars (ScmVar'(var)) depth ^
        "push rax\n"   ^
        "push 1                 ;push argc\n" ^
        "push SOB_NIL_ADDRESS   ;fake env\n" ^
        "call car\n"   ^
        "add rsp,8*1            ;pop env\n" ^
        "pop rbx                ;pop argc\n"  ^
        "shl rbx,3              ;rbx=rbx*8 \n" ^
        "add rsp, rbx           ;pop args\n"


    | x -> raise X_this_should_not_happen


      let primitives =
        [
          (* Type queries  *)
          "boolean?"; "flonum?"; "rational?";
          "pair?"; "null?"; "char?"; "string?";
          "procedure?"; "symbol?";
          (* String procedures *)
          "string-length"; "string-ref"; "string-set!";
          "make-string"; "symbol->string";
          (* Type conversions *)
          "char->integer"; "integer->char"; "exact->inexact";
          (* Identity test *)
          "eq?";
          (* Arithmetic ops *)
          "+"; "*"; "/"; "="; "<";
          (* Additional rational numebr ops *)
          "numerator"; "denominator"; "gcd";
          (* you can add yours here *)
          "apply" ; "car" ; "cdr" ; "cons" ; "set-car!" ; "set-cdr!"
        ]


module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts =
    let list_of_sexps = List.fold_left (fun acc ast -> (acc @ (get_the_sexps ast))) [] asts in
    let list_of_sexps = expand_the_sexprs (eliminate_the_dups list_of_sexps)  in
    let list_of_sexps =  ([ScmVoid; (ScmNil) ; (ScmBoolean(true)) ; (ScmBoolean(false))] @ list_of_sexps) in
    let list_of_sexps = eliminate_the_dups list_of_sexps  in
    build_const_tbl list_of_sexps [] 0 ;;


  let make_fvars_tbl asts =
    let list_of_free_vars = ((List.fold_left (fun acc ast -> (acc @ (select_free_vars ast))) [] asts) @ primitives) in
    let list_of_free_vars = eliminate_the_dups list_of_free_vars in
    build_fvars_tbl list_of_free_vars 0;;

  let generate consts fvars e = expr_to_string consts fvars e 0;;
end;;



