(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;

exception X_debug of expr';;

let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct
(*ref Start*)
let num_of_clousers = ref 0

let boxed_vars = ref []

let read_vars =  ref []

let set_vars =   ref []
(*ref End*)

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env =
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

 let name_of_scm_var scm_var =
    match scm_var with
       | ScmVar'(VarFree name) -> name
       | ScmVar'(VarParam (name,_)) -> name
       | ScmVar'(VarBound (name,_,_)) -> name
       | _ -> raise X_this_should_not_happen

let scmVar_to_name_var scm_var= name_of_scm_var(ScmVar'(scm_var))


  (* run this first! *)
  let annotate_lexical_addresses pe =
   let rec run pe params env =
   match pe with
    |ScmConst(sexpr) -> ScmConst'(sexpr)
    |ScmVar(name) -> ScmVar'(tag_lexical_address_for_var name params env)
    |ScmIf(test,dit,dif) -> ScmIf'(run test params env , run dit params env ,run dif params env)
    |ScmOr (list_of_subtrees) -> ScmOr'(List.map (fun v -> run v params env ) list_of_subtrees)
    |ScmLambdaSimple(args ,body) -> ScmLambdaSimple' (args, run  body args ([params] @ env))
    |ScmLambdaOpt(args,arg ,body) -> ScmLambdaOpt'(args,arg, run body (args @ [arg]) ([params] @ env))
    |ScmDef(ScmVar(var) ,value_for_var) -> ScmDef'(tag_lexical_address_for_var var params env ,run value_for_var params env)
    |ScmSet(ScmVar(var) ,value_for_var) -> ScmSet'((tag_lexical_address_for_var var params env) ,(run value_for_var params env))
    |ScmApplic(sub_exp1 ,sub_exps) -> ScmApplic'(run sub_exp1 params env ,(List.map (fun v -> run v params env ) sub_exps))
    |ScmSeq(seq) -> ScmSeq'(List.map (fun v -> run v params env ) seq)
    |_ -> raise X_this_should_not_happen
   in
   run pe [] [];;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;

  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail =
    match pe with
     |ScmConst'(_) -> pe
     |ScmVar'(_) -> pe
     |ScmIf'(test, dit,dif) ->ScmIf'(run test false , run dit in_tail, run dif in_tail)
     |ScmOr'(list_of_subtrees) -> ScmOr'(annotate_tail_calls_for_list list_of_subtrees in_tail)
     |ScmLambdaSimple'(args,body) -> ScmLambdaSimple'(args, run body true)
     |ScmLambdaOpt'(args,arg,body) -> ScmLambdaOpt'(args,arg, run body true)
     |ScmDef'(var,value_for_var) -> ScmDef'(var, run value_for_var false)
     |ScmSet'(var,value_for_var)-> ScmSet'(var, run value_for_var false)
     |ScmApplic'(sub_exp1 , sub_exps) -> if(in_tail = false) then
                                                 ScmApplic'(run sub_exp1 false  ,List.map (fun x -> run x false ) sub_exps)
                                         else
                                               ScmApplicTP'(run sub_exp1 false  ,List.map (fun x -> run x false ) sub_exps)
     |ScmSeq'(list)-> ScmSeq'(annotate_tail_calls_for_list list in_tail)
    | _ -> raise X_this_should_not_happen
   and
    annotate_tail_calls_for_list list in_tail =
     match list with
      | [] -> []
      | [hd] -> [run hd in_tail]
      | first::rest ->  run first false :: (annotate_tail_calls_for_list rest in_tail) in
   run pe false;;

  (* boxing *)

        let rec make_Box name expr =
           match expr with
                | ScmVar'(VarParam(v, minor)) ->  if(String.equal v name) then ScmBoxGet'(VarParam(v, minor)) else (expr)
                | ScmVar'(VarBound(v, major, minor)) ->  if(String.equal v name ) then  ScmBoxGet'(VarBound(v, major, minor)) else (expr)
                | ScmIf'(test , dit , dif) -> ScmIf'(make_Box name test, make_Box name dit, make_Box name dif)
                | ScmOr'(list_of_subtrees) -> ScmOr'(List.map (fun (z) -> make_Box name z) list_of_subtrees)
                | ScmLambdaSimple'(args , body) -> if(List.mem name args) then ScmLambdaSimple'(args , body) else ScmLambdaSimple'(args , make_Box name body)
                | ScmLambdaOpt'(args , arg , body) -> if(List.mem name (args @[arg])) then ScmLambdaOpt'(args , arg , body) else ScmLambdaOpt'(args , arg , make_Box name body)
                | ScmSet'(VarBound(v ,minor,major),value_for_var) ->if(String.equal v name ) then ScmBoxSet'(VarBound(v ,minor,major) , make_Box name value_for_var) else ScmSet'(VarBound(v, minor, major) ,make_Box name value_for_var)
                | ScmSet'(VarParam(v ,minor) , value_for_var) -> if(String.equal v name ) then ScmBoxSet'(VarParam(v ,minor) , make_Box name value_for_var ) else ScmSet'(VarParam(v, minor), make_Box name value_for_var)
                | ScmApplic'(sub_exp1, sub_exps) -> ScmApplic'((make_Box name sub_exp1),(List.map (fun (z) ->make_Box name z) sub_exps))
                | ScmApplicTP'(sub_exp1, sub_exps) -> ScmApplicTP'( (make_Box name  sub_exp1 ),(List.map (fun (z) -> make_Box name z) sub_exps))
                | ScmSeq'(seq) -> ScmSeq'(List.map (fun (z) -> make_Box name z ) seq)
                | _ -> expr;;


       let rec find_write name closure expr   =
         match expr with
            | ScmIf'(test , dit , dif) -> (find_write name closure test) @( find_write name closure dit) @( find_write name closure dif)
            | ScmOr'(list_of_subtrees) -> (List.fold_left (fun x y -> x @ y) [] (List.map (fun (z)-> find_write name  closure z) list_of_subtrees ))
            | ScmSet'(VarBound(v,minor,major) , value_for_var) -> if(String.equal v name ) then  ([[closure]] @  find_write name closure value_for_var ) else ([[]])
            | ScmSet'(VarParam(v,minor) , value_for_var) ->  if(String.equal v name ) then  [[closure]] @  find_write name closure value_for_var  else ([[]])
            | ScmApplic'(sub_exp1, sub_exps) -> List.fold_left(fun x y -> x @ y) (find_write name closure sub_exp1) (List.map (fun (z)-> find_write name  closure z) sub_exps)
            | ScmApplicTP'(sub_exp1, sub_exps) -> (List.fold_left (fun x y -> x @ y) (find_write name closure sub_exp1)(List.map (fun (z)-> find_write name  closure z) sub_exps ))
            | ScmSeq'(seq) -> (List.fold_left (fun x y -> x @ y) [] (List.map (fun (z)-> find_write name  closure z) seq ))
            | ScmLambdaSimple'(args , body) -> if(List.mem name args) then [[]] else (List.map (fun z-> [closure]@z) (List.filter (fun z -> z!=[]) (find_write name expr body)))
            | ScmLambdaOpt'(args , arg , body) ->if(List.mem name (args @ [arg])) then [[]] else ((List.map (fun z-> [closure]@z) (List.filter (fun z -> z!=[]) (find_write name expr body))))
            | _ -> [[]]



     let rec find_reads name closure expr   =
       match expr with
        | ScmVar'(VarParam(v, minor)) -> if(String.equal v name ) then [[closure]] else ([[]])
        | ScmVar'(VarBound(v, major, minor)) -> if(String.equal v name ) then [[closure]]  else([[]])
        | ScmSet'(var_ , value_for_var) -> (find_reads name closure value_for_var)
        | ScmApplic'(sub_exp1, sub_exps) ->List.fold_left (fun x y -> x @ y) (find_reads name closure sub_exp1) (List.map (fun (x)-> find_reads name  closure x) sub_exps)
        | ScmSeq'(seq) -> List.fold_left (fun x y -> x @ y) [] (List.map (fun (x)-> find_reads name  closure x) seq )
        | ScmApplicTP'(sub_exp1, sub_exps) -> (List.fold_left (fun x y -> x @ y) (find_reads name closure sub_exp1) (List.map (fun (x)-> find_reads name  closure x) sub_exps))
        | ScmIf'(test,dit,dif) -> (find_reads name closure test) @( find_reads name closure dit) @ (find_reads name closure dif)
        | ScmOr'(list_of_subtrees) ->  List.fold_left (fun x y -> x @ y) [] (List.map (fun (x)-> find_reads name  closure x) list_of_subtrees)
        | ScmLambdaSimple'(args , body) ->if(List.mem name args) then [[]] else (List.map (fun x-> [closure]@x) (List.filter (fun x -> x!=[]) (find_reads name expr body)))
        | ScmLambdaOpt'(args , arg , body) ->if(List.mem name (args @ [arg])) then [[]]  else  (List.map (fun x-> [closure]@x) (List.filter (fun x -> x!=[]) (find_reads name expr body)))
        | _ -> [[]]


 let rec search x lst index =
     match lst with
     | [] -> -1
     | h :: t ->
       if x = h then index else (search x t (index + 1))

   let need_to_be_boxed name reads writes_ lam =
     if ((List.filter (fun x-> x!=[]) reads) ==[] || (List.filter (fun x-> x!=[]) writes_) == [])
        then (false)
        else(
            let a b c =List.concat (List.map (fun d -> List.map (fun e' -> (d,e')) c) b) in
            let read = List.map(fun x -> match x with | (e::r) -> r | _-> []) (List.filter (fun x-> x!= []) reads) in
            let write = List.map(fun x -> match x with | (e::r) -> r | _-> []) (List.filter (fun x-> x!= []) writes_) in
            let pair = a read write in
            let equal_pair (b , c) =
               if ((b == [] && c != []) || (b!=[] && c==[]) )
                then (true)
                else( b!=[]&&c!=[]&&(List.hd b)!= (List.hd c)) in
               ormap equal_pair pair);;


     let get_it matching minor var =
         (match matching with
          | ScmSeq'(exprlist) -> ScmSeq'([ScmSet'(VarParam(var, minor), ScmBox'(VarParam(var,minor)))] @ exprlist)
          | any->ScmSeq'([ScmSet'(VarParam(var, minor), ScmBox'(VarParam(var,minor)))] @ [any]))

   let rec box_set expr =
     match expr with
       | ScmIf'(test , dit , dif) -> ScmIf'(box_set test  , box_set dit  , box_set dif )
       | ScmSeq'(seq) -> ScmSeq'(List.map (fun (x)-> box_set x ) seq)
       | ScmDef'(var , value_for_var) -> ScmDef'(var, box_set value_for_var)
       | ScmOr'(list_of_subtrees) -> ScmOr'(List.map (fun (x)-> box_set x ) list_of_subtrees)
       | ScmApplic'(sub_exp1 , sub_exps) -> ScmApplic'(box_set sub_exp1 , (List.map (fun (x)-> box_set x ) sub_exps))
       | ScmApplicTP'(sub_exp1 , sub_exps) -> ScmApplicTP'(box_set sub_exp1, List.map (fun (x)-> box_set x ) sub_exps)
       | ScmLambdaSimple'(args , body) ->
          let rec box_lambda vars exp =
           (match vars with
           | var::rest -> if ((need_to_be_boxed var (find_reads var expr body) (find_write var expr body) expr))
                            then(get_it (make_Box var (box_lambda rest exp)) (search var args 0) var)
                            else  (box_lambda rest exp)
           | [] -> exp)
          in ScmLambdaSimple'(args, box_set(box_lambda args body))

       | ScmLambdaOpt'(args , arg , body) ->
           let rec box_lambda vars exp=
             (match vars with
             | var::rest ->
               if ((need_to_be_boxed var (find_reads var expr body) (find_write var expr body) expr))
                    then (get_it (make_Box var (box_lambda rest exp)) (search var (args @ [arg]) 0) var)
                    else (box_lambda rest exp)
             | []->exp)
           in ScmLambdaOpt'(args, arg, box_set (box_lambda (args @ [arg]) body))
       | _ -> expr
       ;;

   let run_semantics expr =
     box_set
      (annotate_tail_calls
          (annotate_lexical_addresses expr))

 end;; (* end of module Semantic_Analysis *)


