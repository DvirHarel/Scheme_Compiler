(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
    val nt_integer_part : int PC.parser
    val nt_int : int PC.parser
    val nt_frac : scm_number PC.parser
    val nt_float1 : float PC.parser
    val nt_float2 : float PC.parser
    val nt_float3 : float PC.parser
    val nt_float : scm_number PC.parser
    val nt_number : sexpr PC.parser
    val nt_boolean: sexpr PC.parser
    val nt_char_hex : char PC.parser
    val nt_char : sexpr PC.parser
    val nt_quoted_forms : sexpr PC.parser
    val nt_properList : sexpr PC.parser
    val nt_improperList : sexpr PC.parser
    val nt_string_interpolated : sexpr PC.parser
    val nt_string : sexpr PC.parser


end;; (* end of READER signature *)

module Reader : READER = struct
open PC;;

let unitify nt = pack nt (fun _ -> ());;
let rec list_to_proper_list = function
  | [] -> ScmNil
  | hd::[] -> ScmPair (hd, ScmNil)
  | hd::tl -> ScmPair (hd, list_to_proper_list tl);;
let rec list_to_improper_list = function
    | [] -> raise X_no_match
    | hd::[] -> hd
    | hd::tl -> ScmPair (hd, list_to_improper_list tl);;
let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str
and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str



and nt_line_comment str =
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end_of_line_or_file in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end_of_line_or_file) in
  let nt1 = unitify nt1 in
  nt1 str


and nt_paired_comment str =
    let nt1 = char '{' in
    let nt2 = disj_list[unitify nt_char; unitify nt_string; unitify nt_comment] in
    let nt2' = disj nt2 (unitify (one_of"{}")) in
    let nt3 = diff nt_any nt2' in
    let nt3 = disj (unitify nt3) nt2 in
    let nt3 = star nt3 in
    let nt4 = char '}' in
    let nt1 = unitify (caten nt1 (caten nt3 nt4)) in
    nt1 str


and nt_sexpr_comment str =
  let pref = (word "#;") in
  let comment = (caten pref nt_sexpr) in
  let nt1 = pack comment (fun _ -> ScmNil) in
  let nt1 = unitify nt1 in
  nt1 str


and nt_comment str =
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment] str
and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str
and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1




and nt_int str =
    let minus = char '-' in
    let plus = char '+' in
    let pack_integer = pack (caten (maybe (disj plus minus)) nt_integer_part) (fun (sign, num) ->match sign with
                                                                                                    |Some('-') -> -1*num
                                                                                                    | _ -> (num)) in
    pack_integer str

and nt_frac str =
    let slash= word "/" in
    let nt0= pack (plus (char '0')) (fun list-> (int_of_string (list_to_string list))) in
    let nt1= diff nt_int nt0 in
    let nt2= caten nt_int (caten slash nt1) in
    let nt3= pack nt2 (fun (x,(y,z))-> ScmRational(x/(gcd x z),z/(gcd x z))) in
    nt3 str

and nt_integer_part str =
    let _digits_parse = plus (range '0' '9') in
    let nt7 = pack _digits_parse (fun (ds) ->  (int_of_string (list_to_string ds))) in
    nt7 str


and nt_mantissa str =
    let nt = pack nt_integer_part (fun n ->
                            let s : string = "0."^(string_of_int n) in
                            float_of_string s) in
    nt str


and nt_exponent str =
    let nt1 = word_ci "e" in
    let nt2 = word "*10^" in
    let nt3 = word "10*" in
    let nt4 = disj_list [nt1; nt2;  nt3] in
    let nt_expo = pack (nt4) (fun _ -> 0) in
    let pack_exponent = pack (caten nt_expo nt_int)
                                (fun (exp,num)->
                                    ( 10. ** (float_of_int (num)))) in
    pack_exponent str

and nt_float1 str=
    let dot= word "." in
    let dot= pack (dot) (fun _ -> 0.) in
    let nt_to_float= pack nt_int (fun num -> float_of_int num) in
    let nt_nantissa= pack (maybe nt_mantissa) (fun num -> if ((Option.is_some num)) then ((Option.get num)) else 0.) in
    let nt_exponent= pack (maybe nt_exponent) (fun num -> if ((Option.is_some num)) then ((Option.get num)) else 1. ) in
    let packer_maker= pack (caten nt_to_float(caten dot (caten nt_nantissa nt_exponent))) (fun (a,(b,(c,d)))-> (((a+.c)*.d))) in
    packer_maker str

and nt_float2 str=
    let dot= word "." in
    let dot= pack (dot) (fun _ -> 0.) in
    let nt1 = pack (caten dot (caten nt_mantissa nt_exponent )) (fun (a,(b,c))  -> b*.c) in
    nt1 str

and nt_float3 str=
    let nt1 = pack (caten nt_int nt_exponent ) (fun (a, b)->(float_of_int a) *. b ) in
    nt1 str

and nt_float str =
    let plus = char '+' in
    let minus = char '-' in
    let nt1 = pack (caten (maybe (disj plus minus)) (disj_list [nt_float1;nt_float2; nt_float3;])) (fun (sign, num) ->
    match sign with
        | Some('-') -> ScmReal(num *. -1.)
        | _ -> ScmReal(num)) in
    nt1 str

and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str

and nt_boolean str=
    let nt1 = word_ci "#t" in
    let nt2 = word_ci "#f" in
    let nt1 = pack nt1 (fun z->ScmBoolean true) in
    let nt2 = pack nt2 (fun z->ScmBoolean false) in
    let nt1 = disj nt1 nt2 in
    nt1 str

and nt_char_simple str =
    let nt1= range '!' '~' in
    let nt2 = pack nt1 (fun b ->  ScmChar b ) in
    nt2 str

and make_named_char char_name ch =
    let nt1=word char_name in
    pack nt1 (fun _-> ch)

and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str
 and value_of_hex_char ch=
    if(((int_of_char ch )-(int_of_char '0') >=0) && ((int_of_char ch ) - (int_of_char '0')<=9))
        then ((int_of_char ch )- (int_of_char '0'))
        else ((int_of_char ch )- (int_of_char 'a')+10)

and nt_char_hex str=
    let hex = char 'x' in
    let range1 = range '0' '9' in
    let range2 = range 'a' 'f' in
    let range3  = range 'A' 'F' in
    let rangeOfall = disj_list[range1;range2;range3] in
    let plus_range = plus rangeOfall in
    let pack_char_hex = pack (caten hex plus_range) (fun (x, hex_part) -> (
    let num = List.fold_left (fun acc ch->acc*16+value_of_hex_char ch) 0 hex_part in
    if ((num>32) &&  (num<126)) then ((char_of_int num))
        else (raise X_no_match))) in
        pack_char_hex str

and nt_symbol_char str =
    let nt1=range 'a' 'z' in
    let nt2=range 'A' 'Z' in
    let nt3=range '/' ':' in
    let nt4=range '<' '?' in
    let nt5=range '^' '_' in
    let nt6 = char_ci '!' in
    let nt7 = char_ci '$' in
    let nt8 = char_ci '+' in
    let nt9 = char_ci '-' in
    let nt10 = char_ci '*' in
    let nt1 = disj_list[ nt1;nt2; nt3; nt4; nt5; nt6 ; nt7; nt8; nt9; nt10]  in
    nt1 str

and nt_char str =
    let sulamit = char '#' in
    let slesh = char '\\' in
    let prefix = pack (caten sulamit slesh) (fun (n1,n2) -> ' ') in
    let pack_char =  disj_list [ nt_char_hex ; nt_char_named; nt_symbol_char ]in
    let just_char = pack (caten prefix pack_char) (fun (ch1, ch2) -> ch2) in
    let ans = pack just_char (fun x -> ScmChar (x)) in
    ans str


and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str


and nt_string_literal_char str=
    let nt1= only_if nt_any (fun (x) -> if (int_of_char x=int_of_char '/' || int_of_char x=int_of_char '"'  || int_of_char x=int_of_char '~' )  then false else true) in
    nt1 str


and nt_string_metachar str=
    let nt3 = word "~~" in
    let nt4 = word "\\n" in
    let nt4 = pack nt4 (fun x -> ['\n'] ) in
    let nt5 = word "\\r" in
    let nt5 = pack nt5 (fun x -> ['\r'] ) in
    let nt6 = word "\\f" in
    let nt6 = pack nt6 (fun x -> ['\012'] ) in
    let nt7 = word "\\t" in
    let nt7 = pack nt7 (fun x -> ['\t'] ) in
    let ntAll= disj_list[ nt3; nt4; nt5; nt6; nt7] in
    ntAll str

and nt_string_hex_char str=
    let slash = char '\\' in
    let prefix = caten slash (caten nt_char_hex (char ';')) in
    let nt_final = pack prefix (fun (x, (y,z)) -> y) in
    nt_final str

and nt_string_interpolated str=
    let nt1 = char '\"' in
    let prefix= word "~{" in
    let suffix= word "}" in
    let ntall= caten nt1 (caten prefix (caten nt_sexpr (caten suffix nt1))) in
    let just_sexpr = pack ntall (fun (a,(b,(c,(d,e))))->c) in
    let magic_list = pack just_sexpr (fun x->[ScmSymbol "format" ; ScmString "~a" ;x]) in
    let nt1 = pack magic_list (fun x->list_to_proper_list x) in
    nt1 str

and nt_string_one str=
    let nt1 = pack nt_string_metachar (fun x ->list_to_string x) in
    let nt2 =  pack nt_string_hex_char (fun x ->Printf.sprintf "%c" x) in
    let nt3 =  pack nt_string_literal_char (fun x ->Printf.sprintf "%c" x) in
    let ntall = disj_list [nt2;nt1;nt3;] in
    ntall str

and nt_string_without_inter str =
    let nt1 = char '\"' in
    let nt2 = star nt_string_one in
    let nt2 = pack nt2 (fun x ->List.map (fun a -> String.get a 0) x  ) in
    let nt3 = caten nt1 (caten nt2 nt1) in
    let nt3 =  pack nt3 (fun (a, ( b ,c) ) -> b ) in
    let nt4 =  pack nt3 (fun b -> ScmString( (list_to_string b))) in

    nt4 str

and nt_string str =

    let nt1  = disj_list [nt_string_without_inter; nt_string_interpolated;] in
    nt1 str


and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str


and nt_properList str =
    let nt1 = pack  (word "(") (fun x ->[ScmBoolean (false)]) in
    let nt2 = pack  (word ")") (fun x -> [ScmBoolean (false)]) in
    let nt3 = caten nt1 (caten (star nt_sexpr) nt2) in
    let nt_sexprs = pack nt3 (fun (a,(b,c))-> b) in
    let nt_final = pack nt_sexprs (fun a -> (list_to_proper_list a)) in
    nt_final str

and nt_improperList str =
    let nt1 = pack (word "(") (fun x ->[ScmBoolean (false)]) in
    let nt2 = pack (word ")") (fun x -> [ScmBoolean (false)]) in
    let dot = pack (word ".") (fun x -> [ScmBoolean (false)]) in
    let nt_almost_all = pack (caten nt1 (plus nt_sexpr)) (fun (x,y)->y) in
    let nt_last = pack (caten dot (caten nt_sexpr nt2)) (fun (x,(y,z)) -> y) in
    let nt_all = caten nt_almost_all nt_last in
    let list_of_all = pack nt_all (fun (x, y) -> x @ [y] ) in
    let final =pack list_of_all (fun x->list_to_improper_list x) in
    final str


 and nt_list str =
     let nt1 = caten (word "(") (caten (plus (word " ")) (word ")")) in
     let nt1 = pack nt1 (fun x -> ScmNil) in
     let nt_final = disj_list [nt1; nt_properList; nt_improperList] in
     nt_final str


and nt_quoted_forms str =
    let quoted = pack (word "'") (fun x ->ScmSymbol ("quote")) in
    let quasiQuoted = pack (word "`") (fun x ->ScmSymbol ("quasiquote")) in
    let unquoted = pack (word ",") (fun x ->ScmSymbol ("unquote")) in
    let unquoteAndSpliced = pack (word ",@") (fun x ->ScmSymbol ("unquote-splicing")) in
    let nt1 = disj_list [quoted;quasiQuoted;unquoteAndSpliced; unquoted] in
    let nt1 = caten nt1 nt_sexpr in
    let nt1 = pack nt1 (fun (x,y) ->ScmPair ( x,ScmPair (y,ScmNil)) ) in
    nt1 str

and nt_sexpr str =
  let nt1 =
    disj_list [nt_boolean;nt_number; nt_symbol; nt_char; nt_quoted_forms; nt_list;
               nt_string; nt_vector; ] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;