(* This program is translated from the MINICAML included in the Caml-light
   ver. 0.71 package and wrritten in Standard ML/NJ syntax.
   Originall copyright as follows:

------------- 
Software: Caml Light, version 0.71 of January 1996, hereinafter
referred to as "the software".

The software has been designed and produced by Xavier Leroy,
Damien Doligez, Francois Rouaix, Jerome Vouillon and Pierre Weis,
research workers for the Institut National de Recherche en Informatique et
en Automatique (INRIA) - Domaine de Voluceau - Rocquencourt - 78153 Le
Chesnay Cedex - France.

INRIA holds all ownership rights to Caml Light version 0.7.

The software has been registered at Agence pour la Protection
des Programmes (APP).

Preamble:

The software is currently being developed and INRIA desires
that it be used by the scientific community so as to test, evaluate
and develop it.  To this end, INRIA has decided to have a prototype of
the software distributed by FTP.

a- Extent of the rights granted by the INRIA to the user of the software:

INRIA freely grants the right to use, modify and integrate the
software in another software, provided that all derivative works are
distributed under the same conditions as the software.

b- Reproduction of the software:

INRIA grants any user of the software the right to reproduce it so as
to circulate it in accordance with the same purposes and conditions as
those defined at point a- above.  Any copy of the software and/or relevant
documentation must comprise reference to the ownership of INRIA and
the present file.

The user undertakes not to carry out any paying distribution of the
software. However, he is authorized to bill any person or body for the
cost of reproduction of said software. As regards any other type of
distribution, the user undertakes to apply to obtain the express
approval of INRIA.
--------------------------------------
and
--------------------------------------
All other files included in the Caml Light distribution or generated
by the Caml Light system are subject to the conditions in points a-
and b- above.
-------------------------------------

And my copyright is:

Copyright(c) 1996 by Yasushi KODAMA
and this program is subject to above conditions, then feel free to modify
and integrate this program. If you have any comments or find bugs,
please let me know. 

You can execute some examples as follows:
<< factorial >>
## let rec fac =function 0->1|x->((fac (x-1))*x);
fac : (int -> int) = <fun>
## fac 0;
- : int = 1
## fac 5;
- : int = 120
## fac 10;
- : int = 3628800
## fac 12;
- : int = 479001600

Originally, on the MINICAML included in caml-right packages, double
semicolons `;;' are used by the delimitter as the end of a line,
but on this system, single semicolon is used for this purpose.

August 1996
Thanks,
yas@is.noda.sut.ac.jp *)

datatype rword = TRUE | FALSE | LET | IN | FUNCTION | REC | NE | LE
	 |	 GE | CONS | ARROW | MATCH | WITH
datatype lexis = Reserved of rword
         |       Identifier of string
         |       Num of int
	 |       One of string;
datatype definition = Def of (bool*string*expr)
	 |            Expr of expr
and expr =  Number of int
         |  Variable of string
         |  Boolean of bool
         |  Let of definition*expr
	 |  Function of (motif*expr) list
	 |  Application of expr*expr
	 |  Pair of expr*expr
	 |  Cons of expr*expr
	 |  Unit
	 |  Nil
         |  Misc
and motif = Motif_variable of string
	 |  Motif_boolean of bool
	 |  Motif_number of int
	 |  Motif_pair of motif*motif
	 |  Motif_nil
	 |  Motif_cons of motif*motif
	 |  Motif_unit
	 |  Motif_arrow;
datatype value = Val_number of int
	 |  Val_bool of bool
         |  Val_pair of value * value
         |  Val_nil
         |  Val_cons of value * value
         |  Val_closure of closure
         |  Val_primitive of value -> value
         |  Val_string of string
         |  Val_unit
withtype environment = (string * value) list
and closure = { Definition: (motif*expr) list, 
		Environment: (environment ref) };
datatype simple_type =
    VarType of variable_of_type
|   Term of string * (simple_type list)
and value_of_an_variable =
    Unknown
|   Known of simple_type
withtype variable_of_type = { Index: int,
			      Value: value_of_an_variable } ref;
type types_schema = { Parameters: variable_of_type list,
		      Bodys: simple_type };
exception Syntax_error;
exception End_of_system;
exception Quit_system;
exception Cant_close_parenthesis;
exception Type_Error of string;
exception Eval_Error of string;
exception Not_found;
exception Fail_filtrate;
exception Circulation of simple_type * simple_type;
exception Conflict of simple_type * simple_type;
fun mem x (front::rest) = if x = front then true else mem x rest
|   mem x [] = false;
fun digit c = ("0" <= c andalso c <= "9");
fun small_alpha c = ("a" <= c andalso c <= "z");
fun large_alpha c = ("A" <= c andalso c <= "Z");
fun integer ISTREAM i =
    if digit (lookahead ISTREAM) then
	integer ISTREAM (10*i+ord(input(ISTREAM,1))-ord("0"))
    else i
and identifier ISTREAM id =
    let val c = lookahead ISTREAM in
        if (small_alpha c) orelse (large_alpha c) orelse (digit c)
	    orelse c = "_" then
	    identifier ISTREAM (id^(input(ISTREAM,1)))
        else id
    end
and operator c = mem c ["<",">",":","-"]
and token ISTREAM =
    let val c = native_token ISTREAM in
	case c of
	    One(" ") => token ISTREAM
	|   One("\t") => token ISTREAM
	|   One("\n") => token ISTREAM
	|   _ => c
    end
and native_token ISTREAM =
    let val c = lookahead ISTREAM in
        if (small_alpha c) orelse (large_alpha c) then
	    let val id = identifier ISTREAM "" in
    		case id of 
		    "true" => Reserved(TRUE)
                |   "false" => Reserved(FALSE)
	    	|   "let" => Reserved(LET)
		|   "in" => Reserved(IN)
		|   "function" => Reserved(FUNCTION)
		|   "rec" => Reserved(REC)
		|   "match" => Reserved(MATCH)
		|   "with" => Reserved(WITH)
            	|   _ => Identifier(id)
	    end
        else if digit c then
            Num(integer ISTREAM 0)
        else if operator c then
	    let val oper = input(ISTREAM,1) in
		let val n = lookahead ISTREAM in
		    if oper = "<" andalso n = ">" then ( input(ISTREAM,1);
							Reserved(NE) )
                    else if oper = "<" andalso n = "=" then ( input(ISTREAM,1);
							Reserved(LE) )
		    else if oper = ">" andalso n = "=" then ( input(ISTREAM,1);
							Reserved(GE) )
		    else if oper = ":" andalso n = ":" then ( input(ISTREAM,1);
							Reserved(CONS) )
		    else if oper = "-" andalso n = ">" then ( input(ISTREAM,1);
							Reserved(ARROW) )
                    else One(oper)
		end
	    end
        else One(input(ISTREAM,1))
    end;
fun print_rword x = case x of
    TRUE => print "TRUE"
|   FALSE => print "FALSE"
|   LET => print "LET"
|   IN => print "IN"
|   FUNCTION => print "FUNCTION"
|   REC => print "REC"
|   ARROW => print "ARROW"
|   WITH => print "WITH"
and print_token x = case x of
    Identifier(i) => ( print "Identifier \""; print i; print "\"" )
|   Reserved(s) => ( print "Reserved "; print_rword s )
|   Num(n) => ( print "Num("; print n; print ")" )
|   One(one) => ( print "One("; print one; print ")" )
and print_expr x = case x of
    Variable(s) => ( print "Variable \""; print s; print "\"" )
|   Boolean(b) => ( print "Boolean "; print b )
|   Application(e1,e2) => ( print "Application ( "; print_expr e1;
			print ", "; print_expr e2; print " )" )
|   Number(i) => ( print "Number "; print i )
|   Pair(e1,e2) => ( print "Pair ( "; print_expr e1; print ", ";
			print_expr e2; print " )" )
|   Cons(e1,e2) => ( print "Cons ( "; print_expr e1; print ", ";
			print_expr e2; print " )" )
|   Function cl => ( print "Function ( "; print_case_list cl; print " )" )
|   Let(d,e) => ( print "Let ( "; print_definition d; print ", ";
		  print_expr e; print " )" )
|   Unit => ( print "Unit" )
and print_definition x = case x of
    Def(b,s,e) => ( print("Def ( "); print b; print(", "); print s;
		    print ", "; print_expr e; print " )" )
|   Expr(e) => ( print "Expr ( "; print_expr e; print " )" )
and print_case_list ((m,e)::[]) = ( print "( "; print_motif m; print ", ";
			print_expr e; print " )" )
|   print_case_list ((m,e)::rest) = ( print "( "; print_motif m; print ", ";
			print_expr e; print " ) | "; print_case_list rest )
|   print_case_list [] = ()
and print_motif x = case x of
    Motif_variable v => ( print "Motif_variable \""; print v; print "\"" )
|   Motif_boolean b => ( print "Motif_boolean "; print b )
|   Motif_number n => ( print "Motif_number "; print n )
|   Motif_pair (m1,m2) => ( print "Motif_pair ( "; print_motif m1;
			    print ", "; print_motif m2; print " )" )
|   Motif_nil => print "Motif_nil"
|   Motif_cons (m1,m2) => ( print "Motif_cons ( "; print_motif m1;
		print ", "; print_motif m2; print " )" )
|   Motif_arrow => print "Motif_arrow"
and print_list ((front:string)::rest) =
	( print(front); print(", "); print_list rest )
|   print_list [] = ()
and print_value_environment vl = (
	print "VEnv [ "; print_value_environment_c vl; print " ]" )
and print_value_environment_c ((s,v)::r) = ( print "( "; print s; print ", ";
		      print_value v; print " )"; print_value_environment_c r )
|   print_value_environment_c [] = ()
and print_motif_expr_list mel = ( print "[ "; print_motif_expr_list_c mel;
					print " ]" )
and print_motif_expr_list_c ((m,e)::[]) = ( print "( "; print_motif m;
	print ", "; print_expr e; print " )" )
|   print_motif_expr_list_c ((m,e)::r) = ( print "( "; print_motif m;
	print ", "; print_expr e; print " ) |"; print_motif_expr_list_c r )
|   print_motif_expr_list_c [] = ()
and print_motif_expr (m,e) = ( print "( "; print_motif m; print ", ";
				print_expr e; print " )" )
and print_closure (cl as { Definition=d, Environment=e }) =
	( print "{ "; print_motif_expr_list d; print ",";
				print_value_environment (!e); print " }" )
and print_value x = case x of
    Val_bool b => ( print "Val_bool "; print b )
|   Val_pair (v1,v2) => ( print "Val_pair ( "; print_value v1; print ", ";
					    print_value v2; print " )" )
|   Val_nil => print "Val_nil"
|   Val_cons (c1,c2) => ( print "Val_cons ( "; print_value c1; print ", ";
					    print_value c2; print " )" )
|   Val_closure cl => ( print "Val_closure "; print_closure cl )
|   Val_primitive f => ( print "Val_primitive "; print "<fun>" )
|   Val_string s => ( print "Val_string "; print s )
|   Val_unit => print "Val_unit"
fun read_operator oper operators =
    case oper of
        One(one) => if (mem one operators) then one else ""
    |   Reserved(r) => ( case r of
		           GE => if (mem ">=" operators) then ">=" else ""
		       |   LE => if (mem "<=" operators) then "<=" else ""
		       |   CONS => if (mem "::" operators) then "::" else ""
		       |   NE => if (mem "<>" operators) then "<>" else ""
		       |   ARROW => if (mem "->" operators) then "->" else ""
		       |   WITH => if (mem "with" operators) then "with"
				else ""
		       |   REC => if (mem "rec" operators) then "rec" else ""
		       |   _ => "" )
    |   _ => "";
fun read_operation ISTREAM ahead read_base operators =
    let fun read_rest ISTREAM a1 e1 =
	let val oper_str = read_operator a1 operators in
	    if oper_str = "" then (a1,e1)
            else let val (a2,e2) = read_base ISTREAM (token ISTREAM) in
                read_rest ISTREAM a2
		    (Application(Variable oper_str,Pair(e1,e2)))
	         end
        end in
    let val (a3,e3) = read_base ISTREAM ahead in
	read_rest ISTREAM a3 e3
    end end;
fun read_infix ISTREAM ahead read_base inf construct_syntax =
    let fun read_start ISTREAM a1 =
	let val (a3,e3) = read_base ISTREAM a1 in
	    let val oper_str = read_operator a3 [inf] in
                if oper_str = "" then (a3,e3)
                else let val (a5,e5) = read_start ISTREAM (token ISTREAM) in
		    (a5, construct_syntax e3 e5) end
            end
        end in
        read_start ISTREAM ahead end;
fun phrase ISTREAM =
    let val (a,d) = definition ISTREAM (token ISTREAM) in d end
and sequence_of_application ISTREAM ahead f =
    let val (a1,ex) = expr_simple ISTREAM ahead in
	if check_expr_simple a1 then
            sequence_of_application ISTREAM a1 (Application(f,ex))
	else (a1,Application(f,ex))
    end
and motif_simple ISTREAM ahead =
    case ahead of
	Identifier(i) => (ahead,Motif_variable i)
    |   Num(n) => (ahead,Motif_number n)
    |   Reserved(TRUE) => (ahead,Motif_boolean true)
    |   Reserved(FALSE) => (ahead,Motif_boolean false)
    |   _ => (ahead,Motif_arrow)
and sequence_of_motif ISTREAM ahead l =
    let val (a1,e1) = motif_simple ISTREAM ahead in
	if e1 <> Motif_arrow then
	    sequence_of_motif ISTREAM (token ISTREAM) (e1::l)
	else (a1,l)
    end
and seq_of_motif ISTREAM ahead =
    let val (a1,l) = sequence_of_motif ISTREAM ahead [] in
	(a1,hd l)
    end
and motif1 ISTREAM ahead = read_infix ISTREAM ahead seq_of_motif "::"
	(fn m1 => fn m2 => Motif_cons(m1,m2))
and motif ISTREAM ahead = read_infix ISTREAM ahead motif1 ","
	(fn m1 => fn m2 => Motif_pair(m1,m2))
and read_list_of_case ISTREAM ahead =
    let fun other_case ISTREAM a1 =
	let val oper_str = read_operator a1 ["|"] in
	    if oper_str <> "|" then (a1,[])
	    else let val (a2,m2) = motif ISTREAM (token ISTREAM) in
		let val oper_str = read_operator a2 ["->"] in
		    if oper_str <> "->" then raise Syntax_error
		    else let val (a3,e3) = expr ISTREAM (token ISTREAM) in
			let val (a4,e4) = other_case ISTREAM a3 in
			    (a4, (m2,e3)::e4)
			end end
                end end
        end
    in let val (a2,m2) = motif ISTREAM ahead in
    	    let val oper_str = read_operator a2 ["->"] in
	        if oper_str <> "->" then raise Syntax_error
	        else let val (a3,e3) = expr ISTREAM (token ISTREAM) in
		    let val (a4,e4) = other_case ISTREAM a3 in
			(a4,(m2,e3)::e4)
		    end end
            end
        end
    end
and expr0 ISTREAM ahead =
    if check_expr_simple ahead then
	let val (a1,e1) = expr_simple ISTREAM ahead in
	    if check_expr_simple a1 then sequence_of_application ISTREAM a1 e1
	    else (a1,e1)
	end
    else if ahead = One(")") then (ahead,Unit) else raise Syntax_error
and expr1 ISTREAM ahead = read_operation ISTREAM ahead expr0 ["*","/"]
and expr2 ISTREAM ahead = read_operation ISTREAM ahead expr1 ["+","-"]
and expr3 ISTREAM ahead = read_operation ISTREAM ahead expr2
	["=","<>","<",">","<=", ">="]
and expr4 ISTREAM ahead = read_infix ISTREAM ahead expr3 "::"
	(fn e1 => fn e2 => Cons(e1,e2))
and expr5 ISTREAM ahead = read_infix ISTREAM ahead expr4 ","
	(fn e1 => fn e2 => Pair(e1,e2))
and expr ISTREAM ahead =
    case ahead of
        Reserved(FUNCTION) => 
	    let val (a1,ml) = read_list_of_case ISTREAM (token ISTREAM) in
		(a1,Function ml)
            end
    |   Reserved(MATCH) =>
	    let val (a1,e1) = expr ISTREAM (token ISTREAM) in
		let val oper_str = read_operator a1 ["with"] in
		    if oper_str <> "with" then raise Syntax_error
		    else let val (a2,ml) =
			read_list_of_case ISTREAM (token ISTREAM) in
			(a2,Application( Function ml, e1 )) end
                end
            end
    |   _ => expr5 ISTREAM ahead
and expr_simple ISTREAM ahead =
    case ahead of
	Identifier(i) => ((token ISTREAM),Variable i)
    |   Num(n) => ((token ISTREAM),Number n)
    |   Reserved(TRUE) => ((token ISTREAM),Boolean true)
    |   Reserved(FALSE) => ((token ISTREAM),Boolean false)
    |   One("(") =>
	    let val (a1,e1) = expr ISTREAM (token ISTREAM) in
		case a1 of
		    One(")") => if e1 = Unit then ((token ISTREAM),Unit)
                     		else ((token ISTREAM),e1)
		|   _ => raise Cant_close_parenthesis
            end
and check_expr_simple ahead =
    case ahead of
	Identifier(i) => true
    |   Num(n) => true
    |   Reserved(TRUE) => true
    |   Reserved(FALSE) => true
    |   One("(") => true
    |   _ => false
and definition ISTREAM ahead =
    case ahead of
        Reserved(LET) =>
	    let val r = ref false; val a5 = token ISTREAM; val a6 = ref a5;
		val n = ref "" in
		let val oper_str = read_operator a5 ["rec"] in
		    if oper_str = "rec" then r:=true else r:=false;
		    if !r then ( a6 := token ISTREAM ) else ( a6 := a5 );
		    case (!a6) of
			Identifier(i) => n := i
		    |   _ => raise Syntax_error;
		    let val a7 = token ISTREAM in
			let val oper_str = read_operator a7 ["="] in
			    if oper_str <> "=" then raise Syntax_error else
				let val (a1,e1)=expr ISTREAM (token ISTREAM) in
					if a1 <> Reserved(IN) then
						(a1,Def(!r, !n, e1))
					else let val (a2,e2) =
						expr ISTREAM (token ISTREAM) in
					    if a2 <> One(";") then
						raise Syntax_error
					    else
					       (a2,Expr(Let(Def(!r,!n,e1),e2)))
					    end
		                end
			end
		    end
		end
	    end
    |   _ =>let val (a,v) = (expr ISTREAM ahead) in (a,Expr v) end;
fun code_number n = Val_number n
and code_number_fn x = case x of 
			Val_number n => n
		     |  _ => raise Eval_Error "integer is expected.\n"
and code_bool b = Val_bool b
and code_bool_fn x = case x of
			Val_bool b => b
		     |  _ => raise Eval_Error "boolean is expected.\n";
fun prim1 coder calcul decoder =
	Val_primitive(fn v => coder(calcul (decoder v)))
and prim2 encoder calcul decoder1 decoder2 = Val_primitive(
	fn (Val_pair(v1,v2)) => encoder(calcul((decoder1 v1),(decoder2 v2)))
    |   _ => raise Eval_Error "pair is expected.");
fun exiting v = ( raise End_of_system; v )
val Val_env_initial = [
    ("+", prim2 code_number ((op+):(int*int)->int)
		code_number_fn code_number_fn),
    ("-", prim2 code_number ((op-):(int*int)->int)
		code_number_fn code_number_fn),
    ("*", prim2 code_number ((op* ):(int*int)->int)
		code_number_fn code_number_fn),
    ("/", prim2 code_number ((op div):(int*int)->int)
		code_number_fn code_number_fn),
    ("=", prim2 code_bool (op=) code_number_fn code_number_fn),
    ("<>", prim2 code_bool (op<>) code_number_fn code_number_fn),
    ("<", prim2 code_bool (op<) code_number_fn code_number_fn),
    (">", prim2 code_bool (op>) code_number_fn code_number_fn),
    ("<=", prim2 code_bool (op<=) code_number_fn code_number_fn),
    (">=", prim2 code_bool (op>=) code_number_fn code_number_fn),
    ("not", prim1 code_bool not code_bool_fn),
    ("write_int", prim1 code_number (fn (x:int) => (print x; print "\n"; 0))
					code_number_fn ),
    ("quit", Val_primitive(fn x => exiting x))];
val type_int = Term ("int",[])
and type_bool = Term ("bool",[])
and type_string = Term ("string",[])
and type_unit = Term("unit",[]);
fun type_arrow t1 t2 = Term ("->",[t1,t2])
and type_product t1 t2 = Term ("*",[t1,t2])
and type_list t = Term ("list",[t]);
fun schema_trivial ty = { Parameters = [], Bodys = ty };
val type_arithmetic = schema_trivial
    (type_arrow (type_product type_int type_int) type_int)
and type_comparison = schema_trivial
    (type_arrow (type_product type_int type_int) type_bool)
val type_env_initial = [
    ("+", type_arithmetic), ("-", type_arithmetic), ("*", type_arithmetic),
    ("/", type_arithmetic), ("=", type_comparison), ("<>", type_comparison),
    ("<", type_comparison), (">", type_comparison), ("<=", type_comparison),
    (">=", type_comparison),
    ("not", schema_trivial(type_arrow type_bool type_bool)),
    ("write_int", schema_trivial(type_arrow type_int type_int)),
    ("quit", schema_trivial(type_arrow type_unit type_unit))];
fun assoc x ((a,b)::rest) = if x = a then b else assoc x rest
|   assoc x [] = raise Not_found;
fun filtrate value motif =
    case (value, motif) of
	(v, Motif_variable id) => [(id,v)]
    |   (Val_bool b1, Motif_boolean b2) =>
	if b1 = b2 then [] else raise Fail_filtrate
    |   (Val_number i1, Motif_number i2) =>
	if i1 = i2 then [] else raise Fail_filtrate
    |   (Val_pair(v1,v2), Motif_pair(m1,m2)) =>
	(filtrate v1 m1)@(filtrate v2 m2)
    |   (Val_nil, Motif_nil) => []
    |   (Val_cons(v1, v2), Motif_cons(m1, m2)) =>
	(filtrate v1 m1)@(filtrate v2 m2)
    |   (_,_) => raise Fail_filtrate;
fun Value_application env list_of_case argument =
    case list_of_case of
	[] => raise Eval_Error "Fail of filtrate"
    |   ((motif, expr) :: other_case) =>
	let val env_extend = (filtrate argument motif) @ env in
	    Eval env_extend expr 
        end handle Fail_filtrate =>
		( Value_application env other_case argument )
and Value_definition env_sequence def =
   let val (b,n,ex) = def in
	if b then
	    case ex of
		Function list_of_case =>
		    let val (closure as { Definition = d, Environment = e} ) =
					{ Definition = list_of_case,
					  Environment = ref [] } in
			let val env_extend =
			    (n, Val_closure closure) :: env_sequence in
				e := env_extend;
				env_extend end end
            |   _ => ( raise Eval_Error "let rec is not functional.";
			env_sequence )
	else (n, (Eval env_sequence ex))::env_sequence
    end
and Eval env expr =
    case expr of
        Variable id => ( (assoc id env) handle
		           Not_found => (
				raise Eval_Error (id^" is not found.");
				Val_unit ) )
    |   Number n => Val_number n
    |   Boolean b => Val_bool b
    |   Function(list_of_case) => Val_closure { Definition= list_of_case,
						Environment = (ref env) }
    |   Application(function, argument) =>
	let val val_function = Eval env function in
	let val val_argument = Eval env argument in
	    case val_function of
		Val_primitive function_primitive =>
		    function_primitive val_argument
	    |  Val_closure (cl as { Definition=d, Environment=e }) =>
		Value_application (!e) d val_argument
	    | _ => raise
		Eval_Error "application of a value is not functional."
        end end
    |   Let(definition, bodys) =>
	    let val Def def = definition in
		Eval (Value_definition env def) bodys
	    end
    |   Pair(e1,e2) => Val_pair(Eval env e1, Eval env e2)
    |   Cons(e1,e2) => Val_cons(Eval env e1, Eval env e2)
    |   Nil => Val_nil
    |   Unit => Val_unit;
fun display_value x =
    case x of
	Val_number n => print n
    |   Val_bool false => print "false"
    |   Val_bool true => print "true"
    |   Val_pair(v1,v2) =>
	( print "("; display_value v1;
	print ", "; display_value v2;
	print ")" )
    |   Val_nil => print "[]"
    |   Val_cons(v1,v2) =>
	    ( display_value v1; print "::"; display_value v2 )
    |   Val_closure _ => print "<fun>"
    |   Val_primitive _ => print "<fun>"
    |   Val_string s => print ("\""^s^"\"")
    |   Val_unit => print "()"
fun print_simple_type_list stl = ( print "[ "; print_simple_type_list_c stl;
			     print " ]" )
and print_simple_type_list_c (h::[]) = print_simple_type h
|   print_simple_type_list_c (h::r) = ( print_simple_type h; print ", ";
				      print_simple_type_list_c r )
|   print_simple_type_list_c [] = ()
and print_simple_type (VarType vot) = ( print "VarType ";
				      print_variable_of_type vot )
|   print_simple_type (Term (s,stl)) = ( print "Term ( \"";
					 print s; print "\", ";
				       print_simple_type_list stl; print " )" )
and print_value_of_an_variable Unknown = print "Unknown "
|   print_value_of_an_variable (Known (st)) = (
    print "Known "; print_simple_type st )
and print_variable_of_type (vt as (ref { Index=i, Value=v }) ) =
    ( print "ref { Index = "; print i; print ", Value = ";
    print_value_of_an_variable; print " }" )
and print_parameters_c (h::[]) = print_variable_of_type h
|   print_parameters_c (h::r) = ( print_variable_of_type h; print ", ";
				print_parameters_c r )
|   print_parameters_c [] = ()
and print_parameters pl = ( print "[ "; print_parameters_c pl; print " ]" )
and print_schema (vv as { Parameters=p, Bodys=b }) = (
    print "{ Parameters = "; print_parameters p;
    print ", Bodys = "; print_simple_type b; print " }" )
and print_type_env_c (((s:string), schema)::[]) =
	( print "( \""; print s; print "\", "; print_schema schema;
	  print " )\n" )
|   print_type_env_c ((s, schema)::r) =
	( print "( \""; print s; print "\", "; print_schema schema;
	  print " ),\n"; print_type_env_c r )
|   print_type_env_c [] = ()
and print_type_env te = ( print "TEnv [ \n";
			print_type_env_c te; print " ]\n" )
val level_of_relation = ref 0;
fun start_of_definition () = inc level_of_relation
and end_of_definition () = dec level_of_relation;
fun new_unknown () =
    let val x = ref {Index = !level_of_relation, Value = Unknown} in
	VarType x end
fun mem x (h::r) = if x = h then true else (mem x r)
|   mem x [] = false;
fun gen ty =
    let val parameters = ref [] in
    let fun find_parameters ty =
        case (shorten ty) of
	    VarType (vv as (ref {Index=i, Value=v})) =>
		if ((i > (!level_of_relation)) andalso
		    (not (mem vv (!parameters))))
		then parameters := (vv :: (!parameters))
		else ()
        |   Term(constr, arguments) =>
	    app find_parameters arguments
        |   _ => ()
    in
	( find_parameters ty;
	{ Parameters = (!parameters), Bodys = ty } )
    end end
and shorten x =
    case x of
	VarType (vv as (ref {Index=i, Value=v})) =>
	    ( case v of
		Known ty1 =>
		    ( let val shorten_ty1 = shorten ty1 in
			vv := {Index=i, Value=(Known(shorten_ty1))};
		        shorten_ty1 end )
	      | _ => x )
    | _ => x;
val name_of_variables = ref ([]:(variable_of_type * string) list)
val count_of_variables = ref 0;
fun display_var vv = ( print "'";
    let val name = assoc vv (!name_of_variables) handle
	Not_found =>
	    let val name = chr (ord("a") + (!count_of_variables)) in
		inc count_of_variables;
		name_of_variables := ((vv,name) :: (!name_of_variables));
                name
            end in
        print name
    end )
and display ty =
    case (shorten ty) of
	VarType vv => display_var vv
    |   Term( constructor, arguments ) =>
        ( case (length arguments) of
            0 => print constructor
        |   1 => ( display (nth (arguments,0));
                 print " "; print constructor )
        |   2 => ( print "("; display (nth (arguments,0));
                 print " "; print constructor;
                 print " "; display (nth (arguments,1));
                 print ")" ) )
and display_type ty = (
    name_of_variables := [];
    count_of_variables := 0;
    display ty )
and display_schema (schema as {Parameters=p, Bodys=b}) =
    ( name_of_variables := [];
    count_of_variables := 0;
    if p <> [] then (
	print "for all ";
	app (fn vv => (display_var vv; print " ")) p;
        print ", " )
    else ();
    display b );
fun test_of_occurrence vv ty =
    let fun test ty1 =
	case shorten ty1 of
	    VarType (vv1 as (ref {Index=i, Value=v})) =>
		if vv1 = vv then raise Circulation (VarType vv, ty)
		else ()
	|   Term(constructor, arguments) => app test arguments
    in test ty end;
fun modify_level level_max ty =
    case shorten ty of
	VarType (vv as (ref {Index=i, Value=v})) =>
	    if i > level_max then vv := {Index=level_max, Value=v}
			     else ()
    |   Term(constructor, arguments) => app (modify_level level_max) arguments;
fun unify ty1 ty2 =
    let val value1 = shorten ty1; val value2 = shorten ty2 in
        if value1 = value2 then () else
	    case (value1, value2) of
		(VarType (vv as (ref {Index=i, Value=v})), ty) =>
		    ( test_of_occurrence vv ty;
		    modify_level i ty;
		    vv := {Index=i, Value=Known ty} )
            |   (ty, VarType(vv as (ref {Index=i, Value=v}))) =>
		    ( test_of_occurrence vv ty;
		    modify_level i ty;
		    vv := {Index=i, Value=Known ty} )
            |   (Term(constr1, arguments1), Term(constr2, arguments2)) =>
		    if constr1 <> constr2 then
			raise Conflict (value1,value2)
		    else
			let val i = ref 0 in
			    while (!i) < length(arguments1) do (
			        unify (nth (arguments1,(!i)))
				      (nth (arguments2,(!i))); inc i )
			end
    end
fun specialization (schema as {Parameters=p,Bodys=b}) =
    case p of
	[] => b
    |   parameters =>
	( let val new_unknowns = map (fn v => (v, new_unknown())) parameters in
    	    let fun copy ty =
		( case (shorten ty) of
		    (ty as (VarType v)) =>
			( assoc v new_unknowns handle
			    Not_found => ty )
		|   Term(constr, arguments) =>
		    Term(constr, (map copy arguments)) )
	    in
		copy b end end );
fun type_motif env x =
    case x of
	Motif_variable id =>
	    let val ty = new_unknown() in
		(ty, (id, schema_trivial ty)::env)
	    end
    |   Motif_boolean b => (type_bool, env)
    |   Motif_number n => (type_int, env)
    |   Motif_pair (m1,m2) =>
	let val (ty1, env1) = type_motif env m1;
	    val (ty2, env2) = type_motif env m2 in
		(type_product ty1 ty2, env2)
	end
    |   Motif_nil => (type_list (new_unknown()), env)
    |   Motif_cons(m1,m2) =>
	let val (ty1, env1) = type_motif env m1 in
	let val (ty2, env2) = type_motif env1 m2 in
	    unify (type_list ty1) ty2;
	    (ty2, env2) end end
and type_exp env x =
    case x of
        Number n => type_int
    |   Boolean b => type_bool
    |   Nil => type_list (new_unknown())
    |   Unit => type_unit
    |   Variable id => ( specialization (assoc id env) handle
		  Not_found => raise (Type_Error (id^" is not found.")) )
    |   Let((Def def), bodys) => type_exp (type_def env def) bodys
    |   Function(list_of_case) =>
	    let val argument_type = new_unknown();
	        val return_type = new_unknown() in
	        let fun case_type (motif, expr) =
		    let val (type_m, env_extend) = type_motif env motif in
		        unify type_m argument_type;
		        let val type_expr = type_exp env_extend expr in
			    unify type_expr return_type
			end end
                in
		    app case_type list_of_case;
		    type_arrow argument_type return_type
		end
            end
    |   Application( function, argument ) =>
	    let val function_type = type_exp env function;
	        val argument_type = type_exp env argument;
	        val return_type = new_unknown() in
		unify function_type (type_arrow argument_type return_type);
                return_type
            end
    |   Cons(e1, e2) =>
	let val type_e1 = type_exp env e1;
	    val type_e2 = type_exp env e2 in
	    unify (type_list type_e1) type_e2;
	    type_e2
	end
    |   Pair(e1, e2) => type_product (type_exp env e1) (type_exp env e2)
and type_def env (b,s,exp) = (
    start_of_definition();
    let val type_expr =
	if b then
	    let val type_provisoire = new_unknown() in
	    let val type_expr =
		type_exp ((s, schema_trivial type_provisoire)::env) exp in
		unify type_expr type_provisoire;
		type_expr end end
	else (type_exp env exp)
    in
	end_of_definition();
	(s, gen type_expr)::env
    end )
fun read_phrase ISTREAM = phrase ISTREAM;
fun run () =
    let val type_env = ref type_env_initial;
	val val_env = ref Val_env_initial in
    let val stream_of_enter = std_in in
	while true do (
	    print("## "); flush_out std_out;
	    let val result = read_phrase stream_of_enter in
( print_definition result; print "\n";
		case result of
		    Expr expr =>
			let val ty = type_exp (!type_env) expr;
			    val ret = Eval (!val_env) expr in
			    print "- : "; display_type ty;
			    print " = "; display_value ret; print "\n"
			end
		|   Def def => 
			let val new_type_env = type_def (!type_env) def;
			    val new_val_env = Value_definition (!val_env) def
			in
			    case (new_type_env, new_val_env) of
				(((name, schema)::_), ((_, v)::_)) =>
				    ( print (name^" : ");
				    display_schema schema;
				    print " = "; display_value v;
				    print "\n" );
			    type_env := new_type_env;
			    val_env := new_val_env
			end )
            end handle
	        Syntax_error => print "Parse error: Syntax error.\n"
	    |   Cant_close_parenthesis =>
			print"Parse error: Can't find the right parenthesis.\n"
	    |   Type_Error str => ( print "Type check error: ";
				print str; print "\n" )
	    |   Eval_Error str => ( print "Eval error: ";
				print str; print "\n" )
	    |	Conflict (sty1,sty2) => ( print "Type check error: ";
				print "Incompatible in types entry ";
				display_type sty1; print " with ";
				display_type sty2; print "\n" )
	    |   Circulation (sty1,sty2) => ( print "Type check error: ";
				print "Impossible for identifier ";
				display_type sty1; print " and ";
				display_type sty2; print "\n" )
	    |   End_of_system => ( print "End of MINICAML.sml...\n";
					raise Quit_system; () ) )
    end end;
print "please type run();\n";
