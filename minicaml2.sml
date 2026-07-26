(* ================================================================
   MINICAML2.sml  --  an evolved MINICAML interpreter in Standard ML

   Derived from minicaml.sml (Copyright (c) 1996 Yasushi KODAMA),
   itself translated from the MINICAML distributed with Caml Light
   0.71 (Copyright INRIA).  Distributed under the same conditions:
   free to use, modify and integrate, provided derivative works keep
   these conditions and this notice.

   ----------------------------------------------------------------
   What is new with respect to the 1996 version
   ----------------------------------------------------------------
   * Portable Standard ML.  The old SML/NJ-only primitives
     (lookahead/input/std_in/polymorphic print/inc/dec/nth) are gone;
     this file compiles under Poly/ML, MLton and SML/NJ.
   * Real tokenizer + recursive-descent parser with one token of
     lookahead held in a mutable cell, instead of threading the
     lookahead token through every production by hand.
   * New syntax
       - if e1 then e2 else e3
       - list literals   [e1; e2; e3]     and   []
       - list patterns   [], [p1; p2], p1 :: p2
       - wildcard pattern  _   and parenthesised patterns  (p1, p2)
       - function definition sugar   let f x y = e
                                     let rec f x = e
       - anonymous functions         fun x y -> e
       - let ... in ... as a real expression, nestable anywhere
       - short-circuit  &&  and  ||
       - string literals with escapes, and  ^  for concatenation
       - unary minus, and the  mod  operator (OCaml semantics: the
         remainder takes the sign of the dividend)
       - (* nestable comments *)
   * Polymorphic structural equality and ordering
     (=, <>, <, >, <=, >= now work on ints, strings, bools, unit,
      tuples and lists), plus the polymorphic primitives
      hd, tl, fst, snd.
   * Nicer printing: lists show as [1; 2; 3], strings are escaped,
     type variables no longer run out after 26 of them.
   * Better diagnostics: parse errors say what was found and what was
     expected, and the reader resynchronises at the next `;'.
   * Optional AST tracing, toggled with the `trace' reference.

   Phrases are terminated by a single semicolon `;' as before.  A `;'
   inside brackets is the list separator, so [1; 2; 3]; is fine.

   Usage
     $ poly -q --use minicaml2.sml           then type   run ();
     $ ...                                   or          runFile "demo.mml";
   ================================================================ *)


(* ================================================================
   1.  Lexical analysis
   ================================================================ *)

(* The integers of the object language are arbitrary precision, so a
   program may compute 2^64-1 or 100! without any silent wrap-around or
   overflow trap.  Everything internal to the interpreter (levels,
   indices, list lengths) keeps using the host's fixed int. *)
type num = IntInf.int

datatype token =
    TNUM of num             (* 42, or 10^100             *)
  | TSTR of string          (* "hello"                   *)
  | TID  of string          (* x, foo_bar, map           *)
  | TKW  of string          (* let, if, function, ...    *)
  | TOP  of string          (* + - -> :: ( ) [ ] ; | ... *)
  | TEOF

exception Lex_error of string
exception Syntax_error of string
exception End_of_input
exception End_of_system

(* SML writes negative integers as ~1; this language, like Caml, uses -1. *)
fun intToString (n : num) =
    String.translate (fn #"~" => "-" | c => String.str c) (IntInf.toString n)

fun tokenString t =
    case t of
        TNUM n => intToString n
      | TSTR s => "\"" ^ String.toString s ^ "\""
      | TID s  => s
      | TKW s  => s
      | TOP s  => s
      | TEOF   => "<end of input>"

val keywords =
    ["let", "rec", "in", "if", "then", "else",
     "fun", "function", "match", "with", "true", "false"]

fun isIdStart c = Char.isAlpha c orelse c = #"_"
fun isIdChar  c = Char.isAlphaNum c orelse c = #"_" orelse c = #"'"

(* Read exactly one token from `ins'.  Whitespace and (* nested
   comments *) are skipped.  Returns TEOF at end of file. *)
fun lex ins =
    let
      fun peek () = TextIO.lookahead ins
      fun eat  () = ignore (TextIO.input1 ins)

      fun skipComment 0 = ()
        | skipComment n =
            (case TextIO.input1 ins of
                 NONE => raise Lex_error "unterminated comment"
               | SOME #"*" =>
                   (case peek () of
                        SOME #")" => (eat (); skipComment (n - 1))
                      | _ => skipComment n)
               | SOME #"(" =>
                   (case peek () of
                        SOME #"*" => (eat (); skipComment (n + 1))
                      | _ => skipComment n)
               | SOME _ => skipComment n)

      fun takeWhile p acc =
          case peek () of
              SOME c => if p c then (eat (); takeWhile p (c :: acc))
                        else String.implode (List.rev acc)
            | NONE => String.implode (List.rev acc)

      fun lexString acc =
          case TextIO.input1 ins of
              NONE => raise Lex_error "unterminated string literal"
            | SOME #"\"" => String.implode (List.rev acc)
            | SOME #"\\" =>
                (case TextIO.input1 ins of
                     SOME #"n"  => lexString (#"\n" :: acc)
                   | SOME #"t"  => lexString (#"\t" :: acc)
                   | SOME #"\\" => lexString (#"\\" :: acc)
                   | SOME #"\"" => lexString (#"\"" :: acc)
                   | SOME c     => lexString (c :: acc)
                   | NONE => raise Lex_error "unterminated string literal")
            | SOME c => lexString (c :: acc)

      (* if the next character is `c', consume it and return `yes' *)
      fun two c yes no =
          case peek () of
              SOME c' => if c = c' then (eat (); yes) else no
            | NONE => no

      fun go () =
          case peek () of
              NONE => TEOF
            | SOME c =>
                if Char.isSpace c then (eat (); go ())
                else if Char.isDigit c then
                    let val s = takeWhile Char.isDigit []
                    in case IntInf.fromString s of
                           SOME n => TNUM n
                         | NONE => raise Lex_error ("bad integer " ^ s)
                    end
                else if isIdStart c then
                    let val s = takeWhile isIdChar []
                    in if s = "_" then TOP "_"
                       else if s = "mod" then TOP "mod"
                       else if List.exists (fn k => k = s) keywords then TKW s
                       else TID s
                    end
                else if c = #"\"" then (eat (); TSTR (lexString []))
                else
                  (eat ();
                   case c of
                       #"(" => (case peek () of
                                    SOME #"*" => (eat (); skipComment 1; go ())
                                  | _ => TOP "(")
                     | #"-" => two #">" (TOP "->") (TOP "-")
                     | #"<" => (case peek () of
                                    SOME #"=" => (eat (); TOP "<=")
                                  | SOME #">" => (eat (); TOP "<>")
                                  | _ => TOP "<")
                     | #">" => two #"=" (TOP ">=") (TOP ">")
                     | #":" => two #":" (TOP "::") (TOP ":")
                     | #"&" => two #"&" (TOP "&&") (TOP "&")
                     | #"|" => two #"|" (TOP "||") (TOP "|")
                     | _    => TOP (String.str c))
    in
      go ()
    end


(* ================================================================
   2.  Abstract syntax
   ================================================================ *)

datatype expr =
    Number    of num
  | Str       of string
  | Boolean   of bool
  | Variable  of string
  | Nil
  | Unit
  | Pair      of expr * expr
  | Cons      of expr * expr
  | If        of expr * expr * expr
  | Function  of (motif * expr) list
  | Application of expr * expr
  | Let       of bool * string * expr * expr   (* let [rec] x = e1 in e2 *)

and motif =
    Motif_variable of string
  | Motif_wild
  | Motif_number  of num
  | Motif_string  of string
  | Motif_boolean of bool
  | Motif_unit
  | Motif_nil
  | Motif_pair of motif * motif
  | Motif_cons of motif * motif

datatype definition =
    Def  of bool * string * expr                (* let [rec] x = e *)
  | Expr of expr


(* ================================================================
   3.  Parser  (recursive descent, one token of lookahead)
   ================================================================ *)

type lexstate = { ins : TextIO.instream, tok : token ref }

fun mkstate ins : lexstate = { ins = ins, tok = ref TEOF }
fun cur (st : lexstate) = ! (#tok st)
fun advance (st : lexstate) = (#tok st) := lex (#ins st)

fun isOp st s = (cur st = TOP s)
fun isKw st s = (cur st = TKW s)

fun expected st what =
    raise Syntax_error (what ^ " expected, but found `"
                        ^ tokenString (cur st) ^ "'")

fun expectOp st s = if isOp st s then advance st else expected st ("`" ^ s ^ "'")
fun expectKw st s = if isKw st s then advance st else expected st ("`" ^ s ^ "'")

fun binop oper e1 e2 = Application (Variable oper, Pair (e1, e2))

val comparisons = ["=", "<>", "<", ">", "<=", ">="]
fun isMember x l = List.exists (fn y => y = x) l

(* ---------------- patterns ---------------- *)

fun parse_motif st =                        (* p1, p2, p3   (right assoc) *)
    let val m = parse_motif_cons st
    in if isOp st "," then (advance st; Motif_pair (m, parse_motif st)) else m
    end

and parse_motif_cons st =                   (* p1 :: p2     (right assoc) *)
    let val m = parse_motif_atom st
    in if isOp st "::" then (advance st; Motif_cons (m, parse_motif_cons st))
       else m
    end

and parse_motif_atom st =
    case cur st of
        TID s        => (advance st; Motif_variable s)
      | TOP "_"      => (advance st; Motif_wild)
      | TNUM n       => (advance st; Motif_number n)
      | TSTR s       => (advance st; Motif_string s)
      | TKW "true"   => (advance st; Motif_boolean true)
      | TKW "false"  => (advance st; Motif_boolean false)
      | TOP "-"      => (advance st;
                         case cur st of
                             TNUM n => (advance st;
                                        Motif_number (IntInf.~ n))
                           | _ => expected st "an integer literal")
      | TOP "("      => (advance st;
                         if isOp st ")" then (advance st; Motif_unit)
                         else let val m = parse_motif st
                              in expectOp st ")"; m end)
      | TOP "["      => (advance st;
                         if isOp st "]" then (advance st; Motif_nil)
                         else let val m = parse_motif_list st
                              in expectOp st "]"; m end)
      | _ => expected st "a pattern"

and parse_motif_list st =                   (* inside [ ... ] *)
    let val m = parse_motif st
    in if isOp st ";" then
           (advance st;
            if isOp st "]" then Motif_cons (m, Motif_nil)
            else Motif_cons (m, parse_motif_list st))
       else Motif_cons (m, Motif_nil)
    end

fun startsMotif t =
    case t of
        TID _ => true | TNUM _ => true | TSTR _ => true
      | TOP "_" => true | TOP "(" => true | TOP "[" => true
      | TKW "true" => true | TKW "false" => true
      | _ => false

fun startsAtom t =
    case t of
        TNUM _ => true | TSTR _ => true | TID _ => true
      | TKW "true" => true | TKW "false" => true
      | TOP "(" => true | TOP "[" => true
      | _ => false

(* ---------------- expressions ---------------- *)

fun curry_fun [] body = body
  | curry_fun (p :: ps) body = Function [(p, curry_fun ps body)]

fun parse_expr st =
    case cur st of
        TKW "if" =>
          (advance st;
           let val c = parse_expr st
               val _ = expectKw st "then"
               val a = parse_expr st
               val _ = expectKw st "else"
               val b = parse_expr st
           in If (c, a, b) end)
      | TKW "fun" =>
          (advance st;
           let val ps = parse_params st
               val _ = expectOp st "->"
           in curry_fun ps (parse_expr st) end)
      | TKW "function" =>
          (advance st; Function (parse_cases st))
      | TKW "match" =>
          (advance st;
           let val e = parse_expr st
               val _ = expectKw st "with"
           in Application (Function (parse_cases st), e) end)
      | TKW "let" =>
          (advance st;
           let val (r, name, rhs) = parse_let_header st
               val _ = expectKw st "in"
           in Let (r, name, rhs, parse_expr st) end)
      | _ => parse_tuple st

(* one or more formal parameters, each an atomic pattern *)
and parse_params st =
    let fun loop acc =
            if startsMotif (cur st) andalso not (isOp st "[")
            then loop (parse_motif_atom st :: acc)
            else List.rev acc
    in case loop [] of
           [] => expected st "a parameter"
         | ps => ps
    end

(* after `let' has been consumed: [rec] name params = expr *)
and parse_let_header st =
    let val isrec = if isKw st "rec" then (advance st; true) else false
        val name  = case cur st of
                        TID s => (advance st; s)
                      | _ => expected st "an identifier after `let'"
        val params = if isOp st "=" then [] else parse_params st
        val _ = expectOp st "="
        val rhs = parse_expr st
    in (isrec, name, curry_fun params rhs) end

(* p -> e | p -> e | ...   (a leading `|' is allowed) *)
and parse_cases st =
    let fun one () =
            let val m = parse_motif st
                val _ = expectOp st "->"
            in (m, parse_expr st) end
        fun loop acc =
            let val c = one ()
            in if isOp st "|" then (advance st; loop (c :: acc))
               else List.rev (c :: acc)
            end
    in if isOp st "|" then advance st else ();
       loop []
    end

and parse_tuple st =                        (* ,   (right assoc)          *)
    let val e = parse_or st
    in if isOp st "," then (advance st; Pair (e, parse_tuple st)) else e end

and parse_or st =                           (* ||  (short circuit)        *)
    let fun loop e =
            if isOp st "||" then
                (advance st; loop (If (e, Boolean true, parse_and st)))
            else e
    in loop (parse_and st) end

and parse_and st =                          (* &&  (short circuit)        *)
    let fun loop e =
            if isOp st "&&" then
                (advance st; loop (If (e, parse_cmp st, Boolean false)))
            else e
    in loop (parse_cmp st) end

and parse_cmp st =                          (* = <> < > <= >=             *)
    let fun loop e =
            case cur st of
                TOP oper =>
                  if isMember oper comparisons
                  then (advance st; loop (binop oper e (parse_cons st)))
                  else e
              | _ => e
    in loop (parse_cons st) end

and parse_cons st =                         (* ::  (right assoc)          *)
    let val e = parse_cat st
    in if isOp st "::" then (advance st; Cons (e, parse_cons st)) else e end

and parse_cat st =                          (* ^   (right assoc)          *)
    let val e = parse_add st
    in if isOp st "^" then (advance st; binop "^" e (parse_cat st)) else e end

and parse_add st =                          (* + - (left assoc)           *)
    let fun loop e =
            case cur st of
                TOP "+" => (advance st; loop (binop "+" e (parse_mul st)))
              | TOP "-" => (advance st; loop (binop "-" e (parse_mul st)))
              | _ => e
    in loop (parse_mul st) end

and parse_mul st =                          (* * / mod (left assoc)       *)
    let fun loop e =
            case cur st of
                TOP "*"   => (advance st; loop (binop "*" e (parse_app st)))
              | TOP "/"   => (advance st; loop (binop "/" e (parse_app st)))
              | TOP "mod" => (advance st; loop (binop "mod" e (parse_app st)))
              | _ => e
    in loop (parse_app st) end

and parse_app st =                          (* juxtaposition, unary minus *)
    if isOp st "-" then
        (advance st; binop "-" (Number (IntInf.fromInt 0)) (parse_app st))
    else
        let fun loop e =
                if startsAtom (cur st) then loop (Application (e, parse_atom st))
                else e
        in loop (parse_atom st) end

and parse_atom st =
    case cur st of
        TNUM n      => (advance st; Number n)
      | TSTR s      => (advance st; Str s)
      | TID s       => (advance st; Variable s)
      | TKW "true"  => (advance st; Boolean true)
      | TKW "false" => (advance st; Boolean false)
      | TOP "("     => (advance st;
                        if isOp st ")" then (advance st; Unit)
                        else let val e = parse_expr st
                             in expectOp st ")"; e end)
      | TOP "["     => (advance st;
                        if isOp st "]" then (advance st; Nil)
                        else let val e = parse_elems st
                             in expectOp st "]"; e end)
      | _ => expected st "an expression"

and parse_elems st =                        (* inside [ ... ] *)
    let val e = parse_expr st
    in if isOp st ";" then
           (advance st;
            if isOp st "]" then Cons (e, Nil) else Cons (e, parse_elems st))
       else Cons (e, Nil)
    end

(* A whole toplevel phrase, up to but not including the final `;'. *)
fun parse_phrase st =
    case cur st of
        TEOF => raise End_of_input
      | TKW "let" =>
          (advance st;
           let val (r, name, rhs) = parse_let_header st
           in if isKw st "in"
              then (advance st; Expr (Let (r, name, rhs, parse_expr st)))
              else Def (r, name, rhs)
           end)
      | _ => Expr (parse_expr st)


(* ================================================================
   4.  AST printing (only used when `trace' is on)
   ================================================================ *)

fun showMotif m =
    case m of
        Motif_variable v => v
      | Motif_wild       => "_"
      | Motif_number n   => intToString n
      | Motif_string s   => "\"" ^ String.toString s ^ "\""
      | Motif_boolean b  => Bool.toString b
      | Motif_unit       => "()"
      | Motif_nil        => "[]"
      | Motif_pair (a,b) => "(" ^ showMotif a ^ ", " ^ showMotif b ^ ")"
      | Motif_cons (a,b) => "(" ^ showMotif a ^ " :: " ^ showMotif b ^ ")"

fun showExpr e =
    case e of
        Number n     => intToString n
      | Str s        => "\"" ^ String.toString s ^ "\""
      | Boolean b    => Bool.toString b
      | Variable v   => v
      | Nil          => "[]"
      | Unit         => "()"
      | Pair (a,b)   => "(" ^ showExpr a ^ ", " ^ showExpr b ^ ")"
      | Cons (a,b)   => "(" ^ showExpr a ^ " :: " ^ showExpr b ^ ")"
      | If (c,a,b)   => "(if " ^ showExpr c ^ " then " ^ showExpr a
                        ^ " else " ^ showExpr b ^ ")"
      | Function cs  => "(function " ^ showCases cs ^ ")"
      | Application (f,a) => "(" ^ showExpr f ^ " " ^ showExpr a ^ ")"
      | Let (r,n,a,b) => "(let " ^ (if r then "rec " else "") ^ n ^ " = "
                         ^ showExpr a ^ " in " ^ showExpr b ^ ")"

and showCases [] = ""
  | showCases [(m,e)] = showMotif m ^ " -> " ^ showExpr e
  | showCases ((m,e) :: r) = showMotif m ^ " -> " ^ showExpr e ^ " | "
                             ^ showCases r

fun showDefinition (Expr e) = showExpr e
  | showDefinition (Def (r,n,e)) =
      "let " ^ (if r then "rec " else "") ^ n ^ " = " ^ showExpr e


(* ================================================================
   5.  Values and the evaluator
   ================================================================ *)

datatype value =
    Val_number  of num
  | Val_bool    of bool
  | Val_string  of string
  | Val_unit
  | Val_nil
  | Val_pair    of value * value
  | Val_cons    of value * value
  | Val_closure of (motif * expr) list * (string * value) list ref
  | Val_primitive of string * (value -> value)

exception Eval_error of string
exception Not_found
exception Fail_filtrate

fun assoc x ((a, b) :: rest) = if x = a then b else assoc x rest
  | assoc _ [] = raise Not_found

(* structural ordering; functional values are incomparable *)
fun val_compare (v1, v2) =
    case (v1, v2) of
        (Val_number a, Val_number b) => IntInf.compare (a, b)
      | (Val_string a, Val_string b) => String.compare (a, b)
      | (Val_bool a, Val_bool b) =>
          if a = b then EQUAL else if b then LESS else GREATER
      | (Val_unit, Val_unit) => EQUAL
      | (Val_nil, Val_nil) => EQUAL
      | (Val_nil, Val_cons _) => LESS
      | (Val_cons _, Val_nil) => GREATER
      | (Val_pair (a,b), Val_pair (c,d)) =>
          (case val_compare (a, c) of EQUAL => val_compare (b, d) | r => r)
      | (Val_cons (a,b), Val_cons (c,d)) =>
          (case val_compare (a, c) of EQUAL => val_compare (b, d) | r => r)
      | _ => raise Eval_error "these values cannot be compared"

fun filtrate (v, m) =
    case (v, m) of
        (_, Motif_variable id) => [(id, v)]
      | (_, Motif_wild) => []
      | (Val_bool a,   Motif_boolean b) => if a = b then [] else raise Fail_filtrate
      | (Val_number a, Motif_number b)  => if a = b then [] else raise Fail_filtrate
      | (Val_string a, Motif_string b)  => if a = b then [] else raise Fail_filtrate
      | (Val_unit, Motif_unit) => []
      | (Val_nil,  Motif_nil)  => []
      | (Val_pair (a,b), Motif_pair (m1,m2)) => filtrate (a,m1) @ filtrate (b,m2)
      | (Val_cons (a,b), Motif_cons (m1,m2)) => filtrate (a,m1) @ filtrate (b,m2)
      | _ => raise Fail_filtrate

fun value_application env cases arg =
    case cases of
        [] => raise Eval_error "no matching case in this function"
      | ((m, body) :: rest) =>
          (let val env' = filtrate (arg, m) @ env
           in eval env' body end
           handle Fail_filtrate => value_application env rest arg)

and value_definition env (isrec, name, e) =
    if isrec then
        case e of
            Function cases =>
              let val cell = ref []
                  val env' = (name, Val_closure (cases, cell)) :: env
              in cell := env'; env' end
          | _ => raise Eval_error
                   ("`let rec " ^ name ^ "' must define a function")
    else (name, eval env e) :: env

and eval env e =
    case e of
        Number n   => Val_number n
      | Str s      => Val_string s
      | Boolean b  => Val_bool b
      | Nil        => Val_nil
      | Unit       => Val_unit
      | Variable id =>
          (assoc id env
           handle Not_found => raise Eval_error (id ^ " is not bound"))
      | Pair (a, b) => Val_pair (eval env a, eval env b)
      | Cons (a, b) => Val_cons (eval env a, eval env b)
      | If (c, a, b) =>
          (case eval env c of
               Val_bool true  => eval env a
             | Val_bool false => eval env b
             | _ => raise Eval_error "the condition of `if' is not a boolean")
      | Function cases => Val_closure (cases, ref env)
      | Let (r, n, a, b) => eval (value_definition env (r, n, a)) b
      | Application (f, a) =>
          let val vf = eval env f
              val va = eval env a
          in case vf of
                 Val_primitive (_, p) => p va
               | Val_closure (cases, cell) => value_application (!cell) cases va
               | _ => raise Eval_error "this value is not a function"
          end


(* ================================================================
   6.  Types
   ================================================================ *)

datatype simple_type =
    VarType of { index : int, value : tyval } ref
  | Term of string * simple_type list
and tyval = Unknown | Known of simple_type

type tyvar = { index : int, value : tyval } ref
type schema = { parameters : tyvar list, bodys : simple_type }

exception Type_error of string
exception Circulation of simple_type * simple_type
exception Conflict of simple_type * simple_type

val type_int    = Term ("int", [])
val type_bool   = Term ("bool", [])
val type_string = Term ("string", [])
val type_unit   = Term ("unit", [])
fun type_arrow t1 t2   = Term ("->", [t1, t2])
fun type_product t1 t2 = Term ("*",  [t1, t2])
fun type_list t        = Term ("list", [t])

fun schema_trivial ty : schema = { parameters = [], bodys = ty }

(* build a scheme with one/two universally quantified variables *)
fun poly1 f : schema =
    let val a = ref { index = 0, value = Unknown }
    in { parameters = [a], bodys = f (VarType a) } end
fun poly2 f : schema =
    let val a = ref { index = 0, value = Unknown }
        val b = ref { index = 0, value = Unknown }
    in { parameters = [a, b], bodys = f (VarType a) (VarType b) } end

val level = ref 0
fun start_of_definition () = level := !level + 1
fun end_of_definition ()   = level := !level - 1
fun new_unknown () = VarType (ref { index = !level, value = Unknown })

fun shorten ty =
    case ty of
        VarType (vv as ref { index = i, value = Known t }) =>
          let val t' = shorten t
          in vv := { index = i, value = Known t' }; t' end
      | _ => ty

fun gen ty : schema =
    let val parameters = ref ([] : tyvar list)
        fun find ty =
            case shorten ty of
                VarType (vv as ref { index = i, value = _ }) =>
                  if i > !level andalso
                     not (List.exists (fn v => v = vv) (!parameters))
                  then parameters := vv :: !parameters
                  else ()
              | Term (_, args) => List.app find args
    in find ty; { parameters = !parameters, bodys = ty } end

fun test_of_occurrence vv ty =
    let fun test t =
            case shorten t of
                VarType vv1 => if vv1 = vv then raise Circulation (VarType vv, ty)
                               else ()
              | Term (_, args) => List.app test args
    in test ty end

fun modify_level lmax ty =
    case shorten ty of
        VarType (vv as ref { index = i, value = v }) =>
          if i > lmax then vv := { index = lmax, value = v } else ()
      | Term (_, args) => List.app (modify_level lmax) args

fun unify (ty1, ty2) =
    let val v1 = shorten ty1
        val v2 = shorten ty2
    in
      if v1 = v2 then ()
      else
        case (v1, v2) of
            (VarType (vv as ref { index = i, value = _ }), ty) =>
              (test_of_occurrence vv ty;
               modify_level i ty;
               vv := { index = i, value = Known ty })
          | (ty, VarType (vv as ref { index = i, value = _ })) =>
              (test_of_occurrence vv ty;
               modify_level i ty;
               vv := { index = i, value = Known ty })
          | (Term (c1, a1), Term (c2, a2)) =>
              if c1 <> c2 orelse length a1 <> length a2
              then raise Conflict (v1, v2)
              else ListPair.app unify (a1, a2)
    end

fun specialization ({ parameters = [], bodys } : schema) = bodys
  | specialization { parameters, bodys } =
      let val fresh = List.map (fn v => (v, new_unknown ())) parameters
          fun copy ty =
              case shorten ty of
                  (t as VarType v) => (assoc v fresh handle Not_found => t)
                | Term (c, args) => Term (c, List.map copy args)
      in copy bodys end

fun type_motif env m =
    case m of
        Motif_variable id =>
          let val ty = new_unknown ()
          in (ty, (id, schema_trivial ty) :: env) end
      | Motif_wild      => (new_unknown (), env)
      | Motif_boolean _ => (type_bool, env)
      | Motif_number _  => (type_int, env)
      | Motif_string _  => (type_string, env)
      | Motif_unit      => (type_unit, env)
      | Motif_nil       => (type_list (new_unknown ()), env)
      | Motif_pair (m1, m2) =>
          let val (t1, env1) = type_motif env m1
              val (t2, env2) = type_motif env1 m2
          in (type_product t1 t2, env2) end
      | Motif_cons (m1, m2) =>
          let val (t1, env1) = type_motif env m1
              val (t2, env2) = type_motif env1 m2
          in unify (type_list t1, t2); (t2, env2) end

fun type_exp env e =
    case e of
        Number _  => type_int
      | Str _     => type_string
      | Boolean _ => type_bool
      | Unit      => type_unit
      | Nil       => type_list (new_unknown ())
      | Variable id =>
          (specialization (assoc id env)
           handle Not_found => raise Type_error (id ^ " is not bound"))
      | Pair (a, b) => type_product (type_exp env a) (type_exp env b)
      | Cons (a, b) =>
          let val ta = type_exp env a
              val tb = type_exp env b
          in unify (type_list ta, tb); tb end
      | If (c, a, b) =>
          let val tc = type_exp env c
              val ta = type_exp env a
              val tb = type_exp env b
          in unify (tc, type_bool); unify (ta, tb); ta end
      | Let (r, n, a, b) => type_exp (type_def env (r, n, a)) b
      | Function cases =>
          let val targ = new_unknown ()
              val tres = new_unknown ()
              fun case_type (m, body) =
                  let val (tm, env') = type_motif env m
                  in unify (tm, targ);
                     unify (type_exp env' body, tres)
                  end
          in List.app case_type cases; type_arrow targ tres end
      | Application (f, a) =>
          let val tf = type_exp env f
              val ta = type_exp env a
              val tr = new_unknown ()
          in unify (tf, type_arrow ta tr); tr end

and type_def env (isrec, name, e) =
    (start_of_definition ();
     let val te =
             if isrec then
                 let val prov = new_unknown ()
                     val te = type_exp ((name, schema_trivial prov) :: env) e
                 in unify (te, prov); te end
             else type_exp env e
     in end_of_definition (); (name, gen te) :: env end)


(* ================================================================
   7.  Printing values and types
   ================================================================ *)

fun escape s = "\"" ^ String.toString s ^ "\""

fun showValue v =
    case v of
        Val_number n => intToString n
      | Val_bool b   => Bool.toString b
      | Val_string s => escape s
      | Val_unit     => "()"
      | Val_nil      => "[]"
      | Val_pair (a, b) => "(" ^ showValue a ^ ", " ^ showValue b ^ ")"
      | Val_cons _   => "[" ^ showList v ^ "]"
      | Val_closure _ => "<fun>"
      | Val_primitive _ => "<fun>"

and showList (Val_cons (h, t)) =
      (case t of
           Val_nil => showValue h
         | Val_cons _ => showValue h ^ "; " ^ showList t
         | _ => showValue h ^ "; " ^ showValue t)
  | showList v = showValue v

val name_of_variables = ref ([] : (tyvar * string) list)
val count_of_variables = ref 0

fun var_name vv =
    assoc vv (!name_of_variables)
    handle Not_found =>
      let val n = !count_of_variables
          val name = if n < 26
                     then "'" ^ String.str (Char.chr (Char.ord #"a" + n))
                     else "'t" ^ Int.toString n
      in count_of_variables := n + 1;
         name_of_variables := (vv, name) :: !name_of_variables;
         name
      end

fun showType ty =
    case shorten ty of
        VarType vv => var_name vv
      | Term (c, []) => c
      | Term (c, [t]) => showType t ^ " " ^ c
      | Term (c, [t1, t2]) =>
          "(" ^ showType t1 ^ " " ^ c ^ " " ^ showType t2 ^ ")"
      | Term (c, args) =>
          "(" ^ String.concatWith ", " (List.map showType args) ^ ") " ^ c

fun showTypeTop ty =
    (name_of_variables := []; count_of_variables := 0; showType ty)

fun showSchema ({ parameters, bodys } : schema) =
    (name_of_variables := []; count_of_variables := 0;
     (if null parameters then ""
      else "for all " ^ String.concatWith " " (List.map var_name parameters)
           ^ ", ")
     ^ showType bodys)


(* ================================================================
   8.  Initial environments
   ================================================================ *)

fun prim_arith name f =
    Val_primitive (name,
      fn Val_pair (Val_number a, Val_number b) => Val_number (f (a, b))
       | _ => raise Eval_error (name ^ ": two integers expected"))

fun prim_cmp name test =
    Val_primitive (name,
      fn Val_pair (a, b) => Val_bool (test (val_compare (a, b)))
       | _ => raise Eval_error (name ^ ": a pair expected"))

fun safe_div name f =
    fn (a, b) => if IntInf.sign b = 0
                 then raise Eval_error "division by zero"
                 else f (a, b)

val val_env_initial = [
    ("+",   prim_arith "+" IntInf.+),
    ("-",   prim_arith "-" IntInf.-),
    ("*",   prim_arith "*" IntInf.* ),
    ("/",   prim_arith "/" (safe_div "/" IntInf.div)),
    (* OCaml's `mod' is the remainder of a truncated division, so its
       sign follows the dividend: (-7) mod 3 = -1.  SML's `mod' floors
       instead and would give 2, so we use IntInf.rem here. *)
    ("mod", prim_arith "mod" (safe_div "mod" IntInf.rem)),
    ("=",   prim_cmp "="  (fn r => r = EQUAL)),
    ("<>",  prim_cmp "<>" (fn r => r <> EQUAL)),
    ("<",   prim_cmp "<"  (fn r => r = LESS)),
    (">",   prim_cmp ">"  (fn r => r = GREATER)),
    ("<=",  prim_cmp "<=" (fn r => r <> GREATER)),
    (">=",  prim_cmp ">=" (fn r => r <> LESS)),
    ("^",   Val_primitive ("^",
              fn Val_pair (Val_string a, Val_string b) => Val_string (a ^ b)
               | _ => raise Eval_error "^: two strings expected")),
    ("not", Val_primitive ("not",
              fn Val_bool b => Val_bool (not b)
               | _ => raise Eval_error "not: a boolean expected")),
    ("hd",  Val_primitive ("hd",
              fn Val_cons (h, _) => h
               | _ => raise Eval_error "hd: empty list")),
    ("tl",  Val_primitive ("tl",
              fn Val_cons (_, t) => t
               | _ => raise Eval_error "tl: empty list")),
    ("fst", Val_primitive ("fst",
              fn Val_pair (a, _) => a
               | _ => raise Eval_error "fst: a pair expected")),
    ("snd", Val_primitive ("snd",
              fn Val_pair (_, b) => b
               | _ => raise Eval_error "snd: a pair expected")),
    ("string_of_int", Val_primitive ("string_of_int",
              fn Val_number n => Val_string (intToString n)
               | _ => raise Eval_error "string_of_int: an integer expected")),
    ("print_string", Val_primitive ("print_string",
              fn Val_string s => (print s; Val_unit)
               | _ => raise Eval_error "print_string: a string expected")),
    ("print_int", Val_primitive ("print_int",
              fn Val_number n => (print (intToString n); Val_unit)
               | _ => raise Eval_error "print_int: an integer expected")),
    ("print_newline", Val_primitive ("print_newline",
              fn _ => (print "\n"; Val_unit))),
    ("write_int", Val_primitive ("write_int",
              fn Val_number n => (print (intToString n ^ "\n"); Val_number n)
               | _ => raise Eval_error "write_int: an integer expected")),
    (* ---- 文字列を分解するための組み込み ---- *)
    ("size", Val_primitive ("size",
              fn Val_string s => Val_number (IntInf.fromInt (String.size s))
               | _ => raise Eval_error "size: a string expected")),
    ("sub", Val_primitive ("sub",          (* sub s i : i 文字目の 1 文字 *)
              fn Val_string s => Val_primitive ("sub",
                   fn Val_number i =>
                        let val k = IntInf.toInt i handle Overflow => ~1
                        in if k < 0 orelse k >= String.size s
                           then raise Eval_error "sub: index out of range"
                           else Val_string (String.str (String.sub (s, k)))
                        end
                    | _ => raise Eval_error "sub: an integer expected")
               | _ => raise Eval_error "sub: a string expected")),
    ("ord", Val_primitive ("ord",          (* 先頭 1 文字の文字コード *)
              fn Val_string s =>
                   if String.size s = 0 then raise Eval_error "ord: empty string"
                   else Val_number (IntInf.fromInt (Char.ord (String.sub (s, 0))))
               | _ => raise Eval_error "ord: a string expected")),
    ("chr", Val_primitive ("chr",
              fn Val_number n =>
                   let val k = IntInf.toInt n handle Overflow => ~1
                   in if k < 0 orelse k > 255
                      then raise Eval_error "chr: out of range"
                      else Val_string (String.str (Char.chr k))
                   end
               | _ => raise Eval_error "chr: an integer expected")),
    ("explode", Val_primitive ("explode",   (* 1 文字ずつの文字列のリストへ *)
              fn Val_string s =>
                   List.foldr (fn (c, acc) => Val_cons (Val_string (String.str c), acc))
                              Val_nil (String.explode s)
               | _ => raise Eval_error "explode: a string expected")),
    ("implode", Val_primitive ("implode",
              fn v =>
                let fun go Val_nil acc = String.concat (List.rev acc)
                      | go (Val_cons (Val_string s, t)) acc = go t (s :: acc)
                      | go _ _ = raise Eval_error "implode: a list of strings expected"
                in Val_string (go v []) end)),
    ("quit", Val_primitive ("quit", fn _ => raise End_of_system))
]

val type_arithmetic =
    schema_trivial (type_arrow (type_product type_int type_int) type_int)
val type_comparison =
    poly1 (fn a => type_arrow (type_product a a) type_bool)

val type_env_initial = [
    ("+", type_arithmetic), ("-", type_arithmetic), ("*", type_arithmetic),
    ("/", type_arithmetic), ("mod", type_arithmetic),
    ("=", type_comparison), ("<>", type_comparison),
    ("<", type_comparison), (">", type_comparison),
    ("<=", type_comparison), (">=", type_comparison),
    ("^", schema_trivial
            (type_arrow (type_product type_string type_string) type_string)),
    ("not", schema_trivial (type_arrow type_bool type_bool)),
    ("hd",  poly1 (fn a => type_arrow (type_list a) a)),
    ("tl",  poly1 (fn a => type_arrow (type_list a) (type_list a))),
    ("fst", poly2 (fn a => fn b => type_arrow (type_product a b) a)),
    ("snd", poly2 (fn a => fn b => type_arrow (type_product a b) b)),
    ("string_of_int", schema_trivial (type_arrow type_int type_string)),
    ("print_string", schema_trivial (type_arrow type_string type_unit)),
    ("print_int", schema_trivial (type_arrow type_int type_unit)),
    ("print_newline", schema_trivial (type_arrow type_unit type_unit)),
    ("write_int", schema_trivial (type_arrow type_int type_int)),
    ("size", schema_trivial (type_arrow type_string type_int)),
    ("sub", schema_trivial (type_arrow type_string (type_arrow type_int type_string))),
    ("ord", schema_trivial (type_arrow type_string type_int)),
    ("chr", schema_trivial (type_arrow type_int type_string)),
    ("explode", schema_trivial (type_arrow type_string (type_list type_string))),
    ("implode", schema_trivial (type_arrow (type_list type_string) type_string)),
    ("quit", poly1 (fn a => type_arrow type_unit a))
]


(* ================================================================
   9.  The read-eval-print loop
   ================================================================ *)

val trace = ref false           (* set to true to dump the parsed AST *)

fun repl (ins, prompt) =
    let
      val st = mkstate ins
      val type_env = ref type_env_initial
      val val_env = ref val_env_initial

      fun say s = (print s; TextIO.flushOut TextIO.stdOut)

      (* resynchronise after an error: drop tokens up to the next `;'.
         Lexing may itself fail here (an unterminated string, say), in
         which case we simply give up on resynchronising. *)
      fun resync () =
          (while cur st <> TOP ";" andalso cur st <> TEOF do advance st)
          handle Lex_error _ => ()

      fun step () =
          (if prompt then say "## " else ();
           advance st;
           while isOp st ";" do advance st;
           let val phrase = parse_phrase st
           in
             if isOp st ";" then ()
             else expected st "`;' at the end of the phrase";
             if !trace then say ("[ast] " ^ showDefinition phrase ^ "\n") else ();
             case phrase of
                 Expr e =>
                   let val ty = type_exp (!type_env) e
                       val v  = eval (!val_env) e
                   in say ("- : " ^ showTypeTop ty ^ " = " ^ showValue v ^ "\n")
                   end
               | Def (r, n, e) =>
                   let val tenv = type_def (!type_env) (r, n, e)
                       val venv = value_definition (!val_env) (r, n, e)
                   in case (tenv, venv) of
                          ((_, sch) :: _, (_, v) :: _) =>
                            say (n ^ " : " ^ showSchema sch
                                 ^ " = " ^ showValue v ^ "\n")
                        | _ => ();
                      type_env := tenv;
                      val_env := venv
                   end
           end
           handle
               Syntax_error m => (say ("Parse error: " ^ m ^ ".\n"); resync ())
             | Lex_error m    => (say ("Lexical error: " ^ m ^ ".\n"); resync ())
             | Type_error m   => (say ("Type error: " ^ m ^ ".\n"); resync ())
             | Eval_error m   => (say ("Runtime error: " ^ m ^ ".\n"); resync ())
             | Conflict (a, b) =>
                 (say ("Type error: cannot match " ^ showTypeTop a
                       ^ " with " ^ showTypeTop b ^ ".\n"); resync ())
             | Circulation (a, b) =>
                 (say ("Type error: cyclic type, " ^ showTypeTop a
                       ^ " occurs in " ^ showTypeTop b ^ ".\n"); resync ())
             | Fail_filtrate =>
                 (say "Runtime error: pattern matching failed.\n"; resync ())
             (* The two exceptions that must escape and stop the loop. *)
             | End_of_input  => raise End_of_input
             | End_of_system => raise End_of_system
             (* Arithmetic traps raised by the host ML.  Without these the
                whole interpreter would die on, say, an overflowing
                multiplication in a user program. *)
             | Overflow => (say "Runtime error: integer overflow.\n"; resync ())
             | Div      => (say "Runtime error: division by zero.\n"; resync ())
             (* Last resort, so that no user program can ever kill us. *)
             | e => (say ("Runtime error: " ^ exnMessage e ^ ".\n"); resync ()))
    in
      (while true do step ())
      handle End_of_input => print "\n"
           | End_of_system => print "End of MINICAML2.sml...\n"
    end

fun run () = repl (TextIO.stdIn, true)

fun runFile name =
    let val ins = TextIO.openIn name
    in repl (ins, false) handle e => (TextIO.closeIn ins; raise e);
       TextIO.closeIn ins
    end

(* Entry point for a standalone executable built with
     $ polyc -o minicaml2 minicaml2.sml
   With no argument it starts the interactive loop, otherwise it runs
   each file given on the command line. *)
fun main () =
    case CommandLine.arguments () of
        [] => run ()
      | files => List.app runFile files

val () = print "MINICAML2 ready.  Type  run ();  or  runFile \"demo.mml\";\n"
