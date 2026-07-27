use "minicaml_fixed9.sml";

val type_env = ref type_env_initial;
val val_env = ref Val_env_initial;

fun runOne phrase =
  case phrase of
      Expr expr =>
        let
          val ty = type_exp (!type_env) expr
          val ret = Eval (!val_env) expr
        in
          print "- : "; display_type ty;
          print " = "; display_value ret; print "\n"
        end
    | Def def =>
        let
          val new_type_env = type_def (!type_env) def
          val new_val_env = Value_definition (!val_env) def
        in
          case (new_type_env, new_val_env) of
              (((name, schema) :: _), ((_, v) :: _)) =>
                (print (name ^ " : "); display_schema schema;
                 print " = "; display_value v; print "\n");
          type_env := new_type_env;
          val_env := new_val_env
        end;

fun loop ins =
  (runOne (read_phrase ins); loop ins)
  handle End_of_system => ()
       | Syntax_error => (print "Parse error: Syntax error.\n"; loop ins)
       | Cant_close_parenthesis =>
           (print "Parse error: Can't find the right parenthesis.\n"; loop ins)
       | Type_Error str => (print "Type check error: "; print str; print "\n"; loop ins)
       | Eval_Error str => (print "Eval error: "; print str; print "\n"; loop ins)
       | Conflict (sty1, sty2) =>
           (print "Type check error: Incompatible in types entry ";
            display_type sty1; print " with "; display_type sty2; print "\n"; loop ins)
       | Circulation (sty1, sty2) =>
           (print "Type check error: Impossible for identifier ";
            display_type sty1; print " and "; display_type sty2; print "\n"; loop ins);

val ins = TextIO.openIn "self_eval_sample.mml";
val _ = loop ins;
val _ = TextIO.closeIn ins;
