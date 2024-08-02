structure Channel_Type =
struct
fun prove_prism_goal thy =
  let 
    open Simplifier; open Global_Theory; open Lens_Lib
    val ctx = Named_Target.theory_init thy
 in
  auto_tac (fold add_simp (get_thms thy lens_defsN) ctx)
end

val wb_prism_suffix = "_wb_prism"
val codep_suffix = "_codeps"

val ctor_suffix = "_C"

fun wb_prism_proof x thms ctx =
  let open Simplifier; open Prism_Lib; open Syntax 
  in
      Goal.prove ctx [] []
      (Syntax.check_term ctx (mk_wb_prism (free x)))
      (fn {context = context, prems = _}
                           => EVERY [ PARALLEL_ALLGOALS (full_simp_tac (fold add_simp thms context))
                                    , Classical.rule_tac context [@{thm wb_ctor_prism_intro}] [] 1
                                    , auto_tac (context delsimprocs [@{simproc unit_eq}])
                                    ])
  end

fun codep_proof thms ctx (x, y) =
  let open Simplifier; open Prism_Lib; open Syntax in
  Goal.prove ctx [] []
      (Syntax.check_term ctx (mk_codep (free x) (free y)))
      (fn {context = context, prems = _}
                           => EVERY [ PARALLEL_ALLGOALS (full_simp_tac (fold add_simp thms context))
                                    , Classical.rule_tac context [@{thm ctor_codep_intro}] [] 1
                                    , auto_tac ctx
                                    ])

  end



fun mk_def ty x v = Const ("Pure.eq", ty --> ty --> Term.propT) $ Free (x, ty) $ v;

val is_prefix = "is_";
val un_prefix = "un_";

fun def qual (x, tm) ctx = 
  let open Specification; open Syntax
      val ((_, (_, thm)), d) = definition (SOME (Binding.qualify false qual (Binding.name x), NONE, NoSyn)) [] [] ((Binding.empty, [Attrib.check_src @{context} (Token.make_src ("lens_defs", Position.none) [])]), mk_def dummyT x tm) ctx
  in (thm, d)  
  end


fun defs qual inds f ctx =
  fold (fn i => fn (thms, ctx) =>
        let val (thm, ctx') = def qual (i, f i) ctx 
        in (thms @ [thm], ctx') end) inds ([], ctx)

fun mk_chantyperep chans ctx = 
  let open HOLogic; open Syntax; open Proof_Context  
  fun mk_chanrep (n, t) =
      let val c = 
          case read_const {proper = false, strict = false} ctx (is_prefix ^ n ^ ctor_suffix)
          of Free (c', _) => free c' | Const (c', _) => const c' | _ => raise Match;
      in  
      (* check_term ctx *) 
        (const @{const_name Chanrep} 
         $ mk_literal n $ t 
         $ c)
      end
  in
  mk_list dummyT (map mk_chanrep chans)
  end

fun chantyperep_instance name raw_chans thy =
  let  
  open Syntax; open HOLogic; open Global_Theory;
  val ty = Syntax.read_typ (Named_Target.theory_init thy) name;
  val tyco = fst (dest_Type ty);
  val disc_intro_thms = if length raw_chans = 1 then [] else get_thms thy (tyco ^ ".disc");
  val disc_elim_thms = if length raw_chans = 1 then [] else get_thms thy (tyco ^ ".exhaust_disc");
  val ctx0 = Class.instantiation ([tyco], [], \<^sort>\<open>chantyperep\<close>) thy;
  val chans = map (fn (n, t) => (n, mk_typerep (read_typ ctx0 t))) raw_chans
  val lhs = \<^Const>\<open>chantyperep ty\<close> $ Free ("T", Term.itselfT ty);
  val rhs = mk_chantyperep chans ctx0;
  val ctx1 = snd (Local_Theory.begin_nested ctx0)
  val eq = check_term ctx1 (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)));
  val (_, ctx2) = Specification.definition NONE [] [] ((Binding.empty, @{attributes [chantyperep_defs]}), eq) ctx1;
  val ctx3 = Local_Theory.end_nested ctx2;
  val ctx4 = fold (Context.proof_map o Named_Theorems.add_thm "Channel_Type.datatype_disc_intros") disc_intro_thms ctx3;
  val ctx5 = fold (Context.proof_map o Named_Theorems.add_thm "Channel_Type.datatype_disc_elims") disc_elim_thms ctx4;
  in
  Class.prove_instantiation_exit (fn _ => NO_CONTEXT_TACTIC ctx5 (Method_Closure.apply_method ctx5 @{method chantyperep_inst} [] [] [] ctx5 [])) ctx5
  end;

fun compile_chantype (name, chans) thy =
  let 
    open BNF_FP_Def_Sugar; open BNF_FP_Rec_Sugar_Util; open BNF_LFP; open Ctr_Sugar
    open Prism_Lib; open Lens_Lib; open Local_Theory; open Specification; open Syntax; open HOLogic
    val ctx = Named_Target.theory_init thy;
    val ctrs = map (fn (n, t) => (((Binding.empty, Binding.name (n ^ ctor_suffix)), [(Binding.empty, t)]), Mixfix.NoSyn)) chans 
    val pnames = map fst chans
    val tyreps = map (mk_typerep o read_typ ctx o snd) chans
    val thypfx = 
      case (Named_Target.locale_of ctx) of
        SOME loc => loc ^ "." |
        NONE => Context.theory_name {long = false} (Local_Theory.exit_global ctx) ^ "."
    val prefix = thypfx ^ name ^ "."
    val attrs = @{attributes [simp, code_unfold]}
    val dummy_disc = absdummy dummyT @{term True}
    val ctx1 = co_datatype_cmd Least_FP construct_lfp 
               ((K Plugin_Name.default_filter, true), 
               [((((([],Binding.name name), Mixfix.NoSyn), ctrs), (Binding.empty, Binding.empty, Binding.empty)),[])]) ctx
    val typ = read_typ ctx1 name
  in
  (
  (* The datatype package does not produce a discriminator for the second constructor when
     there are two constructors. We here generate one for uniformity. *)
    (if (length pnames = 2)
      then abbreviation 
             Syntax.mode_default (SOME (Binding.qualify false name (Binding.name (is_prefix ^ nth pnames 1 ^ ctor_suffix)), NONE, NoSyn)) [] 
             (mk_def dummyT 
                (is_prefix ^ nth pnames 1 ^ ctor_suffix) 
                (const @{const_name comp} $ @{term Not} $ const (prefix ^ is_prefix ^ nth pnames 0 ^ ctor_suffix))) false
      else I)
  (* The datatype also does not produce a discrimator when the length is 1 *)
  #> (if (length pnames = 1)
      then abbreviation
             Syntax.mode_default (SOME (Binding.qualify false name (Binding.name (is_prefix ^ nth pnames 0 ^ ctor_suffix)), NONE, NoSyn)) [] 
             (mk_def dummyT 
                (is_prefix ^ nth pnames 0 ^ ctor_suffix) 
                (Abs ("x", typ, @{term "True"}))) false
      else I)
  #> defs name pnames (fn x => (const @{const_name ctor_prism}
                         $ const (prefix ^ x ^ ctor_suffix)
                         $ (if (length pnames = 1) then dummy_disc else const (prefix ^ is_prefix ^ x ^ ctor_suffix))
                         $ const (prefix ^ un_prefix ^ x ^ ctor_suffix)))
  #> (fn (thms, ctx) =>
       (fold (fn x => fn thy => snd (note ((Binding.qualify false name (Binding.name (x ^ wb_prism_suffix)), attrs), [wb_prism_proof x thms thy]) thy)) pnames
       #> (snd o note ((Binding.qualify false name (Binding.name codepsN), attrs), map (codep_proof thms ctx) (pairings pnames)))
       ) ctx)
  #> Local_Theory.exit_global
  (* Generate chantyperep instance *) 
  #> chantyperep_instance name chans)
  ctx1
  end;

end;

let open Parse; open Parse_Spec; open Scan in
  Outer_Syntax.command @{command_keyword chantype} "define a channel datatype"
    ((name --
      (@{keyword "="} |-- repeat1 (name -- ($$$ "::" |-- !!! typ))))
    >> (fn x => Toplevel.theory (Channel_Type.compile_chantype x)))
  end;