signature CHANNEL_TYPE =
sig
  val ctor_suffix: string
  val compile_chantype: ((binding option * (string * string option)) list * string) * (string * string) list -> theory -> theory
  val make_chantype: string list -> sort list -> string -> (string * string) list -> theory -> theory
end;

structure Channel_Type : CHANNEL_TYPE =
struct

fun 
  add_typerep_tfrees (Type (n, ts)) = Type (n, map add_typerep_tfrees ts) |
  add_typerep_tfrees (TFree (n, sorts)) = TFree (n, sorts @ @{sort typerep}) |
  add_typerep_tfrees (TVar (n, sorts)) = TVar (n, sorts @ @{sort typerep})

val wb_prism_suffix = "_wb_prism"

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

fun def typ qual (x, tm) ctx = 
  let open Specification; open Syntax
      val ((_, (_, thm)), d) = definition (SOME (Binding.qualify false qual (Binding.name x), SOME typ, NoSyn)) [] [] ((Binding.empty, @{attributes [lens_defs, chan_defs]}), mk_def typ x tm) ctx
  in (thm, d)  
  end

fun defs typ qual inds f ctx =
  fold (fn i => fn (thms, ctx) =>
        let val (thm, ctx') = def typ qual (i, f i) ctx 
        in (thms @ [thm], ctx') end) inds ([], ctx)

fun mk_chantyperep chans ctx = 
  let open HOLogic; open Syntax; open Proof_Context  
  fun mk_chanrep (n, t) =
      let val c = 
          case read_const {proper = false, strict = false} ctx (is_prefix ^ n ^ ctor_suffix)
          of Free (c', _) => free c' | Const (c', _) => const c' | _ => raise Match;
      in   
        (const @{const_name Chanrep} 
         $ mk_literal n $ t 
         $ c)
      end
  in
  mk_list dummyT (map mk_chanrep chans)
  end

fun chantyperep_def name raw_chans ct vmap ctx = 
  let  
  open Syntax; open HOLogic; open Global_Theory; open Proof_Context
  val ty = read_type_name {proper = true, strict = false} ctx name;
  fun repl_tvars ty = map_type_tfree (fn (n, s) => TFree (the (AList.lookup (op =) vmap n), s)) ty
  val chans = map (fn (n, t) => (n, mk_typerep (repl_tvars (read_typ ctx t)))) raw_chans
  val lhs = ct $ Free ("T", Term.itselfT ty);
  val rhs = mk_chantyperep chans ctx;
  val eq = check_term ctx (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)));
  in snd (Specification.definition NONE [] [] ((Binding.empty, @{attributes [chantyperep_defs]}), eq) ctx)
  end;

fun chantyperep_instance raw_vars vars sorts name raw_chans thy =
  let  
  open Syntax; open HOLogic; open Global_Theory;
  val vmap = ListPair.zip (raw_vars, vars)
  val tvars = ListPair.zip (vars, sorts)
  val ty = Proof_Context.read_type_name {proper = true, strict = false} (Named_Target.theory_init thy) name;
  val tyco = fst (dest_Type ty);
  val ctx0 = Class.instantiation ([tyco], tvars, \<^sort>\<open>chantyperep\<close>) thy;
  val ctx1 = snd (Local_Theory.begin_nested ctx0)
  val ty' = Type (tyco, map (read_typ ctx1) vars) 
  val ctx2 = chantyperep_def name raw_chans \<^Const>\<open>chantyperep ty'\<close> vmap ctx1
  val ctx3 = Local_Theory.end_nested ctx2;
  val disc_thms = if length raw_chans = 1 then [] else get_thms thy (tyco ^ ".discI")
  val exhaust_disc_thms = if length raw_chans = 1 then [] else get_thms thy (tyco ^ ".exhaust_disc")
  val ctx4 = fold (Context.proof_map o Named_Theorems.add_thm "Channel_Type.disc_thms") disc_thms ctx3;
  val ctx5 = fold (Context.proof_map o Named_Theorems.add_thm "Channel_Type.exhaust_disc_thms") exhaust_disc_thms ctx4;
  in                                                                                                              
  Class.prove_instantiation_exit (fn _ => NO_CONTEXT_TACTIC ctx5 (Method_Closure.apply_method ctx5 @{method chantyperep_inst} [] [] [] ctx5 [])) ctx5
  end;

fun make_chantype tvars sorts name chans thy =
  let 
    open BNF_FP_Def_Sugar; open BNF_FP_Rec_Sugar_Util; open BNF_LFP; open Ctr_Sugar
    open Prism_Lib; open Lens_Lib; open Local_Theory; open Specification; open Syntax; open HOLogic; open Global_Theory
    val ctx = Named_Target.theory_init thy;
    val ctrs = map (fn (n, t) => (((Binding.empty, Binding.name (n ^ ctor_suffix)), [(Binding.empty, add_typerep_tfrees (read_typ ctx t))]), Mixfix.NoSyn)) chans 

    val pnames = map fst chans
    val thypfx = 
      case (Named_Target.locale_of ctx) of
        SOME loc => loc ^ "." |
        NONE => Context.theory_name {long = false} (Local_Theory.exit_global ctx) ^ "."
    val prefix = thypfx ^ name ^ "."
    val attrs = @{attributes [simp, code_unfold]}
    val dummy_disc = absdummy dummyT @{term True}
    val cdtvars = map (fn (v, s) => (NONE, (TFree (v, []), s))) (ListPair.zip (tvars, sorts)) 
    val ctx1 = co_datatypes Least_FP construct_lfp 
               ((Plugin_Name.default_filter, true), [(((((cdtvars, Binding.name name), Mixfix.NoSyn), ctrs), (Binding.empty, Binding.empty, Binding.empty)),[])]) ctx
    val typ = Proof_Context.read_type_name {proper = true, strict = false} ctx1 name
    val tyco = fst (dest_Type typ);
    val typ' = Type (tyco, map TFree (ListPair.zip (tvars, sorts))) 
    val ptyp = prismT dummyT typ'
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
  (* The datatype also does not produce a discriminator when the length is 1 *)
  #> (if (length pnames = 1)
      then abbreviation
             Syntax.mode_default (SOME (Binding.qualify false name (Binding.name (is_prefix ^ nth pnames 0 ^ ctor_suffix)), NONE, NoSyn)) [] 
             (mk_def dummyT 
                (is_prefix ^ nth pnames 0 ^ ctor_suffix) 
                (Abs ("x", typ, @{term "True"}))) false
      else I)
  #> defs ptyp name pnames (fn x => (const @{const_name ctor_prism}
                         $ const (prefix ^ x ^ ctor_suffix)
                         $ (if (length pnames = 1) then dummy_disc else const (prefix ^ is_prefix ^ x ^ ctor_suffix))
                         $ const (prefix ^ un_prefix ^ x ^ ctor_suffix)))
  #> (fn (thms, ctx) =>
       (fold (fn x => fn thy => snd (note ((Binding.qualify false name (Binding.name (x ^ wb_prism_suffix)), attrs), [wb_prism_proof x thms thy]) thy)) pnames
       #> (snd o note ((Binding.qualify false name (Binding.name codepsN), attrs), map (codep_proof thms ctx) (pairings pnames)))
       ) ctx)
  #> Local_Theory.exit_global)
  ctx1
  end;

fun prism_has_chanrep n ctx =
  let open Syntax; open HOLogic
      val c = parse_term ctx n in
  Trueprop $ (const @{const_name has_chanrep} $ c)                         
  end

fun prism_has_chanrep_proof ctx (n, t) =
  let open Simplifier; open Prism_Lib; open Syntax; open HOLogic
      val d = read_term ctx ("is_" ^ n ^ "_C")
      val ct = Syntax.check_term ctx ((const @{const_name Chanrep} $ mk_literal n $ mk_typerep (add_typerep_tfrees (read_typ ctx t))) $ d)
  in
      Goal.prove ctx [] []
      (Syntax.check_term ctx (prism_has_chanrep n ctx))
      (fn _ => NO_CONTEXT_TACTIC ctx (Method_Closure.apply_method ctx @{method prism_has_chanrep} [ct] [] [] ctx []))
  end

fun prism_chanrep n t ctx =
  let open Syntax; open HOLogic
      val c = read_term ctx n; val d = read_term ctx ("is_" ^ n ^ "_C") 
      val ct = ((const @{const_name Chanrep} $ mk_literal n $ mk_typerep (add_typerep_tfrees t)) $ d) in
  Trueprop $ (eq_const dummyT $ (const @{const_name chanrep_of} $ c) $ ct)
  end

fun prism_chanrep_proof ctx (n, t) =
  let open Simplifier; open Prism_Lib; open Syntax 
  in
      Goal.prove ctx [] []
      (Syntax.check_term ctx (prism_chanrep n (read_typ ctx t) ctx))
      (fn _ => NO_CONTEXT_TACTIC ctx (Method_Closure.apply_method ctx @{method prism_chanrep} [] [] [] ctx []))
  end

fun prism_chanrep_proofs (name, chans) thy =
  let val ctx = Named_Target.theory_init thy 
  in
  Local_Theory.exit_global (snd (Local_Theory.note ((Binding.qualify false name (Binding.name "prism_chanreps")
                           , @{attributes [simp, code_unfold]}), map (prism_has_chanrep_proof ctx) chans @ map (prism_chanrep_proof ctx) chans) ctx))
  end

fun compile_chantype ((raw_tvars, name), raw_chans) thy =
  let
  open Syntax; 
  val ctx = Named_Target.theory_init thy;
  val tvars = map (fn n => "'" ^ Char.toString (Char.chr n)) (97 upto (96 + length raw_tvars)); 
  val sorts = map (fn t => case snd (snd t) of SOME s => read_sort ctx s @ @{sort typerep} | NONE => @{sort typerep}) raw_tvars
  in
  (make_chantype (map (fst o snd) raw_tvars) sorts name raw_chans #>
  (* Generate chantyperep instance *)
  chantyperep_instance (map (fst o snd) raw_tvars) tvars sorts name raw_chans #>
  (* Generate representations for each prism (channel) *)
  prism_chanrep_proofs (name, raw_chans)) thy
  end

end;

let open Parse; open Parse_Spec; open Scan in
  Outer_Syntax.command @{command_keyword chantype} "define a channel datatype"
    ((( BNF_Util.parse_type_args_named_constrained -- name) --
      (@{keyword "="} |-- repeat1 (name -- ($$$ "::" |-- !!! typ))))
    >> (fn x => Toplevel.theory (Channel_Type.compile_chantype x)))
  end;