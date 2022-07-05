signature ALPHABET_SCENE_SPACES =
sig
  val mk_alpha_scene_space: string -> theory -> theory
end;

structure Alphabet_Scene_Spaces : ALPHABET_SCENE_SPACES =
struct

open Syntax;
open Lens_Lib;
open HOLogic;

fun alpha_scene_space_term xs more parent =
  let val vs = map (fn x => (const @{const_name lens_scene}) $ const x) xs
  in const @{const_name alpha_scene_space'} $ mk_list dummyT vs  $ const more $ const parent
  end;
 
val basis_lens_suffix = "_basis_lens"

fun mk_basis_lens t = mk_Trueprop (const @{const_name basis_lens} $ t)

fun basis_lens_proof x thy =
  let open Simplifier; open Global_Theory; open Syntax in
      Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [mk_basis_lens (const x)]))
      (fn {context = _, prems = _}
                           => (fn ctx => NO_CONTEXT_TACTIC ctx (Method_Closure.apply_method ctx @{method basis_lens} [] [] [] ctx [])) (Proof_Context.init_global thy))
  end;

fun basis_lenses lnames thy =
  let open Global_Theory; val attrs = map (Attrib.attribute (Named_Target.theory_init thy)) @{attributes [simp, code_unfold, lens]} in
  fold (fn x => fn thy => snd (add_thm ((Binding.make (Long_Name.base_name x ^ basis_lens_suffix, Position.none), basis_lens_proof x thy), attrs) thy)) lnames thy 
  end;


fun frame_UNIV_term xs more =
  let open Syntax; open HOLogic
  in mk_Trueprop 
     (const @{const_name HOL.eq} 
     $ const @{const_abbrev frame_UNIV}
     $ (const @{const_abbrev frame_union}
       $ fold_rev (fn x => fn y => const @{const_name lens_insert} $ const x $ y) xs (const @{const_abbrev frame_empty})
       $ (const @{const_name more_frame} $ const more)))
  end

fun frame_more_term xs more parent =
  let open Syntax; open HOLogic
  in mk_Trueprop 
     (const @{const_name HOL.eq} 
     $ (const @{const_name more_frame} $ (const parent))
     $ (const @{const_abbrev frame_union}
       $ fold_rev (fn x => fn y => const @{const_name lens_insert} $ const x $ y) xs (const @{const_abbrev frame_empty})
       $ (const @{const_name more_frame} $ const more)))
  end

fun frame_UNIV_proof xs more thy =
  let open Simplifier; open Global_Theory; open Syntax in
      Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [frame_UNIV_term xs more]))
      (fn {context = context, prems = _}
                           => (fn ctx => NO_CONTEXT_TACTIC ctx (Method_Closure.apply_method ctx @{method more_frame} [] [] [] ctx [])) (Proof_Context.init_global thy))
  end;

fun frame_more_proof xs more parent thy =
  let open Simplifier; open Global_Theory; open Syntax in
      Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [frame_more_term xs more parent]))
      (fn {context = context, prems = _}
                           => (fn ctx => NO_CONTEXT_TACTIC ctx (Method_Closure.apply_method ctx @{method more_frame} [] [] [] ctx [])) (Proof_Context.init_global thy))
  end;

fun frame_UNIV tname xs more thy =
  let open Global_Theory; val attrs = map (Attrib.attribute (Named_Target.theory_init thy)) @{attributes [frame]} in  
  snd (add_thm ((Binding.make (Long_Name.base_name tname ^ "_frame_UNIV", Position.none), frame_UNIV_proof xs more thy), attrs) thy)
  end

fun frame_more tname xs more parent thy =
  let open Global_Theory; val attrs = map (Attrib.attribute (Named_Target.theory_init thy)) @{attributes [frame]} in  
  snd (add_thm ((Binding.make (Long_Name.base_name tname ^ "_frame_more", Position.none), frame_more_proof xs more parent thy), attrs) thy)
  end


fun mk_alpha_scene_space tname thy =
  let
  open Syntax
  open Term
  open Proof_Context
  val (Type (qname, _)) = read_type_name {proper = false, strict = false} (init_global thy) tname
  val info = Record.the_info thy qname
  val r_ext = fst (#extension info)
  fun mk_def ty x v = Const ("Pure.eq", ty --> ty --> Term.propT) $ Free (x, ty) $ v;
  val xs = map (Lens_Lib.remove_lens_suffix o fst) (#fields info)
  val ctx0 = Class.instantiation_cmd ([r_ext], ["scene_space"], "scene_space") thy;
  val parent =     
      (case #parent info of
       NONE => @{const_name id_lens} |
       SOME (ts, pname) => (pname ^ ".more\<^sub>L"))
  val (Type (qtname, _)) = Syntax.read_typ ctx0 tname
  val (Const (more, _)) = Syntax.read_term ctx0 (tname ^ ".more\<^sub>L")

  val (_, ctx1) = Local_Theory.begin_nested ctx0

  val def_ty = Syntax.read_typ ctx0 ("'a " ^ r_ext ^ " scene list");
  val (_, ctx2) = Specification.definition (SOME (Binding.name ("Vars_" ^ tname ^ "_ext"), NONE, NoSyn)) [] [] ((Binding.empty, @{attributes [scene_space_defs]}), mk_def def_ty ("Vars_" ^ tname ^ "_ext") (alpha_scene_space_term xs more parent)) ctx1

  val ctx3 = Local_Theory.end_nested ctx2

  val thy2 = Class.prove_instantiation_exit (fn _ => NO_CONTEXT_TACTIC ctx3 (Method_Closure.apply_method ctx3 @{method alpha_scene_space} [] [] [] ctx3 [])) ctx3

  val thy3 = basis_lenses xs thy2

  val thy4 = (if #parent info = NONE then frame_UNIV tname xs more thy3 else frame_more tname xs more parent thy3)

  in thy4 end;

end