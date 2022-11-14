section \<open> Alphabet Scene Spaces \<close>

theory Alphabet_Scene_Spaces
  imports Frames Lens_Instances
  keywords "alphabet_scene_space" :: "thy_defn"
begin

text \<open> The scene space for an alphabet is constructed using the set of scenes corresponding to
  each lens, the base lens, and the more lens, to allow for extension. \<close>

definition alpha_scene_space :: "'s scene list \<Rightarrow> ('b::list_scene_space \<Longrightarrow> 's) \<Rightarrow> 's scene list" where
"alpha_scene_space xs m\<^sub>L = xs @ map (\<lambda> x. x ;\<^sub>S m\<^sub>L) VarList"

definition alpha_scene_space' :: "'s scene list \<Rightarrow> ('b::list_scene_space \<Longrightarrow> 's) \<Rightarrow> ('c \<Longrightarrow> 's) \<Rightarrow> 'c scene list" where
"alpha_scene_space' xs m\<^sub>L p\<^sub>L = alpha_scene_space (map (\<lambda> x. x /\<^sub>S p\<^sub>L) xs) (m\<^sub>L /\<^sub>L p\<^sub>L)"

lemma mem_alpha_scene_space_iff [simp]: 
  "x \<in> set (alpha_scene_space xs m\<^sub>L) \<longleftrightarrow> (x \<in> set xs \<or> x \<in> (\<lambda> x. x ;\<^sub>S m\<^sub>L) ` set VarList)"
  by (simp add: alpha_scene_space_def) 

lemma pairwise_compat_foldr: 
  "\<lbrakk> pairwise (##\<^sub>S) (set as); \<forall> b \<in> set as. a ##\<^sub>S b \<rbrakk> \<Longrightarrow> a ##\<^sub>S foldr (\<squnion>\<^sub>S) as \<bottom>\<^sub>S"
  apply (induct as)
   apply (simp)
  apply (auto simp add: pairwise_insert scene_union_pres_compat)
  done

lemma foldr_compat_dist:
  "pairwise (##\<^sub>S) (set as) \<Longrightarrow> foldr (\<squnion>\<^sub>S) (map (\<lambda>a. a ;\<^sub>S x) as) \<bottom>\<^sub>S = foldr (\<squnion>\<^sub>S) as \<bottom>\<^sub>S ;\<^sub>S x"
  apply (induct as)
   apply (simp)
  apply (auto simp add: pairwise_insert)
  apply (metis pairwise_compat_foldr scene_compat_refl scene_union_comp_distl)
  done  

lemma alpha_scene_space_class_intro:
  assumes 
    "\<forall> x\<in>set xs. idem_scene x"
    "scene_indeps (set xs)"
    "vwb_lens m\<^sub>L" \<comment> \<open> The more lens \<close>
    "\<forall> x\<in>set xs. x \<bowtie>\<^sub>S \<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim>"  
    "(foldr (\<squnion>\<^sub>S) xs \<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim>) = \<top>\<^sub>S"
  shows "class.list_scene_space (set (alpha_scene_space xs m\<^sub>L)) (alpha_scene_space xs m\<^sub>L)"
proof (simp add: alpha_scene_space_def, unfold_locales)
  show idem: "\<And>x. x \<in> set (xs @ map (\<lambda>x. x ;\<^sub>S m\<^sub>L) VarList) \<Longrightarrow> idem_scene x"
    using assms(1) idem_scene_VarList by fastforce
  show indeps: "scene_indeps (set (xs @ map (\<lambda>x. x ;\<^sub>S m\<^sub>L) VarList))"
    apply (auto simp add: scene_indeps_def pairwise_def)
    apply (metis assms(2) pairwiseD scene_indeps_def)
    using assms(1) assms(4) idem_scene_VarList scene_comp_pres_indep apply blast
    using assms(1) assms(4) idem_scene_VarList scene_comp_pres_indep scene_indep_sym apply blast
    using Vars_VarList Vars_ext_lens_indep apply blast
    done
  have cf: "compat_family (set (xs @ map (\<lambda>x. x ;\<^sub>S m\<^sub>L) VarList))"
    by (metis List.finite_set idem indep_family_def indep_implies_compat_family indeps scene_indeps_def)

  show "scene_span (set (xs @ map (\<lambda>x. x ;\<^sub>S m\<^sub>L) VarList))"
    unfolding scene_span_def
    apply (subst foldr_scene_via_foldr)
    apply (rule cf)
    apply (simp)
    apply (subst foldr_compat_dist)
    apply (metis Vars_VarList scene_space_compats)
    apply (metis Vars_VarList assms(3) assms(5) compat_family.intro finite_Vars foldr_scene_via_foldr idem_scene_VarList scene_comp_top_scene scene_space_compats top_scene_eq)    
    done
qed (simp)

lemma alpha_scene_space_class_intro':
  assumes 
    "\<forall> x\<in>set xs. idem_scene x"
    "scene_indeps (set xs)"
    "vwb_lens m\<^sub>L" \<comment> \<open> The more lens \<close>
    "vwb_lens p\<^sub>L" \<comment> \<open> The parent more lens \<close>
    "m\<^sub>L \<subseteq>\<^sub>L p\<^sub>L"
    "\<forall>a\<in>set xs. a \<subseteq>\<^sub>S \<lbrakk>p\<^sub>L\<rbrakk>\<^sub>\<sim>"
    "\<forall> x\<in>set xs. x \<bowtie>\<^sub>S \<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim>"
    "foldr (\<squnion>\<^sub>S) xs \<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim> = \<lbrakk>p\<^sub>L\<rbrakk>\<^sub>\<sim>"
  shows "class.scene_space (alpha_scene_space' xs m\<^sub>L p\<^sub>L)"
  unfolding alpha_scene_space'_def
  apply (rule alpha_scene_space_class_intro)
      apply (simp_all add: assms scene_quotient_idem)
  apply (simp add: scene_indeps_def pairwise_def )
  apply (metis assms(2) pairwiseD scene_indeps_def scene_quotient_indep)
  using assms(3) assms(4) assms(5) lens_quotient_vwb apply blast
   apply (simp add: assms lens_scene_quotient scene_quotient_indep)
  apply (subst foldr_scene_union_add_tail[THEN sym])
  apply (simp)
  apply (metis (mono_tags, lifting) assms(2) pairwiseD pairwise_imageI scene_indep_compat scene_indeps_def scene_quotient_indep)
  apply (simp add: assms(4) assms(5) assms(7) lens_scene_quotient scene_quotient_indep)
  apply (subst foldr_compat_quotient_dist)
  apply (metis assms(2) pairwise_alt scene_indep_compat scene_indeps_def)
  using assms(6) apply blast
  apply (simp add: lens_scene_quotient assms)
  apply (subst scene_union_quotient[THEN sym])
  apply (metis assms(2) assms(3) assms(4) assms(5) assms(7) assms(8) bot_idem_scene empty_iff foldr.simps(1) foldr_scene_union_add_tail id_apply list.set(1) order_eq_refl pairwise_compat_foldr pairwise_empty pairwise_mono scene_bot_least scene_indep_compat scene_indeps_def scene_union_incompat sublens'_implies_subscene sublens_implies_sublens' subscene_antisym)
  apply (metis assms(2) assms(6) foldr_scene_indep pairwise_def scene_indep_compat scene_indep_sym scene_indeps_def scene_le_iff_indep_inv)
  apply (simp add: assms(3) assms(4) assms(5) sublens'_implies_subscene sublens_implies_sublens')
  apply (subst foldr_scene_union_add_tail)
  apply (metis assms(2) pairwiseD pairwiseI scene_indep_compat scene_indeps_def)
  using assms(7) scene_indep_compat apply blast
  apply (simp add: assms(8))
  apply (metis assms(4) scene_comp_quotient scene_comp_top_scene)
  done

lemma alpha_scene_space_class_intro'':
  assumes 
    "\<forall> x\<in>set (concat xs). idem_scene x"
    "scene_indeps (set (concat xs))"
    "vwb_lens m\<^sub>L" \<comment> \<open> The more lens \<close>
    "vwb_lens p\<^sub>L" \<comment> \<open> The parent more lens \<close>
    "m\<^sub>L \<subseteq>\<^sub>L p\<^sub>L"
    "\<forall>a\<in>set (concat xs). a \<subseteq>\<^sub>S \<lbrakk>p\<^sub>L\<rbrakk>\<^sub>\<sim>"
    "\<forall> x\<in>set (concat xs). x \<bowtie>\<^sub>S \<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim>"
    "\<Squnion>\<^sub>S (map \<Squnion>\<^sub>S xs @ [\<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim>]) = \<lbrakk>p\<^sub>L\<rbrakk>\<^sub>\<sim>"
  shows "class.scene_space (alpha_scene_space' (concat xs) m\<^sub>L p\<^sub>L)"
proof -
  have p1: "pairwise (##\<^sub>S) (set (concat xs))"
    by (metis assms(2) pairwise_def scene_indep_compat scene_indeps_def)
  have p2: "pairwise (##\<^sub>S) (set (concat xs @ [\<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim>]))"
    by (metis (no_types, lifting) assms(7) insertE list.simps(15) p1 pairwise_def rotate1.simps(2) scene_compat_sym scene_indep_compat set_rotate1)
  have "foldr (\<squnion>\<^sub>S) (concat xs) \<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim> = \<Squnion>\<^sub>S (concat (xs @ [[\<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim>]]))"
    by simp
  also have "... = \<Squnion>\<^sub>S (map \<Squnion>\<^sub>S (xs @ [[\<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim>]]))"
    by (metis append_self_conv concat.simps(2) concat_append foldr_scene_concat p2)
  also have "... = foldr (\<squnion>\<^sub>S) (map \<Squnion>\<^sub>S xs) \<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim>"
    by simp
  finally show ?thesis
    using assms by (rule_tac alpha_scene_space_class_intro', simp_all)
qed

definition more_frame :: "('a::scene_space \<Longrightarrow> 'b::scene_space) \<Rightarrow> 'b frame" where
"more_frame m\<^sub>L = \<Union>\<^sub>F ((\<lambda>x. [x ;\<^sub>S m\<^sub>L]\<^sub>F) ` set Vars)"

lemma more_frame_unit [simp]: "more_frame (m\<^sub>L :: unit \<Longrightarrow> 'b::scene_space) = \<lbrace>\<rbrace>\<^sub>F"
  by (simp add: more_frame_def)

named_theorems scene_space_defs

lemmas scene_space_lemmas =
   lens_plus_scene[THEN sym] lens_equiv_scene[THEN sym] lens_equiv_sym
   lens_scene_comp[THEN sym] lens_quotient_vwb lens_quotient_comp
   comp_vwb_lens lens_comp_assoc[THEN sym] sublens_iff_subscene[THEN sym] 
   lens_scene_quotient[THEN sym] sublens_greatest lens_quotient_id_denom
   scene_comp_assoc lens_quotient_indep lens_quotient_plus[THEN sym] lens_quotient_bij 
   plus_pred_sublens lens_scene_top_iff_bij_lens lens_indep_scene[THEN sym]
   lens_indep_left_ext lens_indep_right_ext

method basis_lens uses defs =
  (rule basis_lens_intro, simp_all add: scene_space_defs alpha_scene_space_def alpha_scene_space'_def scene_space_lemmas)

method composite_lens =
  (rule composite_lens.intro, simp, rule composite_lens_axioms.intro
  ,simp add: scene_space_defs alpha_scene_space_def alpha_scene_space'_def scene_space_lemmas image_comp)

method more_frame = 
  ((simp add: frame_scene_top frame_scene_foldr)?
  ,(simp_all add: frame_scene_top frame_scene_foldr alpha_scene_space'_def alpha_scene_space_def scene_space_lemmas more_frame_def scene_space_defs image_comp))

method alpha_scene_space = 
  (rule scene_space_class.intro
  ,(intro_classes)[1]
  ,simp add: scene_space_defs lens_scene_quotient
  ,rule alpha_scene_space_class_intro alpha_scene_space_class_intro'
  ,simp_all add: scene_indeps_def pairwise_def scene_space_lemmas)

ML_file \<open>Alphabet_Scene_Spaces.ML\<close>

ML \<open>

val _ =
  Outer_Syntax.command @{command_keyword alphabet_scene_space} "define a scene space for an alphabet"
    (Parse.name
    >> (fn n =>
        Toplevel.theory (Alphabet_Scene_Spaces.mk_alpha_scene_space n)));


\<close>

end