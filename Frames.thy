section \<open> Frames \<close>

theory Frames
  imports Scene_Spaces
begin

subsection \<open> Frame type \<close>

typedef (overloaded) 'a::scene_space frame = "scene_space :: 'a scene set"
  morphisms of_frame mk_frame
  by blast

setup_lifting type_definition_frame

lemma UNIV_frame_scene_space: "UNIV = mk_frame ` scene_space"
  by (metis of_frame of_frame_inverse UNIV_eq_I imageI)

lift_definition frame_scene :: "'s::scene_space scene \<Rightarrow> 's frame" ("\<lbrakk>_\<rbrakk>\<^sub>F")
  is "\<lambda> s. if s \<in> scene_space then s else \<bottom>\<^sub>S"
  by auto

named_theorems frame

instance frame :: (scene_space) finite
  by (intro_classes, simp add: UNIV_frame_scene_space finite_scene_space)

instantiation frame :: (scene_space) order
begin

lift_definition less_eq_frame :: "'a frame \<Rightarrow> 'a frame \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_frame :: "'a frame \<Rightarrow> 'a frame \<Rightarrow> bool" is "(<)" .

instance
  apply (intro_classes; transfer)
     apply (simp add: less_scene_def)
    apply (simp_all add: less_scene_def subscene_refl)
  using idem_scene_space subscene_trans apply auto[1]
  apply (simp add: idem_scene_space subscene_antisym)
  done

end

instantiation frame :: (scene_space) lattice
begin

lift_definition sup_frame :: "'a frame \<Rightarrow> 'a frame \<Rightarrow> 'a frame" is "(\<squnion>\<^sub>S)"
  by (simp add: union_scene_space)

lift_definition inf_frame :: "'a frame \<Rightarrow> 'a frame \<Rightarrow> 'a frame" is "(\<sqinter>\<^sub>S)"
  by (simp add: scene_space_inter)

instance
  apply (intro_classes; transfer)
  apply (metis scene_compl_subset_iff scene_demorgan2 scene_space_inter scene_space_ub scene_space_uminus)
  apply (metis inf_scene_def scene_indep_sym scene_le_iff_indep_inv scene_space_ub scene_space_uminus scene_union_commute)
  apply (metis idem_scene_space scene_compl_subset_iff scene_demorgan2 scene_space_compat scene_space_inter scene_space_uminus scene_union_mono)
  using scene_space_ub apply blast
  apply (simp add: scene_space_ub scene_union_commute)
  apply (meson idem_scene_space scene_space_compat scene_union_mono)
  done

end

abbreviation frame_union :: "'a::scene_space frame \<Rightarrow> 'a frame \<Rightarrow> 'a frame" (infixl "\<union>\<^sub>F" 65) 
  where "frame_union \<equiv> sup"

abbreviation frame_inter :: "'a::scene_space frame \<Rightarrow> 'a frame \<Rightarrow> 'a frame"(infixl "\<inter>\<^sub>F" 70)
  where "frame_inter \<equiv> inf"

lemma frame_scene_union: "\<lbrakk> A \<in> scene_space; B \<in> scene_space \<rbrakk> \<Longrightarrow> \<lbrakk>A \<squnion>\<^sub>S B\<rbrakk>\<^sub>F = \<lbrakk>A\<rbrakk>\<^sub>F \<union>\<^sub>F \<lbrakk>B\<rbrakk>\<^sub>F"
  by (transfer, auto)
  

instantiation frame :: (scene_space) bounded_lattice
begin

lift_definition bot_frame :: "'a frame" is "\<bottom>\<^sub>S" by (simp add: bot_scene_space)
lift_definition top_frame :: "'a frame" is "\<top>\<^sub>S" by (simp add: top_scene_space)

instance by (intro_classes; transfer; simp add: scene_bot_least scene_top_greatest)

end

abbreviation frame_UNIV :: "'s::scene_space frame" ("\<top>\<^sub>F")
  where "\<top>\<^sub>F \<equiv> top"

abbreviation frame_empty :: "'s::scene_space frame" ("\<lbrace>\<rbrace>")
  where "\<lbrace>\<rbrace> \<equiv> bot"

syntax "_frame_UNIV" :: "type \<Rightarrow> logic" ("UNIV\<^sub>F'(_')")

translations "UNIV\<^sub>F('a)" == "\<top>\<^sub>F :: 'a frame"

lemma frame_top: "top = frame_scene \<top>\<^sub>S"
  by (transfer, simp add: top_scene_space)

instance frame :: (scene_space) distrib_lattice
  by (intro_classes; transfer)
     (simp add: scene_space_class.scene_union_inter_distrib)

instantiation frame :: (scene_space) boolean_algebra
begin

lift_definition minus_frame :: "'a frame \<Rightarrow> 'a frame \<Rightarrow> 'a frame" is "\<lambda> a b. a \<sqinter>\<^sub>S - b"
  by (simp add: scene_space_inter scene_space_uminus)

lift_definition uminus_frame :: "'a frame \<Rightarrow> 'a frame" is "uminus"
  by (simp add: scene_space_uminus)

instance  
  by (intro_classes; transfer)
     (simp_all add: idem_scene_space scene_inter_indep scene_union_compl scene_le_iff_indep_inv subscene_refl)

end

instantiation frame :: (scene_space) "{Inf, Sup}"
begin

lift_definition Sup_frame :: "'a frame set \<Rightarrow> 'a frame" is "\<lambda> A. \<Squnion>\<^sub>S (SOME xs. set xs = A)"
proof -
  fix A :: "'a scene set"
  assume a: "\<And>x. x \<in> A \<Longrightarrow> x \<in> scene_space"
  have A_ss: "A \<subseteq> scene_space"
    by (simp add: a subsetI)
  hence "finite A"
    using finite_scene_space rev_finite_subset by blast
  then obtain xs where A: "A = set xs"
    using finite_list by blast
  hence "\<Squnion>\<^sub>S xs \<in> scene_space"
    using A_ss scene_space_foldr by blast
  moreover have "\<Squnion>\<^sub>S (SOME xs. set xs = A) = \<Squnion>\<^sub>S xs"
    by (metis (mono_tags, lifting) A A_ss foldr_scene_union_eq_scene_space someI)
  ultimately show "\<Squnion>\<^sub>S (SOME xs. set xs = A) \<in> scene_space"
    by simp
qed

definition Inf_frame :: "'a frame set \<Rightarrow> 'a frame" where "Inf_frame A = - (Sup (uminus ` A))"

instance ..

end

abbreviation frame_Union :: "'a::scene_space frame set \<Rightarrow> 'a frame"  ("\<Union>\<^sub>F")
  where "\<Union>\<^sub>FS \<equiv> Sup S"

abbreviation frame_Inter :: "'a::scene_space frame set \<Rightarrow> 'a frame"  ("\<Inter>\<^sub>F")
  where "\<Inter>\<^sub>FS \<equiv> Inf S"

instance frame :: (scene_space) complete_lattice
proof
  show Sup: "\<Union>\<^sub>F {} = bot"
    by (transfer, simp)
  show Inf: "\<Inter>\<^sub>F {} = top"
    by (simp add: Inf_frame_def Sup)
  show le_Sup: "\<And>(x::'a frame) A. x \<in> A \<Longrightarrow> x \<le> \<Union>\<^sub>F A"
  proof -
    fix x and A :: "'a frame set"
    assume "x \<in> A"
    thus "x \<le> Sup A"
    proof (transfer)
      fix x and A :: "'a scene set"
      assume x: "x \<in> scene_space" "\<forall>x\<in>A. x \<in> scene_space" "x \<in> A"
      then obtain xs where xs: "set xs = A"
        by (metis finite_list finite_scene_space rev_finite_subset subsetI)
      thus "x \<subseteq>\<^sub>S \<Squnion>\<^sub>S (SOME xs. set xs = A)"
        by (metis (mono_tags, lifting) scene_space_in_foldr someI subset_iff x(2) x(3))
    qed
  qed
  show "\<And>(x:: 'a frame) A. x \<in> A \<Longrightarrow> \<Inter>\<^sub>F A \<le> x"
  proof -
    fix x and A :: "'a frame set"
    assume xA: "x \<in> A"
    have "Inf A \<le> x \<longleftrightarrow> (- \<Union>\<^sub>F (uminus ` A) \<le> x)"
      by (simp add: Inf_frame_def)
    also have "... \<longleftrightarrow> (- x \<le> \<Union>\<^sub>F (uminus ` A))"
      using compl_le_swap2 by blast
    also have "..."
      by (simp add: le_Sup xA)
    finally show "\<Inter>\<^sub>F A \<le> x" .
  qed
  show Sup_le: "\<And>(A::'a frame set) z. (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> \<Union>\<^sub>F A \<le> z"
  proof transfer
    fix z and A :: "'a scene set"
    assume a: "\<forall>x\<in>A. x \<in> scene_space" "z \<in> scene_space" "\<And>x. x \<in> scene_space \<Longrightarrow> x \<in> A \<Longrightarrow> x \<subseteq>\<^sub>S z"
    then obtain xs where xs: "set xs = A"
      by (metis finite_list finite_scene_space rev_finite_subset subsetI)
    with a show "\<Squnion>\<^sub>S (SOME xs. set xs = A) \<subseteq>\<^sub>S z"
      by (metis (mono_tags, lifting) scene_space_foldr_lb subset_iff tfl_some)
  qed
  show "\<And>(A :: 'a frame set) z. (\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> \<Inter>\<^sub>F A"
  proof -
    fix A :: "'a frame set" and z :: "'a frame"
    assume a: "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
    have "z \<le> Inf A \<longleftrightarrow> \<Union>\<^sub>F (uminus ` A) \<le> - z"
      by (metis Inf_frame_def compl_le_swap1)
    also have "..."
      using a compl_le_compl_iff by (blast intro: Sup_le)
    finally show "z \<le> Inf A" .
  qed
qed

lemma frame_scene_foldr: "\<lbrakk> set xs \<subseteq> scene_space \<rbrakk> \<Longrightarrow> \<lbrakk>\<Squnion>\<^sub>S xs\<rbrakk>\<^sub>F = \<Union>\<^sub>F (set (map frame_scene xs))"
  by (transfer, auto simp add: image_constant_conv Int_absorb2 scene_space_foldr)
     (metis (mono_tags, lifting) foldr_scene_union_eq_scene_space tfl_some)

lemma frame_scene_top: "\<top>\<^sub>F = \<lbrakk>\<Squnion>\<^sub>S Vars\<rbrakk>\<^sub>F"
  by (simp add: frame_top top_scene_eq)  

lemma uminus_frame_Inf: "- \<Inter>\<^sub>F A = \<Union>\<^sub>F (uminus ` A)"
  by (simp add: Inf_frame_def)

lemma uminus_frame_Sup: "- \<Union>\<^sub>F A = \<Inter>\<^sub>F (uminus ` A)"
  by (simp add: Inf_frame_def SUP_image)

subsection \<open> Frames as sets of basis scenes \<close>

locale var_lens = vwb_lens +
  assumes lens_in_scene_space: "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> scene_space"

declare var_lens.lens_in_scene_space [simp]
declare var_lens.axioms(1) [simp]

locale basis_lens = vwb_lens +
  assumes lens_in_basis: "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> set Vars"

declare basis_lens.lens_in_basis [simp]

abbreviation (input) evar_lens :: "('a::two \<Longrightarrow> 's::scene_space) \<Rightarrow> bool" 
  where "evar_lens \<equiv> var_lens"

abbreviation (input) ebasis_lens :: "('a::two \<Longrightarrow> 's::scene_space) \<Rightarrow> bool" 
  where "ebasis_lens \<equiv> basis_lens"

lemma basis_then_var [simp]: "basis_lens x \<Longrightarrow> var_lens x"
  using basis_lens.lens_in_basis basis_lens_def var_lens_axioms_def var_lens_def by blast

lemma basis_lens_intro: "\<lbrakk> vwb_lens x; \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> set Vars \<rbrakk> \<Longrightarrow> basis_lens x"
  using basis_lens.intro basis_lens_axioms.intro by blast

lift_definition lens_frame :: "('a \<Longrightarrow> 's::scene_space) \<Rightarrow> 's frame" 
is "\<lambda> x. if var_lens x then \<lbrakk>x\<rbrakk>\<^sub>\<sim> else \<bottom>\<^sub>S" by auto

lemma frame_scene_basis_lens: "var_lens x \<Longrightarrow> \<lbrakk>\<lbrakk>x\<rbrakk>\<^sub>\<sim>\<rbrakk>\<^sub>F = lens_frame x"
  by (transfer, auto)

definition lens_member :: "('a \<Longrightarrow> 's::scene_space) \<Rightarrow> 's frame \<Rightarrow> bool" (infix "\<in>\<^sub>F" 50)
  where "x \<in>\<^sub>F a \<longleftrightarrow> (lens_frame x \<le> a)"

abbreviation lens_not_member (infix "\<notin>\<^sub>F" 50) where "x \<notin>\<^sub>F A \<equiv> \<not> (x \<in>\<^sub>F A)"

lemma lens_member_frame [simp]: "x \<in>\<^sub>F lens_frame x"
  by (simp add: lens_member_def)

lemma lens_not_member_empty: "var_lens x \<Longrightarrow> (x \<in>\<^sub>F \<lbrace>\<rbrace>) \<longleftrightarrow> x \<approx>\<^sub>L 0\<^sub>L"
  by (simp add: lens_member_def)
     (transfer, auto simp add: lens_equiv_scene scene_bot_least subscene_antisym zero_lens_scene)

lemma lens_not_member_empty_two: "evar_lens x \<Longrightarrow> x \<notin>\<^sub>F \<lbrace>\<rbrace>"
  using ief_lens_iff_zero lens_not_member_empty no_ief_two_view var_lens.axioms(1) by blast

lemma lens_member_top: "x \<in>\<^sub>F top"
  by (simp add: lens_member_def)

lemma FUn_iff [simp]: "basis_lens x \<Longrightarrow> (x \<in>\<^sub>F a \<union>\<^sub>F b) = (x \<in>\<^sub>F a \<or> x \<in>\<^sub>F b)"
  by (simp add: lens_member_def)
     (transfer, simp add: var_le_union_iff)

lemma FCompl_iff: "ebasis_lens x \<Longrightarrow> x \<in>\<^sub>F - A \<longleftrightarrow> x \<notin>\<^sub>F A"
  apply (simp add: lens_member_def, auto)
  apply (metis (no_types, opaque_lifting) basis_then_var boolean_algebra.disj_cancel_right boolean_algebra_class.boolean_algebra.double_compl bot.extremum compl_le_swap1 dual_order.trans lens_member_def lens_not_member_empty_two sup.absorb2)
  apply (metis FUn_iff boolean_algebra.disj_cancel_right lens_member_def top_greatest)
  done

lemma FInter_iff [simp]: "basis_lens x \<Longrightarrow> (x \<in>\<^sub>F a \<inter>\<^sub>F b) = (x \<in>\<^sub>F a \<and> x \<in>\<^sub>F b)"
  by (simp add: lens_member_def)
  
definition lens_insert :: "('a \<Longrightarrow> 's::scene_space) \<Rightarrow> 's frame \<Rightarrow> 's frame"
  where "lens_insert x a = sup (lens_frame x) a"

lemma lens_insert_twice [simp]: "lens_insert x (lens_insert x A) = lens_insert x A"
  by (simp add: lens_insert_def)

lemma lens_Un_insert_left [simp]: "lens_insert x A \<union>\<^sub>F B = lens_insert x (A \<union>\<^sub>F B)"
  by (simp add: lens_insert_def semigroup.assoc sup.semigroup_axioms)

lemma lens_insert_iff: 
  assumes "basis_lens x" "basis_lens y"
  shows "x \<in>\<^sub>F lens_insert y A \<longleftrightarrow> x \<approx>\<^sub>L 0\<^sub>L \<or> x \<approx>\<^sub>L y \<or> x \<in>\<^sub>F A"
  using assms
  apply (simp add: lens_insert_def lens_member_def)
  apply (transfer)
  apply (simp_all add: lens_equiv_scene scene_bot_least zero_lens_scene)
  apply (metis basis_lens.lens_in_basis basis_then_var le_vars_then_equal scene_bot_least subscene_refl var_le_union_iff var_lens.lens_in_scene_space)
  done

lemma lens_insert_iff_two [simp]: 
  assumes "basis_lens (x :: 'a::two \<Longrightarrow> 's::scene_space)" "basis_lens y"
  shows "x \<in>\<^sub>F lens_insert y A \<longleftrightarrow> x \<approx>\<^sub>L y \<or> x \<in>\<^sub>F A"
  using assms basis_lens_def ief_lens_iff_zero lens_insert_iff no_ief_two_view by blast

lemma lens_insert_commute: "lens_insert x (lens_insert y A) = lens_insert y (lens_insert x A)"
  by (simp add: lens_insert_def sup.left_commute)

syntax
  "_frame_set" :: "args \<Rightarrow> 'a::scene_space frame"    ("\<lbrace>(_)\<rbrace>")
translations
  "\<lbrace>x, xs\<rbrace>" \<rightleftharpoons> "CONST lens_insert x \<lbrace>xs\<rbrace>"
  "\<lbrace>x\<rbrace>" \<rightleftharpoons> "CONST lens_insert x \<lbrace>\<rbrace>"

lemma frame_single_var_lens [simp]: "var_lens x \<Longrightarrow> \<lbrakk>\<lbrakk>x\<rbrakk>\<^sub>\<sim>\<rbrakk>\<^sub>F = \<lbrace>x\<rbrace>"
  by (simp add: frame_scene_basis_lens lens_insert_def)

subsection \<open> Equivalence under a frame \<close>

lift_definition frame_equiv :: "'a::scene_space \<Rightarrow> 'a \<Rightarrow> 'a frame \<Rightarrow> bool" ("_ \<approx>\<^sub>F _ on _" [65,0,66] 65)
  is "\<lambda> s\<^sub>1 s\<^sub>2 a. s\<^sub>1 \<approx>\<^sub>S s\<^sub>2 on a" .

lemma frame_equiv_empty [simp]: "s\<^sub>1 \<approx>\<^sub>F s\<^sub>2 on \<lbrace>\<rbrace>"
  by (transfer, simp)

lemma frame_equiv_refl [simp]: "s \<approx>\<^sub>F s on a"
  by (simp add: of_frame frame_equiv.rep_eq idem_scene_space scene_equiv_def)

lemma frame_equiv_sym [simp]: "s\<^sub>1 \<approx>\<^sub>F s\<^sub>2 on a \<Longrightarrow> s\<^sub>2 \<approx>\<^sub>F s\<^sub>1 on a"
  by (transfer, simp add: scene_equiv_def)
     (metis idem_scene_space scene_override_idem scene_override_overshadow_right)

lemma frame_equiv_trans_gen [simp]: "\<lbrakk> s\<^sub>1 \<approx>\<^sub>F s\<^sub>2 on a; s\<^sub>2 \<approx>\<^sub>F s\<^sub>3 on b \<rbrakk> \<Longrightarrow> s\<^sub>1 \<approx>\<^sub>F s\<^sub>3 on (a \<inter>\<^sub>F b)"
proof (transfer, simp add: scene_override_inter scene_space_compat scene_space_uminus)
  fix a b :: "'a scene" and s\<^sub>1 s\<^sub>2 s\<^sub>3 :: "'a"
  assume 
    a:"a \<in> scene_space" and b: "b \<in> scene_space" and
    "s\<^sub>1 \<approx>\<^sub>S s\<^sub>2 on a" "s\<^sub>2 \<approx>\<^sub>S s\<^sub>3 on b"
  have 1: "s\<^sub>3 = s\<^sub>3 \<oplus>\<^sub>S s\<^sub>2 on b"
    by (metis \<open>b \<in> scene_space\<close> \<open>s\<^sub>2 \<approx>\<^sub>S s\<^sub>3 on b\<close> idem_scene_space scene_equiv_def scene_equiv_sym)
  have 2: "s\<^sub>1 = s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on a"
    by (metis \<open>s\<^sub>1 \<approx>\<^sub>S s\<^sub>2 on a\<close> scene_equiv_def)
  have 3: "s\<^sub>2 = s\<^sub>2 \<oplus>\<^sub>S s\<^sub>3 on b"
    by (metis \<open>s\<^sub>2 \<approx>\<^sub>S s\<^sub>3 on b\<close> scene_equiv_def)

  have "s\<^sub>1 \<oplus>\<^sub>S (s\<^sub>1 \<oplus>\<^sub>S s\<^sub>3 on a) on b = s\<^sub>1 \<oplus>\<^sub>S (s\<^sub>1 \<oplus>\<^sub>S (s\<^sub>3 \<oplus>\<^sub>S s\<^sub>2 on b) on a) on b"
    using "1" by auto
  also from 1 2 3 a b have "... = s\<^sub>1 \<oplus>\<^sub>S (s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on a) on b"
    by (metis scene_inter_commute scene_override_inter scene_override_overshadow_right scene_space_compat scene_space_uminus)
  also have "... = s\<^sub>1 \<oplus>\<^sub>S s\<^sub>1 on b"
    using 2 by auto
  also have "... = s\<^sub>1"
    by (simp add: b idem_scene_space)
  finally show "s\<^sub>1 \<approx>\<^sub>S s\<^sub>3 on a \<sqinter>\<^sub>S b"
    by (simp add: a b scene_equiv_def scene_override_inter scene_space_compat scene_space_uminus)
qed

lemma frame_equiv_trans: "\<lbrakk> s\<^sub>1 \<approx>\<^sub>F s\<^sub>2 on a; s\<^sub>2 \<approx>\<^sub>F s\<^sub>3 on a \<rbrakk> \<Longrightarrow> s\<^sub>1 \<approx>\<^sub>F s\<^sub>3 on a"
  by (transfer)
     (metis scene_equiv_def scene_override_overshadow_right)

end