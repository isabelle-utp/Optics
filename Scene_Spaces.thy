section \<open> Scene Spaces \<close>

theory Scene_Spaces
  imports Scenes
begin

subsection \<open> Preliminaries \<close>

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

lemma foldr_scene_union_add_tail:
  "\<lbrakk> pairwise (##\<^sub>S) (set xs); \<forall> x\<in>set xs. x ##\<^sub>S b \<rbrakk> \<Longrightarrow> foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S \<squnion>\<^sub>S b = foldr (\<squnion>\<^sub>S) xs b"
  apply (induct xs)
   apply (simp)
  apply (simp)
  apply (subst scene_union_assoc[THEN sym])
  apply (auto simp add: pairwise_insert)
  using pairwise_compat_foldr scene_compat_refl apply blast
  apply (meson pairwise_compat_foldr scene_compat_sym)
  done

corollary foldr_scene_union_remove1:
"\<lbrakk> pairwise (##\<^sub>S) (set xs); x \<in> set xs \<rbrakk> \<Longrightarrow> foldr (\<squnion>\<^sub>S) (remove1 x xs) \<bottom>\<^sub>S \<squnion>\<^sub>S x = foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S"
  apply (induct xs)
   apply simp
  apply (auto simp add: pairwise_insert scene_union_commute)
  by (smt (verit, del_insts) Un_iff le_iff_sup pairwise_compat_foldr pairwise_def 
      scene_compat.rep_eq scene_union_assoc scene_union_commute set_remove1_subset)

subsection \<open> Predicates \<close>

definition scene_indeps :: "'s scene set \<Rightarrow> bool" where
"scene_indeps = pairwise (\<bowtie>\<^sub>S)"

definition scene_span :: "'s scene list \<Rightarrow> bool" where
"scene_span S = (foldr (\<squnion>\<^sub>S) S \<bottom>\<^sub>S = \<top>\<^sub>S)"

text \<open> cf. @{term finite_dimensional_vector_space}, which scene spaces are based on. \<close>  

subsection \<open> Scene space class \<close>

class scene_space = 
  fixes Vars :: "'a scene list"
  assumes idem_scene_Vars: "\<And> x. x \<in> set Vars \<Longrightarrow> idem_scene x"
  and indep_Vars: "scene_indeps (set Vars)"
  and span_Vars: "scene_span Vars"
begin

lemma scene_space_compats [simp]: "pairwise (##\<^sub>S) (set Vars)"
  by (metis local.indep_Vars pairwise_alt scene_indep_compat scene_indeps_def)

inductive_set scene_space :: "'a scene set" where
bot_scene_space [intro]: "\<bottom>\<^sub>S \<in> scene_space" | 
Vars_scene_space [intro]: "x \<in> set Vars \<Longrightarrow> x \<in> scene_space" |
union_scene_space [intro]: "\<lbrakk> x \<in> scene_space; y \<in> scene_space \<rbrakk> \<Longrightarrow> x \<squnion>\<^sub>S y \<in> scene_space"

lemma idem_scene_space: "a \<in> scene_space \<Longrightarrow> idem_scene a"
  by (induct rule: scene_space.induct)
     (auto simp add: idem_scene_Vars)

lemma set_Vars_scene_space [simp]: "set Vars \<subseteq> scene_space"
  by blast

lemma scene_space_foldr: "set xs \<subseteq> scene_space \<Longrightarrow> foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S \<in> scene_space"
  by (induction xs, auto)

lemma top_scene_space: "\<top>\<^sub>S \<in> scene_space"
proof -
  have "\<top>\<^sub>S = foldr (\<squnion>\<^sub>S) Vars \<bottom>\<^sub>S"
    using span_Vars by (simp add: scene_span_def)
  also have "... \<in> scene_space"
    by (simp add: scene_space_foldr)
  finally show ?thesis .
qed

lemma Vars_compat_scene_space: "\<lbrakk> b \<in> scene_space; x \<in> set Vars \<rbrakk> \<Longrightarrow> x ##\<^sub>S b"
proof (induct b rule: scene_space.induct)
  case bot_scene_space
  then show ?case
    by (metis scene_compat_refl scene_union_incompat scene_union_unit(1)) 
next
  case (Vars_scene_space a)
  then show ?case
    by (metis local.indep_Vars pairwiseD scene_compat_refl scene_indep_compat scene_indeps_def)
next
  case (union_scene_space a b)
  then show ?case
    using scene_union_pres_compat by blast
qed

lemma scene_space_compat: "\<lbrakk> a \<in> scene_space; b \<in> scene_space \<rbrakk> \<Longrightarrow> a ##\<^sub>S b"
proof (induct rule: scene_space.induct)
  case bot_scene_space
  then show ?case
    \<comment> \<open> TODO: Make a simp rule for the below \<close>
    by (metis scene_compat_refl scene_union_commute scene_union_incompat scene_union_unit) 
next
  case (Vars_scene_space x)
  then show ?case
    by (simp add: Vars_compat_scene_space) 
next
  case (union_scene_space x y)
  then show ?case
    using scene_compat_sym scene_union_pres_compat by blast 
qed

corollary scene_space_union_assoc:
  assumes "x \<in> scene_space" "y \<in> scene_space" "z \<in> scene_space"
  shows "x \<squnion>\<^sub>S (y \<squnion>\<^sub>S z) = (x \<squnion>\<^sub>S y) \<squnion>\<^sub>S z"
  by (simp add: assms scene_space_compat scene_union_assoc)

lemma scene_space_vars_decomp: "a \<in> scene_space \<Longrightarrow> \<exists>xs. set xs \<subseteq> set Vars \<and> foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S = a"
proof (induct rule: scene_space.induct)
  case bot_scene_space
  then show ?case
    by (metis bot.extremum foldr.simps(1) id_apply list.set(1))
next
  case (Vars_scene_space x)
  show ?case
    apply (rule exI [where x="[x]"])
    using Vars_scene_space by simp
next
  case (union_scene_space x y)
  then obtain xs ys where xsys: "set xs \<subseteq> set Vars \<and> foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S = x"
                                "set ys \<subseteq> set Vars \<and> foldr (\<squnion>\<^sub>S) ys \<bottom>\<^sub>S = y"
    by blast+
  show ?case
    apply (rule exI [where x="xs @ ys"])
    apply (auto simp: xsys)
    by (metis (no_types, lifting) Vars_compat_scene_space foldr_scene_union_add_tail local.indep_Vars
        pairwise_mono scene_indep_compat scene_indeps_def subsetD union_scene_space.hyps(3) xsys(1))
 qed

lemma "fold (\<squnion>\<^sub>S) (map (\<lambda>x. x ;\<^sub>S a) Vars) b = \<lbrakk>a\<rbrakk>\<^sub>\<sim> \<squnion>\<^sub>S b"
  oops

lemma scene_space_inter: "\<lbrakk> a \<in> scene_space; b \<in> scene_space \<rbrakk> \<Longrightarrow> a \<sqinter>\<^sub>S b \<in> scene_space"
  sorry

lemma scene_space_uminus: "\<lbrakk> a \<in> scene_space \<rbrakk> \<Longrightarrow> - a \<in> scene_space"
proof (induction rule: scene_space.induct)
  case bot_scene_space
  then show ?case
    by (metis top_scene_space uminus_scene_twice uminus_top_scene)
next
  case (Vars_scene_space x)
  have "\<top>\<^sub>S = foldr (\<squnion>\<^sub>S) Vars \<bottom>\<^sub>S"
    using scene_span_def span_Vars by metis
  also have "... = x \<squnion>\<^sub>S (foldr (\<squnion>\<^sub>S) (remove1 x Vars) \<bottom>\<^sub>S)"
    by (metis foldr_scene_union_remove1 local.Vars_scene_space scene_space_compats scene_union_commute)
  have "(foldr (\<squnion>\<^sub>S) (remove1 x Vars) \<bottom>\<^sub>S) = - x"
    apply (rule scene_union_indep_uniq[where Z=x])
         apply (meson idem_scene_space order_trans scene_space_foldr set_Vars_scene_space set_remove1_subset)
    using local.Vars_scene_space local.idem_scene_Vars apply auto
    defer
    using scene_indep_self_compl scene_indep_sym apply blast
     apply (simp add: \<open>foldr (\<squnion>\<^sub>S) Vars \<bottom>\<^sub>S = x \<squnion>\<^sub>S foldr (\<squnion>\<^sub>S) (remove1 x Vars) \<bottom>\<^sub>S\<close> calculation scene_union_commute scene_union_compl)
    sorry (* need to prove foldr (\<squnion>\<^sub>S) (remove1 x Vars) \<bottom>\<^sub>S \<bowtie>\<^sub>S x *)
  then show ?case
    by (metis order_trans scene_space_foldr set_Vars_scene_space set_remove1_subset)
next
  case (union_scene_space x y)
  then show ?case
    by (simp add: scene_demorgan1 scene_space_inter)
qed

end

subsection \<open> Frame type \<close>

typedef (overloaded) 'a::scene_space frame = "scene_space :: 'a scene set"
  by blast

setup_lifting type_definition_frame

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

subsection \<open> Alphabet Scene Spaces \<close>

definition alpha_scene_space :: "'s scene list \<Rightarrow> ('a \<Longrightarrow> 's) \<Rightarrow> ('b::scene_space \<Longrightarrow> 's) \<Rightarrow> 's scene list" where
"alpha_scene_space xs b\<^sub>L m\<^sub>L = xs @ map (\<lambda> x. x ;\<^sub>S m\<^sub>L) Vars"

lemma scene_space_class_intro:
  assumes 
    "\<forall> x\<in>set xs. idem_scene x"
    "scene_indeps (set xs)"
    "vwb_lens b\<^sub>L" \<comment> \<open> The base lens \<close>
    "vwb_lens m\<^sub>L" \<comment> \<open> The more lens \<close>
    "b\<^sub>L \<bowtie> m\<^sub>L"
    "\<forall> x\<in>set xs. x \<bowtie>\<^sub>S \<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim>"  
    "foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S = \<lbrakk>b\<^sub>L\<rbrakk>\<^sub>\<sim>"
    "bij_lens (b\<^sub>L +\<^sub>L m\<^sub>L)"
  shows "class.scene_space (alpha_scene_space xs b\<^sub>L m\<^sub>L)"
proof (simp add: alpha_scene_space_def, unfold_locales)
  from assms(5-7) have 1: "(foldr (\<squnion>\<^sub>S) xs \<lbrakk>m\<^sub>L\<rbrakk>\<^sub>\<sim>) = \<top>\<^sub>S"
    by (metis assms(2) assms(3) assms(4) assms(8) foldr_scene_union_add_tail lens_plus_scene lens_scene_top_iff_bij_lens pairwise_alt plus_mwb_lens scene_indep_compat scene_indeps_def vwb_lens_mwb)

  show "\<And>x. x \<in> set (xs @ map (\<lambda>x. x ;\<^sub>S m\<^sub>L) Vars) \<Longrightarrow> idem_scene x"
    using assms(1) idem_scene_Vars by fastforce
  show "scene_indeps (set (xs @ map (\<lambda>x. x ;\<^sub>S m\<^sub>L) Vars))"
    apply (auto simp add: scene_indeps_def pairwise_def)
    apply (metis assms(2) pairwiseD scene_indeps_def)
    using assms(1) assms(6) idem_scene_Vars scene_comp_pres_indep apply blast
    using assms(1) assms(6) idem_scene_Vars scene_comp_pres_indep scene_indep_sym apply blast
    apply (metis indep_Vars pairwiseD scene_comp_indep scene_indeps_def)
    done
  show "scene_span (xs @ map (\<lambda>x. x ;\<^sub>S m\<^sub>L) Vars)"
    apply (simp add: scene_span_def)
    apply (subst foldr_compat_dist)
    apply (simp)
    apply (metis "1" assms(4) scene_comp_top_scene scene_span_def span_Vars)    
    done
qed

method alpha_scene_space uses defs =
  (rule scene_space_class.intro
  ,(intro_classes)[1]
  ,unfold defs
  ,rule scene_space_class_intro
  ,simp_all add: scene_indeps_def pairwise_def lens_plus_scene[THEN sym] lens_equiv_scene[THEN sym] lens_equiv_sym)
  
alphabet test = 
  x :: int
  y :: int 
  z :: int

instantiation test_ext :: (scene_space) scene_space
begin

definition Vars_test_ext :: "'a test_scheme scene list" where
"Vars_test_ext = alpha_scene_space [\<lbrakk>x\<rbrakk>\<^sub>\<sim>, \<lbrakk>y\<rbrakk>\<^sub>\<sim>, \<lbrakk>z\<rbrakk>\<^sub>\<sim>] base\<^sub>L more\<^sub>L"
  
instance by (alpha_scene_space defs: Vars_test_ext_def)

end

end