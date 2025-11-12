section \<open> Scene Spaces \<close>

theory Scene_Spaces            
  imports "HOL-Algebra.Complete_Lattice" Scenes
begin

(* Remove HOL-Algebra notation that may clash *)

no_notation Order.le (infixl \<open>\<sqsubseteq>\<index>\<close> 50)
no_notation Order.lless (infixl \<open>\<sqsubset>\<index>\<close> 50)
no_notation Order.top (\<open>\<top>\<index>\<close>)
no_notation Order.bottom (\<open>\<bottom>\<index>\<close>)

subsection \<open> Preliminaries \<close>

abbreviation foldr_scene :: "'a scene list \<Rightarrow> 'a scene" ("\<Squnion>\<^sub>S") where
"foldr_scene as \<equiv> foldr (\<squnion>\<^sub>S) as \<bottom>\<^sub>S"

lemma pairwise_indep_then_compat [simp]: "pairwise (\<bowtie>\<^sub>S) A \<Longrightarrow> pairwise (##\<^sub>S) A"
  by (simp add: pairwise_alt)

lemma pairwise_compat_foldr: 
  "\<lbrakk> pairwise (##\<^sub>S) (set as); \<forall> b \<in> set as. a ##\<^sub>S b \<rbrakk> \<Longrightarrow> a ##\<^sub>S \<Squnion>\<^sub>S as"
  apply (induct as)
   apply (simp)
  apply (auto simp add: pairwise_insert scene_union_pres_compat)
  done

lemma foldr_scene_indep:
  "\<lbrakk> pairwise (##\<^sub>S) (set as); \<forall> b \<in> set as. a \<bowtie>\<^sub>S b \<rbrakk> \<Longrightarrow> a \<bowtie>\<^sub>S \<Squnion>\<^sub>S as"
  apply (induct as)
   apply (simp)
  apply (auto intro: scene_indep_pres_compat simp add: pairwise_insert )
  done

lemma foldr_compat_dist:
  "pairwise (##\<^sub>S) (set as) \<Longrightarrow> foldr (\<squnion>\<^sub>S) (map (\<lambda>a. a ;\<^sub>S x) as) \<bottom>\<^sub>S = \<Squnion>\<^sub>S as ;\<^sub>S x"
  apply (induct as)
   apply (simp)
  apply (auto simp add: pairwise_insert)
  apply (metis pairwise_compat_foldr scene_compat_refl scene_union_comp_distl)
  done  

lemma foldr_compat_quotient_dist:
  "\<lbrakk> pairwise (##\<^sub>S) (set as); \<forall> a\<in>set as. a \<le> \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<rbrakk> \<Longrightarrow> foldr (\<squnion>\<^sub>S) (map (\<lambda>a. a /\<^sub>S x) as) \<bottom>\<^sub>S = \<Squnion>\<^sub>S as /\<^sub>S x"
  apply (induct as)
   apply (auto simp add: pairwise_insert)
  apply (subst scene_union_quotient)
     apply simp_all
  using pairwise_compat_foldr scene_compat_refl apply blast
  apply (meson foldr_scene_indep scene_indep_sym scene_le_iff_indep_inv)
  done

lemma foldr_scene_union_add_tail:
  "\<lbrakk> pairwise (##\<^sub>S) (set xs); \<forall> x\<in>set xs. x ##\<^sub>S b \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>S xs \<squnion>\<^sub>S b = foldr (\<squnion>\<^sub>S) xs b"
  apply (induct xs)
   apply (simp)
  apply (simp)
  apply (subst scene_union_assoc[THEN sym])
     apply (auto simp add: pairwise_insert)
  using pairwise_compat_foldr scene_compat_refl apply blast
  apply (meson pairwise_compat_foldr scene_compat_sym)
  done

lemma pairwise_Diff: "pairwise R A \<Longrightarrow> pairwise R (A - B)"
  using pairwise_mono by fastforce

lemma scene_compats_members: "\<lbrakk> pairwise (##\<^sub>S) A; x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow> x ##\<^sub>S y"
  by (metis pairwise_def scene_compat_refl)

corollary foldr_scene_union_removeAll:
  assumes "pairwise (##\<^sub>S) (set xs)" "x \<in> set xs"
  shows "\<Squnion>\<^sub>S (removeAll x xs) \<squnion>\<^sub>S x = \<Squnion>\<^sub>S xs"
using assms proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have x_compat: "\<And> z. z \<in> set xs \<Longrightarrow> x ##\<^sub>S z"
    using Cons.prems(1) Cons.prems(2) scene_compats_members by auto

  from Cons have x_compats: "x ##\<^sub>S \<Squnion>\<^sub>S (removeAll x xs)"
    by (metis (no_types, lifting) insert_Diff list.simps(15) pairwise_compat_foldr pairwise_insert removeAll_id set_removeAll x_compat)

  from Cons have a_compats: "a ##\<^sub>S \<Squnion>\<^sub>S (removeAll x xs)"
    by (metis (no_types, lifting) insert_Diff insert_iff list.simps(15) pairwise_compat_foldr pairwise_insert scene_compat_refl set_removeAll x_compats)

  from Cons show ?case 
  proof (cases "x \<in> set xs")
    case True
    with Cons show ?thesis
      by (auto simp add: pairwise_insert scene_union_commute)
         (metis a_compats scene_compats_members scene_union_assoc scene_union_idem,
          metis (full_types) a_compats scene_union_assoc scene_union_commute x_compats)
  next
    case False
    with Cons show ?thesis
      by (simp add: scene_union_commute)
  qed
qed

lemma foldr_scene_union_eq_sets:
  assumes "pairwise (##\<^sub>S) (set xs)" "set xs = set ys"
  shows "\<Squnion>\<^sub>S xs = \<Squnion>\<^sub>S ys"
using assms proof (induct xs arbitrary: ys)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  hence ys: "set ys = insert a (set (removeAll a ys))"
    by (auto)
  then show ?case
    by (metis (no_types, lifting) Cons.hyps Cons.prems(1) Cons.prems(2) Diff_insert_absorb foldr_scene_union_removeAll insertCI insert_absorb list.simps(15) pairwise_insert set_removeAll)
qed

lemma foldr_scene_removeAll:
  assumes "pairwise (##\<^sub>S) (set xs)"
  shows "x \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll x xs) = x \<squnion>\<^sub>S \<Squnion>\<^sub>S xs"
  by (metis (mono_tags, opaque_lifting) assms foldr_Cons foldr_scene_union_eq_sets insertCI insert_Diff list.simps(15) o_apply removeAll.simps(2) removeAll_id set_removeAll)

lemma pairwise_Collect: "pairwise R A \<Longrightarrow> pairwise R {x \<in> A. P x}"
  by (simp add: pairwise_def)

lemma removeAll_overshadow_filter: 
  "removeAll x (filter (\<lambda>xa. xa \<notin> A - {x}) xs) = removeAll x (filter (\<lambda> xa. xa \<notin> A) xs)"
  apply (simp add: removeAll_filter_not_eq)
  apply (rule filter_cong)
   apply (simp)
  apply auto
  done

corollary foldr_scene_union_filter:
  assumes "pairwise (##\<^sub>S) (set xs)" "set ys \<subseteq> set xs"
  shows "\<Squnion>\<^sub>S xs = \<Squnion>\<^sub>S (filter (\<lambda>x. x \<notin> set ys) xs) \<squnion>\<^sub>S \<Squnion>\<^sub>S ys"
using assms proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by (simp)
next
  case (Cons x xs)
  show ?case
  proof (cases "x \<in> set ys")
    case True
    with Cons have 1: "set ys - {x} \<subseteq> set xs"
      by (auto)
    have 2: "x ##\<^sub>S \<Squnion>\<^sub>S (removeAll x ys)"
      by (metis Cons.prems(1) Cons.prems(2) True foldr_scene_removeAll foldr_scene_union_removeAll pairwise_subset scene_compat_bot(2) scene_compat_sym scene_union_incompat scene_union_unit(1))
    have 3: "\<And> P. x ##\<^sub>S \<Squnion>\<^sub>S (filter P xs)"
      by (meson Cons.prems(1) Cons.prems(2) True filter_is_subset in_mono pairwise_compat_foldr pairwise_subset scene_compats_members set_subset_Cons)    
    have 4: "\<And> P. \<Squnion>\<^sub>S (filter P xs) ##\<^sub>S \<Squnion>\<^sub>S (removeAll x ys)"
      by (rule pairwise_compat_foldr)
         (metis Cons.prems(1) Cons.prems(2) pairwise_Diff pairwise_subset set_removeAll,
          metis (no_types, lifting) "1" Cons.prems(1) filter_is_subset pairwise_compat_foldr pairwise_subset scene_compat_sym scene_compats_members set_removeAll set_subset_Cons subsetD)
    have "\<Squnion>\<^sub>S (x # xs) = x \<squnion>\<^sub>S \<Squnion>\<^sub>S xs"
      by simp
    also have "... = x \<squnion>\<^sub>S (\<Squnion>\<^sub>S (filter (\<lambda>xa. xa \<notin> set ys - {x}) xs) \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll x ys))"
      using 1 Cons(1)[where ys="removeAll x ys"] Cons(2) by (simp add: pairwise_insert)    
    also have "... = (x \<squnion>\<^sub>S \<Squnion>\<^sub>S (filter (\<lambda>xa. xa \<notin> set ys - {x}) xs)) \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll x ys)"
      by (simp add: scene_union_assoc 1 2 3 4)
    also have "... = (x \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll x (filter (\<lambda>xa. xa \<notin> set ys - {x}) xs))) \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll x ys)"
      by (metis (no_types, lifting) Cons.prems(1) filter_is_subset foldr_scene_removeAll pairwise_subset set_subset_Cons)
    also have "... = (x \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll x (filter (\<lambda>xa. xa \<notin> set ys) xs))) \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll x ys)"
      by (simp only: removeAll_overshadow_filter)
    also have "... = (x \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll x (filter (\<lambda>xa. xa \<notin> set ys) (x # xs)))) \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll x ys)"
      by simp
    also have "... = (x \<squnion>\<^sub>S \<Squnion>\<^sub>S (filter (\<lambda>xa. xa \<notin> set ys) (x # xs))) \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll x ys)"
      by (simp add: True)
    also have "... = (\<Squnion>\<^sub>S (filter (\<lambda>xa. xa \<notin> set ys) (x # xs)) \<squnion>\<^sub>S x) \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll x ys)"
      by (simp add: scene_union_commute)
    also have "... = \<Squnion>\<^sub>S (filter (\<lambda>xa. xa \<notin> set ys) (x # xs)) \<squnion>\<^sub>S (x \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll x ys))"
      by (simp add: scene_union_assoc True 2 3 4 scene_compat_sym)
    also have "... = \<Squnion>\<^sub>S (filter (\<lambda>xa. xa \<notin> set ys) (x # xs)) \<squnion>\<^sub>S \<Squnion>\<^sub>S ys"
      by (metis (no_types, lifting) Cons.prems(1) Cons.prems(2) True foldr_scene_union_removeAll pairwise_subset scene_union_commute)
    finally show ?thesis .
  next
    case False
    with Cons(2-3) have 1: "set ys \<subseteq> set xs"
      by auto
    have 2: "x ##\<^sub>S \<Squnion>\<^sub>S (filter (\<lambda>x. x \<notin> set ys) xs)"
      by (metis (no_types, lifting) Cons.prems(1) filter_is_subset filter_set list.simps(15) member_filter pairwise_compat_foldr pairwise_insert pairwise_subset scene_compat_refl)
    have 3: "x ##\<^sub>S \<Squnion>\<^sub>S ys"
      by (meson Cons.prems(1) Cons.prems(2) list.set_intros(1) pairwise_compat_foldr pairwise_subset scene_compats_members subset_code(1))
    from Cons(1)[of ys] Cons(2-3) have 4: "\<Squnion>\<^sub>S (filter (\<lambda>x. x \<notin> set ys) xs) ##\<^sub>S \<Squnion>\<^sub>S ys"
      by (auto simp add: pairwise_insert)
         (metis (no_types, lifting) "1" foldr_append foldr_scene_union_eq_sets scene_compat_bot(1) scene_union_incompat set_append subset_Un_eq)

    with 1 False Cons(1)[of ys] Cons(2-3) show ?thesis
      by (auto simp add: pairwise_insert scene_union_assoc 2 3 4)
  qed
qed

lemma foldr_scene_append:
  "\<lbrakk> pairwise (##\<^sub>S) (set (xs @ ys)) \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>S (xs @ ys) = \<Squnion>\<^sub>S xs \<squnion>\<^sub>S \<Squnion>\<^sub>S ys"
  by (simp add: foldr_scene_union_add_tail pairwise_compat_foldr pairwise_subset scene_compats_members)

lemma foldr_scene_concat:
  "\<lbrakk> pairwise (##\<^sub>S) (set (concat xs)) \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>S (concat xs) = \<Squnion>\<^sub>S (map \<Squnion>\<^sub>S xs)"
  by (induct xs, simp_all, metis foldr_append foldr_scene_append pairwise_subset set_append set_concat sup_ge2)

subsection \<open> Predicates \<close>

text \<open> All scenes in the set are independent \<close>

definition scene_indeps :: "'s scene set \<Rightarrow> bool" where
"scene_indeps = pairwise (\<bowtie>\<^sub>S)"

text \<open> All scenes in the set cover the entire state space \<close>

definition scene_span :: "'s scene list \<Rightarrow> bool" where
"scene_span S = (foldr (\<squnion>\<^sub>S) S \<bottom>\<^sub>S = \<top>\<^sub>S)"

text \<open> cf. @{term finite_dimensional_vector_space}, which scene spaces are based on. \<close>  

subsection \<open> Scene space class \<close>

class scene_space =
  fixes Vars :: "'a scene list"
  assumes idem_scene_Vars [simp]: "\<And> x. x \<in> set Vars \<Longrightarrow> idem_scene x"
  and indep_Vars: "scene_indeps (set Vars)"
  and span_Vars: "scene_span Vars"
begin

lemma scene_space_compats [simp]: "pairwise (##\<^sub>S) (set Vars)"
  by (metis local.indep_Vars pairwise_alt scene_indep_compat scene_indeps_def)

lemma Vars_ext_lens_indep: "\<lbrakk> a ;\<^sub>S x \<noteq> b ;\<^sub>S x; a \<in> set Vars; b \<in> set Vars \<rbrakk> \<Longrightarrow> a ;\<^sub>S x \<bowtie>\<^sub>S b ;\<^sub>S x"
  by (metis indep_Vars pairwiseD scene_comp_indep scene_indeps_def)

inductive_set scene_space :: "'a scene set" where
bot_scene_space [intro]: "\<bottom>\<^sub>S \<in> scene_space" | 
Vars_scene_space [intro, simp]: "x \<in> set Vars \<Longrightarrow> x \<in> scene_space" |
union_scene_space [intro]: "\<lbrakk> x \<in> scene_space; y \<in> scene_space \<rbrakk> \<Longrightarrow> x \<squnion>\<^sub>S y \<in> scene_space"

lemma idem_scene_space: "a \<in> scene_space \<Longrightarrow> idem_scene a"
  by (induct rule: scene_space.induct) auto

lemma set_Vars_scene_space [simp]: "set Vars \<subseteq> scene_space"
  by blast

lemma mem_Vars_scene_space [simp]: "A \<subseteq> set Vars \<Longrightarrow> A \<subseteq> scene_space"
  by blast

lemma pairwise_compat_Vars_subset: "set xs \<subseteq> set Vars \<Longrightarrow> pairwise (##\<^sub>S) (set xs)"
  using pairwise_subset scene_space_compats by blast

lemma scene_space_foldr: "set xs \<subseteq> scene_space \<Longrightarrow> \<Squnion>\<^sub>S xs \<in> scene_space"
  by (induction xs, auto)

lemma top_scene_eq: "\<top>\<^sub>S = \<Squnion>\<^sub>S Vars"
  using local.span_Vars scene_span_def by force

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
    by simp
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
    by (simp add: exI[where x="[]"])
next
  case (Vars_scene_space x)
  show ?case
    apply (rule exI[where x="[x]"])
    using Vars_scene_space by simp
next
  case (union_scene_space x y)
  then obtain xs ys where xsys: "set xs \<subseteq> set Vars \<and> foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S = x"
                                "set ys \<subseteq> set Vars \<and> foldr (\<squnion>\<^sub>S) ys \<bottom>\<^sub>S = y"
    by blast+
  show ?case
  proof (rule exI[where x="xs @ ys"])
    show "set (xs @ ys) \<subseteq> set Vars \<and> \<Squnion>\<^sub>S (xs @ ys) = x \<squnion>\<^sub>S y"
      by (auto simp: xsys)
         (metis (full_types) Vars_compat_scene_space foldr_scene_union_add_tail pairwise_subset 
           scene_space_compats subsetD union_scene_space.hyps(3) xsys(1))
  qed
qed

lemma scene_space_vars_decomp_iff: "a \<in> scene_space \<longleftrightarrow> (\<exists>xs. set xs \<subseteq> set Vars \<and> a = foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S)"
  apply (rule iffI)
   apply (simp add: scene_space_foldr subset_eq)
  using scene_space_vars_decomp apply auto[1]
  by (meson dual_order.trans scene_space_foldr set_Vars_scene_space)

lemma scene_space_equiv_union:
  assumes "a \<in> scene_space" "b \<in> scene_space"
  shows "s \<approx>\<^sub>S s' on (a \<squnion>\<^sub>S b) \<longleftrightarrow> (s \<approx>\<^sub>S s' on a \<and> s \<approx>\<^sub>S s' on b)"
  by (meson assms(1,2) scene_equiv_union_decomp scene_space_compat)

lemma scene_space_equiv_foldr:
  assumes "set xs \<subseteq> scene_space"
  shows "s \<approx>\<^sub>S s' on (\<Squnion>\<^sub>S xs) \<longleftrightarrow> (\<forall> a\<in>set xs. s \<approx>\<^sub>S s' on a)"
using assms proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (simp add: scene_space_equiv_union scene_space_foldr)
qed

lemma Vars_indep_foldr: 
  assumes "x \<in> set Vars" "set xs \<subseteq> set Vars"
  shows "x \<bowtie>\<^sub>S \<Squnion>\<^sub>S (removeAll x xs)"
proof (rule foldr_scene_indep)
  show "pairwise (##\<^sub>S) (set (removeAll x xs))"
    by (simp, metis Diff_subset assms(2) pairwise_mono scene_space_compats)
  from assms show "\<forall>b\<in>set (removeAll x xs). x \<bowtie>\<^sub>S b"
    by (simp)
       (metis DiffE insertI1 local.indep_Vars pairwiseD scene_indeps_def subset_iff)
qed

lemma Vars_indeps_foldr:
  assumes "set xs \<subseteq> set Vars"
  shows "foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S \<bowtie>\<^sub>S foldr (\<squnion>\<^sub>S) (filter (\<lambda>x. x \<notin> set xs) Vars) \<bottom>\<^sub>S"
  apply (rule foldr_scene_indep)
   apply (meson filter_is_subset pairwise_subset scene_space_compats)
  apply (simp)
  apply auto
  apply (rule scene_indep_sym)
  apply (metis (no_types, lifting) assms foldr_scene_indep local.indep_Vars pairwiseD pairwise_mono scene_indeps_def scene_space_compats subset_iff)
  done

lemma uminus_var_other_vars:
  assumes "x \<in> set Vars"
  shows "- x = foldr (\<squnion>\<^sub>S) (removeAll x Vars) \<bottom>\<^sub>S"
proof (rule scene_union_indep_uniq[where Z="x"])
    show "idem_scene (foldr (\<squnion>\<^sub>S) (removeAll x Vars) \<bottom>\<^sub>S)"
      by (metis Diff_subset idem_scene_space order_trans scene_space_foldr set_Vars_scene_space set_removeAll)
    show "idem_scene x" "idem_scene (-x)"
      by (simp_all add: assms local.idem_scene_Vars)
    show "foldr (\<squnion>\<^sub>S) (removeAll x Vars) \<bottom>\<^sub>S \<bowtie>\<^sub>S x"
      using Vars_indep_foldr assms scene_indep_sym by blast
    show "- x \<bowtie>\<^sub>S x"
      using scene_indep_self_compl scene_indep_sym by blast
    show "- x \<squnion>\<^sub>S x = foldr (\<squnion>\<^sub>S) (removeAll x Vars) \<bottom>\<^sub>S \<squnion>\<^sub>S x"
      by (metis \<open>idem_scene (- x)\<close> assms foldr_scene_union_removeAll local.span_Vars scene_space_compats scene_span_def scene_union_compl uminus_scene_twice)
qed

lemma uminus_vars_other_vars:
  assumes "set xs \<subseteq> set Vars"
  shows "- \<Squnion>\<^sub>S xs = \<Squnion>\<^sub>S (filter (\<lambda>x. x \<notin> set xs) Vars)"
proof (rule scene_union_indep_uniq[where Z="foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S"])
  show "idem_scene (- foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S)" "idem_scene (foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S)"
    using assms idem_scene_space idem_scene_uminus scene_space_vars_decomp_iff by blast+
  show "idem_scene (foldr (\<squnion>\<^sub>S) (filter (\<lambda>x. x \<notin> set xs) Vars) \<bottom>\<^sub>S)"
    by (meson filter_is_subset idem_scene_space scene_space_vars_decomp_iff)
  show "- foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S \<bowtie>\<^sub>S foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S"
    by (metis scene_indep_self_compl uminus_scene_twice)
  show "foldr (\<squnion>\<^sub>S) (filter (\<lambda>x. x \<notin> set xs) Vars) \<bottom>\<^sub>S \<bowtie>\<^sub>S foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S"
    using Vars_indeps_foldr assms scene_indep_sym by blast
  show "- \<Squnion>\<^sub>S xs \<squnion>\<^sub>S \<Squnion>\<^sub>S xs = \<Squnion>\<^sub>S (filter (\<lambda>x. x \<notin> set xs) Vars) \<squnion>\<^sub>S \<Squnion>\<^sub>S xs"
    using foldr_scene_union_filter[of Vars xs, THEN sym]
    by (simp add: assms)
       (metis \<open>idem_scene (- \<Squnion>\<^sub>S xs)\<close> local.span_Vars scene_span_def scene_union_compl uminus_scene_twice)
qed

lemma scene_space_uminus: "\<lbrakk> a \<in> scene_space \<rbrakk> \<Longrightarrow> - a \<in> scene_space"
  by (auto simp add: scene_space_vars_decomp_iff uminus_vars_other_vars)
     (metis filter_is_subset)

lemma uminus_image_scene_space: "uminus ` scene_space = scene_space"
  by (metis (mono_tags, opaque_lifting) Set.set_eqI image_subset_iff scene_space_uminus subset_eq uminus_scene_twice)

lemma scene_space_inter: "\<lbrakk> a \<in> scene_space; b \<in> scene_space \<rbrakk> \<Longrightarrow> a \<sqinter>\<^sub>S b \<in> scene_space"
  by (simp add: inf_scene_def scene_space.union_scene_space scene_space_uminus)

lemma scene_union_foldr_remove_element:
  assumes "set xs \<subseteq> set Vars"
  shows "a \<squnion>\<^sub>S \<Squnion>\<^sub>S xs = a \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll a xs)"
  using assms proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases "x = a")
    case True
    then show ?thesis
      by (metis Cons.prems foldr_scene_removeAll pairwise_compat_Vars_subset) 
  next
    case False
    then show ?thesis
      by (metis Cons.prems foldr_scene_removeAll pairwise_subset scene_space_compats)
  qed
qed

lemma scene_union_foldr_Cons_removeAll:
  assumes "set xs \<subseteq> set Vars" "a \<in> set xs"
  shows "foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S = foldr (\<squnion>\<^sub>S) (a # removeAll a xs) \<bottom>\<^sub>S"
  by (metis assms(1) assms(2) foldr_scene_union_eq_sets insert_Diff list.simps(15) pairwise_subset scene_space_compats set_removeAll)

lemma scene_union_foldr_Cons_removeAll':
  assumes "set xs \<subseteq> set Vars" "a \<in> set Vars"
  shows "foldr (\<squnion>\<^sub>S) (a # xs) \<bottom>\<^sub>S = foldr (\<squnion>\<^sub>S) (a # removeAll a xs) \<bottom>\<^sub>S"
  by (simp add: assms(1) scene_union_foldr_remove_element)

lemma scene_in_foldr: "\<lbrakk> a \<in> set xs; set xs \<subseteq> set Vars \<rbrakk> \<Longrightarrow> a \<subseteq>\<^sub>S \<Squnion>\<^sub>S xs"
  apply (induct xs)
   apply (simp)
  apply (subst scene_union_foldr_Cons_removeAll')
    apply simp
   apply simp
  apply (auto)
  apply (rule scene_union_ub)
    apply (metis Diff_subset dual_order.trans idem_scene_space scene_space_vars_decomp_iff set_removeAll)
  using Vars_indep_foldr apply blast
  apply (metis Vars_indep_foldr foldr_scene_union_removeAll idem_scene_space local.idem_scene_Vars order.trans pairwise_mono removeAll_id scene_indep_sym scene_space_compats scene_space_foldr scene_union_commute scene_union_ub set_Vars_scene_space subscene_trans)
  done

lemma scene_union_foldr_subset:
  assumes "set xs \<subseteq> set ys" "set ys \<subseteq> set Vars"
  shows "\<Squnion>\<^sub>S xs \<subseteq>\<^sub>S \<Squnion>\<^sub>S ys"
  using assms proof (induct xs arbitrary: ys)
  case Nil
  then show ?case 
    by (simp add: scene_bot_least)
next
  case (Cons a xs)
  { assume "a \<in> set xs"
    with Cons have "foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S = foldr (\<squnion>\<^sub>S) (a # removeAll a xs) \<bottom>\<^sub>S"
      apply (subst scene_union_foldr_Cons_removeAll)
        apply (auto)
      done
  } note a_in = this
  { assume "a \<notin> set xs"
    then have "a \<squnion>\<^sub>S foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S = foldr (\<squnion>\<^sub>S) (a # xs) \<bottom>\<^sub>S"
      by simp
  } note a_out = this
  show ?case apply (simp)
    apply (cases "a \<in> set xs")
    using a_in Cons apply auto
     apply (metis dual_order.trans scene_union_foldr_remove_element)
    using a_out Cons apply auto
    apply (rule scene_union_mono)
    using scene_in_foldr apply blast
       apply blast
      apply (meson Vars_compat_scene_space dual_order.trans scene_space_foldr set_Vars_scene_space subsetD)
    using local.idem_scene_Vars apply blast
    apply (meson idem_scene_space scene_space_foldr set_Vars_scene_space subset_trans)
    done
qed

lemma union_scene_space_foldrs:
  assumes "set xs \<subseteq> set Vars" "set ys \<subseteq> set Vars"
  shows "(foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S) \<squnion>\<^sub>S (foldr (\<squnion>\<^sub>S) ys \<bottom>\<^sub>S) = foldr (\<squnion>\<^sub>S) (xs @ ys) \<bottom>\<^sub>S"
  using assms
  apply (induct ys)
   apply (simp_all)
  apply (metis Vars_compat_scene_space foldr_scene_union_add_tail local.indep_Vars pairwise_mono scene_indep_compat scene_indeps_def scene_space.Vars_scene_space scene_space.union_scene_space scene_space_foldr subset_eq)
  done

lemma scene_space_ub:
  assumes "a \<in> scene_space" "b \<in> scene_space"
  shows "a \<subseteq>\<^sub>S a \<squnion>\<^sub>S b"
  using assms scene_union_foldr_subset[of _ "_ @ _"] 
  by (auto simp add: scene_space_vars_decomp_iff union_scene_space_foldrs)

lemma scene_compl_subset_iff:
  assumes "a \<in> scene_space" "b \<in> scene_space"
  shows "- a \<subseteq>\<^sub>S -b \<longleftrightarrow> b \<subseteq>\<^sub>S a"
  by (metis scene_indep_sym scene_le_iff_indep_inv uminus_scene_twice)

lemma inter_scene_space_foldrs:
  assumes "set xs \<subseteq> set Vars" "set ys \<subseteq> set Vars"
  shows "\<Squnion>\<^sub>S xs \<sqinter>\<^sub>S \<Squnion>\<^sub>S ys = \<Squnion>\<^sub>S (filter (\<lambda> x. x \<in> set xs \<inter> set ys) Vars)"
proof -
  have "\<Squnion>\<^sub>S xs \<sqinter>\<^sub>S \<Squnion>\<^sub>S ys = - (- \<Squnion>\<^sub>S xs \<squnion>\<^sub>S - \<Squnion>\<^sub>S ys)"
    by (simp add: inf_scene_def)
  also have "... = - (\<Squnion>\<^sub>S (filter (\<lambda>x. x \<notin> set xs) Vars) \<squnion>\<^sub>S \<Squnion>\<^sub>S (filter (\<lambda>x. x \<notin> set ys) Vars))"
    by (simp add: uminus_vars_other_vars assms)
  also have "... = - \<Squnion>\<^sub>S (filter (\<lambda>x. x \<notin> set xs) Vars @ filter (\<lambda>x. x \<notin> set ys) Vars)"
    by (simp add: union_scene_space_foldrs assms)
  also have "... =  \<Squnion>\<^sub>S (filter (\<lambda>x. x \<notin> set (filter (\<lambda>x. x \<notin> set xs) Vars @ filter (\<lambda>x. x \<notin> set ys) Vars)) Vars)"
    by (subst uminus_vars_other_vars, simp_all)
  also have "... = \<Squnion>\<^sub>S (filter (\<lambda> x. x \<in> set xs \<inter> set ys) Vars)"
  proof -
    have "\<And>x. x \<in> set Vars \<Longrightarrow> ((x \<in> set Vars \<longrightarrow> x \<in> set xs) \<and> (x \<in> set Vars \<longrightarrow> x \<in> set ys)) = (x \<in> set xs \<and> x \<in> set ys)"
      by auto
    thus ?thesis
      by (simp cong: arg_cong[where f="\<Squnion>\<^sub>S"] filter_cong add: assms)
  qed
  finally show ?thesis .
qed

lemma scene_inter_distrib_lemma:
  assumes "set xs \<subseteq> set Vars" "set ys \<subseteq> set Vars" "set zs \<subseteq> set Vars"
  shows "\<Squnion>\<^sub>S xs \<squnion>\<^sub>S (\<Squnion>\<^sub>S ys \<sqinter>\<^sub>S \<Squnion>\<^sub>S zs) = (\<Squnion>\<^sub>S xs \<squnion>\<^sub>S \<Squnion>\<^sub>S ys) \<sqinter>\<^sub>S (\<Squnion>\<^sub>S xs \<squnion>\<^sub>S \<Squnion>\<^sub>S zs)"
proof -
  from assms have "\<Squnion>\<^sub>S xs \<squnion>\<^sub>S (\<Squnion>\<^sub>S ys \<sqinter>\<^sub>S \<Squnion>\<^sub>S zs) = \<Squnion>\<^sub>S (xs @ filter (\<lambda>x. x \<in> set ys \<inter> set zs) Vars)"
    by (simp add: union_scene_space_foldrs inter_scene_space_foldrs)
  also have "... = \<Squnion>\<^sub>S (filter (\<lambda>x. x \<in> set (xs @ ys) \<inter> set (xs @ zs)) Vars)"
  proof (rule foldr_scene_union_eq_sets)
    show "pairwise (##\<^sub>S) (set (xs @ filter (\<lambda>x. x \<in> set ys \<inter> set zs) Vars))"
    proof -
      have "\<exists>S. {s \<in> set Vars. s \<in> set ys \<and> s \<in> set zs} \<subseteq> S \<and> set xs \<subseteq> S \<and> pairwise (##\<^sub>S) S"
        using assms(1) scene_space_compats by blast
      then show ?thesis
        using pairwise_subset by fastforce
    qed  
    from assms show "set (xs @ filter (\<lambda>x. x \<in> set ys \<inter> set zs) Vars) = set (filter (\<lambda>x. x \<in> set (xs @ ys) \<inter> set (xs @ zs)) Vars)"
      by auto
  qed    
  also from assms have "... = \<Squnion>\<^sub>S (xs @ ys) \<sqinter>\<^sub>S \<Squnion>\<^sub>S (xs @ zs)"
    by (metis inter_scene_space_foldrs le_sup_iff set_append)
  also have "... = (\<Squnion>\<^sub>S xs \<squnion>\<^sub>S \<Squnion>\<^sub>S ys) \<sqinter>\<^sub>S (\<Squnion>\<^sub>S xs \<squnion>\<^sub>S \<Squnion>\<^sub>S zs)"
    by (simp add: assms union_scene_space_foldrs)  
  finally show ?thesis .
qed

lemma scene_union_inter_distrib:
  assumes "a \<in> scene_space" "b \<in> scene_space" "c \<in> scene_space"
  shows "a \<squnion>\<^sub>S b \<sqinter>\<^sub>S c = (a \<squnion>\<^sub>S b) \<sqinter>\<^sub>S (a \<squnion>\<^sub>S c)"
  using assms
  by (auto simp add: scene_space_vars_decomp_iff scene_inter_distrib_lemma)

lemma finite_distinct_lists_subset:
  assumes "finite A"
  shows "finite {xs. distinct xs \<and> set xs \<subseteq> A}"
proof -
  from assms have 1: "{xs. distinct xs \<and> set xs \<subseteq> A} = {xs. distinct xs \<and> length xs \<le> card A \<and> set xs \<subseteq> A}"
    by (auto, metis card_mono distinct_card)
  have 2: "... \<subseteq> {xs. set xs \<subseteq> A \<and> length xs \<le> card A}"
    by auto
  have 3: "finite ..."
    using assms finite_lists_length_le by blast
  show ?thesis
    by (metis (mono_tags, lifting) "1" "2" "3" infinite_super)
qed

lemma foldr_scene_union_remdups: "set xs \<subseteq> set Vars \<Longrightarrow> \<Squnion>\<^sub>S (remdups xs) = \<Squnion>\<^sub>S xs"
  by (auto intro: foldr_scene_union_eq_sets simp add: pairwise_compat_Vars_subset)

lemma scene_space_as_lists:
  "scene_space = {\<Squnion>\<^sub>S xs | xs. distinct xs \<and> set xs \<subseteq> set Vars}"
proof (rule Set.set_eqI, rule iffI)
  fix a
  assume "a \<in> scene_space"
  then obtain xs where xs: "set xs \<subseteq> set Vars" "\<Squnion>\<^sub>S xs = a"
    using scene_space_vars_decomp_iff by auto
  thus "a \<in> {\<Squnion>\<^sub>S xs |xs. distinct xs \<and> set xs \<subseteq> set Vars}"
    by auto (metis distinct_remdups foldr_scene_union_remdups set_remdups)
next
  fix a
  assume "a \<in> {\<Squnion>\<^sub>S xs |xs. distinct xs \<and> set xs \<subseteq> set Vars}"
  thus "a \<in> scene_space"
    using scene_space_vars_decomp_iff by auto
qed

lemma finite_scene_space: "finite scene_space"
proof -
  have "scene_space = {\<Squnion>\<^sub>S xs | xs. distinct xs \<and> set xs \<subseteq> set Vars}"
    by (simp add: scene_space_as_lists)
  also have "... = \<Squnion>\<^sub>S ` {xs. distinct xs \<and> set xs \<subseteq> set Vars}"
    by auto
  also have "finite ..."
    by (rule finite_imageI, simp add: finite_distinct_lists_subset)
  finally show ?thesis .
qed 

lemma scene_space_inter_assoc:
  assumes "x \<in> scene_space" "y \<in> scene_space" "z \<in> scene_space"
  shows "(x \<sqinter>\<^sub>S y) \<sqinter>\<^sub>S z = x \<sqinter>\<^sub>S (y \<sqinter>\<^sub>S z)"
proof -
  have "(x \<sqinter>\<^sub>S y) \<sqinter>\<^sub>S z = - (- x \<squnion>\<^sub>S - y \<squnion>\<^sub>S - z)"
    by (simp add: scene_demorgan1 uminus_scene_twice)
  also have "... = - (- x \<squnion>\<^sub>S (- y \<squnion>\<^sub>S - z))"
    by (simp add: assms scene_space_uminus scene_space_union_assoc)
  also have "... = x \<sqinter>\<^sub>S (y \<sqinter>\<^sub>S z)"
    by (simp add: scene_demorgan1 uminus_scene_twice)
  finally show ?thesis .
qed

lemma scene_inter_union_distrib:
  assumes "x \<in> scene_space" "y \<in> scene_space" "z \<in> scene_space"
  shows "x \<sqinter>\<^sub>S (y \<squnion>\<^sub>S z) = (x \<sqinter>\<^sub>S y) \<squnion>\<^sub>S (x \<sqinter>\<^sub>S z)"
proof-
  have "x \<sqinter>\<^sub>S (y \<squnion>\<^sub>S z) = (x \<sqinter>\<^sub>S (x \<squnion>\<^sub>S z)) \<sqinter>\<^sub>S (y \<squnion>\<^sub>S z)"
    by (metis assms(1) assms(3) idem_scene_space local.scene_union_inter_distrib scene_indep_bot scene_inter_commute scene_inter_indep scene_space.simps scene_union_unit(1))
  also have "... = (y \<squnion>\<^sub>S z) \<sqinter>\<^sub>S (x \<sqinter>\<^sub>S (x \<squnion>\<^sub>S z))"
    by (simp add: scene_union_inter_distrib assms scene_inter_commute scene_union_assoc union_scene_space scene_space_inter scene_union_commute)  
  also have "\<dots> = x \<sqinter>\<^sub>S ((y \<squnion>\<^sub>S z) \<sqinter>\<^sub>S (x \<squnion>\<^sub>S z))"
    by (metis assms scene_inter_commute scene_space.union_scene_space scene_space_inter_assoc)
  also have "\<dots> = x \<sqinter>\<^sub>S (z \<squnion>\<^sub>S (x \<sqinter>\<^sub>S y))"
    by (simp add: assms scene_union_inter_distrib scene_inter_commute scene_union_commute)
    
  also have "\<dots> = ((x \<sqinter>\<^sub>S y) \<squnion>\<^sub>S x) \<sqinter>\<^sub>S ((x \<sqinter>\<^sub>S y) \<squnion>\<^sub>S z)"
    by (metis (no_types, opaque_lifting) assms(1) assms(2) idem_scene_space local.scene_union_inter_distrib scene_indep_bot scene_inter_commute scene_inter_indep scene_space.bot_scene_space scene_union_commute scene_union_idem scene_union_unit(1))
  also have "\<dots> = (x \<sqinter>\<^sub>S y) \<squnion>\<^sub>S (x \<sqinter>\<^sub>S z)"
    by (simp add: assms scene_union_inter_distrib scene_space_inter)
  finally show ?thesis .
qed

lemma scene_union_inter_minus:
  assumes "a \<in> scene_space" "b \<in> scene_space"
  shows "a \<squnion>\<^sub>S (b \<sqinter>\<^sub>S - a) = a \<squnion>\<^sub>S b"
  by (metis assms(1) assms(2) bot_idem_scene idem_scene_space idem_scene_uminus local.scene_union_inter_distrib scene_demorgan1 scene_space_uminus scene_union_compl scene_union_unit(1) uminus_scene_twice)

lemma scene_union_foldr_minus_element:
  assumes "a \<in> scene_space" "set xs \<subseteq> scene_space"
  shows "a \<squnion>\<^sub>S \<Squnion>\<^sub>S xs = a \<squnion>\<^sub>S \<Squnion>\<^sub>S (map (\<lambda> x. x \<sqinter>\<^sub>S - a) xs)"
using assms proof (induct xs)
  case Nil
  then show ?case by (simp)
next
  case (Cons y ys)
  have "a \<squnion>\<^sub>S (y \<squnion>\<^sub>S \<Squnion>\<^sub>S ys) = y \<squnion>\<^sub>S (a \<squnion>\<^sub>S \<Squnion>\<^sub>S ys)"
    by (metis Cons.prems(2) assms(1) insert_subset list.simps(15) scene_space_foldr scene_space_union_assoc scene_union_commute)
  also have "... = y \<squnion>\<^sub>S (a \<squnion>\<^sub>S \<Squnion>\<^sub>S (map (\<lambda>x. x \<sqinter>\<^sub>S - a) ys))"
    using Cons.hyps Cons.prems(2) assms(1) by auto
  also have "... = y \<squnion>\<^sub>S a \<squnion>\<^sub>S \<Squnion>\<^sub>S (map (\<lambda>x. x \<sqinter>\<^sub>S - a) ys)"
    apply (subst scene_union_assoc)
    using Cons.prems(2) assms(1) scene_space_compat apply auto[1]
      apply (rule pairwise_compat_foldr)
       apply (simp)
       apply (rule pairwise_imageI)
    apply (meson Cons.prems(2) assms(1) scene_space_compat scene_space_inter scene_space_uminus set_subset_Cons subsetD)
    apply simp
    apply (meson Cons.prems(2) assms(1) in_mono list.set_intros(1) scene_space_compat scene_space_inter scene_space_uminus set_subset_Cons)
     apply (rule pairwise_compat_foldr)
    apply (simp)
       apply (rule pairwise_imageI)
    apply (meson Cons.prems(2) assms(1) in_mono scene_space_compat scene_space_inter scene_space_uminus set_subset_Cons)
    apply (simp)
     apply (meson Cons.prems(2) assms(1) in_mono scene_space_compat scene_space_inter scene_space_uminus set_subset_Cons)
    apply simp
    done
  also have "... = a \<squnion>\<^sub>S (y \<sqinter>\<^sub>S - a \<squnion>\<^sub>S \<Squnion>\<^sub>S (map (\<lambda>x. x \<sqinter>\<^sub>S - a) ys))"
    apply (subst scene_union_assoc)
    using Cons.prems(2) assms(1) scene_space_compat scene_space_inter scene_space_uminus apply force
      apply (metis (no_types, lifting) Cons.hyps Cons.prems(2) assms(1) insert_subset list.simps(15) scene_compat_sym scene_space_compat scene_space_foldr scene_union_assoc scene_union_idem scene_union_incompat scene_union_unit(1))
    apply (rule scene_space_compat)
    using Cons.prems(2) assms(1) scene_space_inter scene_space_uminus apply auto[1]
     apply (rule scene_space_foldr)
    apply auto
    apply (meson Cons.prems(2) assms(1) in_mono scene_space_inter scene_space_uminus set_subset_Cons)
    apply (metis Cons.prems(2) assms(1) insert_subset list.simps(15) scene_union_inter_minus scene_union_commute)
    done
  finally show ?case using Cons
    by auto
qed

lemma scene_space_in_foldr: "\<lbrakk> a \<in> set xs; set xs \<subseteq> scene_space \<rbrakk> \<Longrightarrow> a \<subseteq>\<^sub>S \<Squnion>\<^sub>S xs"
proof (induct xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys)
  have ysp: "y \<squnion>\<^sub>S \<Squnion>\<^sub>S ys = y \<squnion>\<^sub>S \<Squnion>\<^sub>S (map (\<lambda> x. x \<sqinter>\<^sub>S - y) ys)"
    using Cons.prems(2) scene_union_foldr_minus_element by force
  show ?case
  proof (cases "a \<subseteq>\<^sub>S y")
    case False
    with Cons show ?thesis
      by (simp)
         (metis (no_types, lifting) idem_scene_space scene_space_foldr scene_space_ub scene_union_commute subscene_trans)
  next
    case True
    with Cons show ?thesis
      by (simp)
         (meson idem_scene_space scene_space_foldr scene_space_ub subscene_trans)
  qed
qed

lemma scene_space_foldr_lb: 
  "\<lbrakk> a \<in> scene_space; set xs \<subseteq> scene_space; \<forall> b\<in>set xs. b \<le> a \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>S xs \<subseteq>\<^sub>S a"
proof (induct xs arbitrary: a)
  case Nil
  then show ?case
    by (simp add: scene_bot_least)
next
  case (Cons x xs)
  then show ?case
    by (simp add: scene_space_compat scene_space_foldr scene_union_lb)
qed

lemma var_le_union_choice:
  "\<lbrakk> x \<in> set Vars; a \<in> scene_space; b \<in> scene_space; x \<le> a \<squnion>\<^sub>S b \<rbrakk> \<Longrightarrow> (x \<le> a \<or> x \<le> b)"
  by (auto simp add: scene_space_vars_decomp_iff)
     (metis Vars_indep_foldr bot_idem_scene idem_scene_space removeAll_id scene_bot_least scene_indep_pres_compat scene_le_iff_indep_inv scene_space.union_scene_space scene_space_foldr scene_space_in_foldr scene_union_compl set_Vars_scene_space subscene_trans subset_trans uminus_scene_twice uminus_top_scene)

lemma var_le_union_iff:
  "\<lbrakk> x \<in> set Vars; a \<in> scene_space; b \<in> scene_space \<rbrakk> \<Longrightarrow> x \<le> a \<squnion>\<^sub>S b \<longleftrightarrow> (x \<le> a \<or> x \<le> b)"
  apply (rule iffI, simp add: var_le_union_choice)
  apply (auto)
   apply (meson idem_scene_space scene_space_ub subscene_trans)
  apply (metis idem_scene_space scene_space_ub scene_union_commute subscene_trans)
  done

text \<open> @{term Vars} may contain the empty scene, as we want to allow vacuous lenses in alphabets \<close>

lemma le_vars_then_equal: "\<lbrakk> x \<in> set Vars; y \<in> set Vars; x \<le> y; x \<noteq> \<bottom>\<^sub>S \<rbrakk> \<Longrightarrow> x = y"
  by (metis bot_idem_scene foldr_scene_removeAll local.idem_scene_Vars local.indep_Vars local.span_Vars pairwiseD scene_bot_least scene_indep_pres_compat scene_indeps_def scene_le_iff_indep_inv scene_space_compats scene_span_def scene_union_annhil subscene_antisym uminus_scene_twice uminus_top_scene uminus_var_other_vars)

end

lemma scene_union_le_iff: 
  assumes "a \<in> scene_space" "b \<in> scene_space"
  shows "a \<squnion>\<^sub>S b \<le> c \<longleftrightarrow> a \<le> c \<and> b \<le> c"
  by (metis assms idem_scene_space idem_scene_union scene_space_compat
      scene_space_ub scene_union_commute scene_union_mono subscene_trans)

lemma foldr_scene_union_eq_scene_space: 
  "\<lbrakk> set xs \<subseteq> scene_space; set xs = set ys \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>S xs = \<Squnion>\<^sub>S ys"
  by (metis foldr_scene_union_eq_sets pairwise_def pairwise_subset scene_space_compat)

lemma foldr_scene_le_then_subset:
  assumes "set xs \<subseteq> set Vars" "set ys \<subseteq> set Vars" "\<Squnion>\<^sub>S xs \<le> \<Squnion>\<^sub>S ys" "\<bottom>\<^sub>S \<notin> set xs"
  shows "set xs \<subseteq> set ys"
  using assms proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
    apply (simp add: scene_union_le_iff scene_space_foldr)
    apply (metis (mono_tags, lifting) Vars_indep_foldr bot_idem_scene foldr_scene_union_filter
        removeAll_id scene_bot_least scene_indep_pres_compat scene_le_iff_indep_inv
        scene_space_compats subscene_antisym top_scene_eq uminus_bot_scene
        uminus_vars_other_vars)
    done
qed

lemma foldr_scene_eq_then_eq:
  assumes "set xs \<subseteq> set Vars" "set ys \<subseteq> set Vars" "\<Squnion>\<^sub>S xs = \<Squnion>\<^sub>S ys" "\<bottom>\<^sub>S \<notin> set xs" "\<bottom>\<^sub>S \<notin> set ys"
  shows "set xs = set ys"
  by (simp add: assms dual_order.eq_iff foldr_scene_le_then_subset scene_union_foldr_subset)

definition scene_decomp :: "'a::scene_space scene \<Rightarrow> 'a scene set" ("\<lbrakk>_\<rbrakk>\<^sub>S") where
  "scene_decomp a = (THE B. B \<subseteq> set Vars \<and> \<bottom>\<^sub>S \<notin> B \<and> (\<exists> xs. B = set xs \<and> a = \<Squnion>\<^sub>S xs))"

lemma scene_decomp:
  assumes "a \<in> scene_space" 
  shows decomp_Vars: "scene_decomp a \<subseteq> set Vars" (is "?A")
  and decomp_nbot [simp]: "\<bottom>\<^sub>S \<notin> scene_decomp a" (is "?B")
  and decomp_foldr_scene: "\<exists> xs. scene_decomp a = set xs \<and> a = \<Squnion>\<^sub>S xs" (is "?C")
proof -
  obtain B where B:"B \<subseteq> set Vars" "\<exists> xs. B = set xs \<and> a = \<Squnion>\<^sub>S xs"
    by (metis assms scene_space_vars_decomp_iff)
  hence sd: "scene_decomp a = B - {\<bottom>\<^sub>S}"
    unfolding scene_decomp_def
    apply (rule_tac the_equality)
    apply (metis (no_types, lifting) Diff_empty Diff_iff Diff_insert0 Diff_subset
        dual_order.trans foldr_scene_union_removeAll insertCI pairwise_subset
        scene_space_compats scene_union_unit(1) set_removeAll)
    apply auto
    apply (metis (no_types, lifting) foldr_scene_le_then_subset subscene_refl
        subset_iff)
    apply (metis (mono_tags, lifting) Vars_indep_foldr foldr_scene_union_filter
        idem_scene_space removeAll_id scene_bot_least scene_in_foldr scene_indep_pres_compat
        scene_le_iff_indep_inv scene_space_class.scene_space.Vars_scene_space
        scene_space_compats subscene_antisym subset_iff top_scene_eq uminus_bot_scene
        uminus_vars_other_vars)
    done    

  from sd B show ?A
    by force
  from sd B show ?B
    by force
  from sd B show ?C
    by (metis foldr_scene_removeAll pairwise_compat_Vars_subset scene_union_unit(2)
        set_removeAll)
qed

lemma scene_decomp_mem_Vars [simp]: 
  "\<lbrakk> a \<in> scene_space; x \<in> scene_decomp a \<rbrakk> \<Longrightarrow> x \<in> set Vars"
  by (metis decomp_Vars subset_iff)

lemma scene_decomp_eq_transfer:
  assumes "a \<in> scene_space" "b \<in> scene_space" "\<lbrakk>a\<rbrakk>\<^sub>S = \<lbrakk>b\<rbrakk>\<^sub>S"
  shows "a = b"
  by (metis assms(1,2,3) decomp_Vars decomp_foldr_scene foldr_scene_union_eq_scene_space
      mem_Vars_scene_space)

lemma scene_decomp_le_transfer:
  assumes "a \<in> scene_space" "b \<in> scene_space" "\<lbrakk>a\<rbrakk>\<^sub>S \<subseteq> \<lbrakk>b\<rbrakk>\<^sub>S"
  shows "a \<le> b"
  by (metis assms(1,2,3) decomp_Vars decomp_foldr_scene scene_union_foldr_subset)

lemma scene_foldr_decomp_le_Vars:
  assumes "set xs \<subseteq> scene_space" "set ys \<subseteq> set Vars" "\<Squnion>\<^sub>S xs \<le> \<Squnion>\<^sub>S ys" "a \<in> set xs" "b \<in> \<lbrakk>a\<rbrakk>\<^sub>S"
  shows "b \<in> set ys"
proof -
  have bV: "b \<in> set Vars"
    using assms(1,4,5) scene_decomp_mem_Vars by blast
  obtain zs where zs: "\<lbrakk>a\<rbrakk>\<^sub>S = set zs" "a = \<Squnion>\<^sub>S zs"
    using assms(1,4) decomp_foldr_scene by blast
  have zs_Vars: "set zs \<subseteq> set Vars"
    by (metis assms(1,4) decomp_Vars subset_iff zs(1))
  have zs_le_xs: "\<Squnion>\<^sub>S zs \<le> \<Squnion>\<^sub>S ys"
    by (metis assms(1,3,4) idem_scene_space scene_space_foldr scene_space_in_foldr subscene_trans zs(2))
  show ?thesis
    by (metis (no_types) assms(1,2,4,5) decomp_nbot foldr_scene_le_then_subset subset_iff zs(1) zs_Vars zs_le_xs)
qed


lemma scene_foldr_decomp_le_iff:
  assumes "set xs \<subseteq> scene_space" "set ys \<subseteq> set Vars"
  shows "\<Squnion>\<^sub>S xs \<le> \<Squnion>\<^sub>S ys \<longleftrightarrow> (\<forall> a\<in>set xs. \<forall> b\<in>\<lbrakk>a\<rbrakk>\<^sub>S. b \<in> set ys)"
  apply (rule iffI)
  using assms(1,2) scene_foldr_decomp_le_Vars apply blast
  apply (rule scene_space_foldr_lb)
  using assms(2) scene_space_vars_decomp_iff apply blast
  using assms(1) apply blast
  apply (metis assms(1,2) decomp_foldr_scene scene_union_foldr_subset subset_iff)
  done

lemma scene_decomp_foldr:
  assumes "set xs \<subseteq> set Vars" "\<bottom>\<^sub>S \<notin> set xs"
  shows "\<lbrakk>\<Squnion>\<^sub>S xs\<rbrakk>\<^sub>S = set xs"
  by (metis assms(1,2) decomp_Vars decomp_foldr_scene decomp_nbot foldr_scene_eq_then_eq mem_Vars_scene_space scene_space_foldr)

lemma scene_decomp_foldr_nbot:
  assumes "set xs \<subseteq> set Vars" 
  shows "\<lbrakk>\<Squnion>\<^sub>S xs\<rbrakk>\<^sub>S = set xs - {\<bottom>\<^sub>S}"
  by (metis Diff_iff assms insert_Diff insert_subset removeAll_id scene_decomp_foldr scene_union_foldr_remove_element scene_union_unit(2) set_removeAll singletonI)

lemma scene_decomp_top:
  "\<lbrakk>\<top>\<^sub>S\<rbrakk>\<^sub>S = set Vars - {\<bottom>\<^sub>S}"
  by (metis Diff_empty Diff_iff Diff_insert0 Diff_subset insertCI scene_decomp_foldr set_removeAll top_scene_eq uminus_bot_scene uminus_var_other_vars)

lemma scene_decomp_bot:
  "\<lbrakk>\<bottom>\<^sub>S\<rbrakk>\<^sub>S = {}"
  by (metis bot.extremum empty_iff foldr.simps(1) id_apply list.set(1) scene_decomp_foldr)

lemma scene_decomp_union:
  assumes "a \<in> scene_space" "b \<in> scene_space"
  shows "\<lbrakk>a \<squnion>\<^sub>S b\<rbrakk>\<^sub>S = \<lbrakk>a\<rbrakk>\<^sub>S \<union> \<lbrakk>b\<rbrakk>\<^sub>S"
proof -
  obtain xs where xs:"set xs \<subseteq> set Vars" "\<bottom>\<^sub>S \<notin> set xs" "a = \<Squnion>\<^sub>S xs"
    by (metis assms(1) decomp_Vars decomp_foldr_scene decomp_nbot foldr_scene_union_remdups set_remdups)
  obtain ys where ys:"set ys \<subseteq> set Vars" "\<bottom>\<^sub>S \<notin> set ys" "b = \<Squnion>\<^sub>S ys"
    by (metis assms(2) decomp_Vars decomp_foldr_scene decomp_nbot foldr_scene_union_remdups set_remdups)
  from xs ys have "\<Squnion>\<^sub>S xs \<squnion>\<^sub>S \<Squnion>\<^sub>S ys = \<Squnion>\<^sub>S (xs @ ys)"
    using union_scene_space_foldrs by blast
  with xs ys have "\<lbrakk>a \<squnion>\<^sub>S b\<rbrakk>\<^sub>S = set xs \<union> set ys"
    by (metis Un_iff le_sup_iff scene_decomp_foldr set_append)
  also have "... = \<lbrakk>a\<rbrakk>\<^sub>S \<union> \<lbrakk>b\<rbrakk>\<^sub>S"
    by (simp add: scene_decomp_foldr xs ys)
  finally show ?thesis .
qed

lemma scene_decomp_uminus:
  assumes "a \<in> scene_space"
  shows "\<lbrakk>- a\<rbrakk>\<^sub>S = set Vars - \<lbrakk>a\<rbrakk>\<^sub>S - {\<bottom>\<^sub>S}"
proof -
  obtain xs where xs:"set xs \<subseteq> set Vars" "\<bottom>\<^sub>S \<notin> set xs" "a = \<Squnion>\<^sub>S xs"
    by (metis assms(1) decomp_Vars decomp_foldr_scene decomp_nbot foldr_scene_union_remdups set_remdups)
  thm uminus_vars_other_vars
  hence "\<lbrakk>- a\<rbrakk>\<^sub>S = \<lbrakk>\<Squnion>\<^sub>S (filter (\<lambda>x. x \<notin> set xs) Vars)\<rbrakk>\<^sub>S"
    by (simp add: uminus_vars_other_vars)
  also have "... = set(filter (\<lambda>x. x \<notin> set xs) Vars) - {\<bottom>\<^sub>S}"
    by (metis (no_types, lifting) Diff_iff filter_filter filter_is_subset insertCI scene_decomp_foldr scene_union_foldr_remove_element scene_union_unit(2) set_minus_filter_out
        set_removeAll)
  also have "... = set Vars - \<lbrakk>a\<rbrakk>\<^sub>S - {\<bottom>\<^sub>S}"
    by (metis (full_types) scene_decomp_foldr set_diff_eq set_filter xs)
  finally show ?thesis .
qed

lemma scene_decomp_inter:
  assumes "a \<in> scene_space" "b \<in> scene_space"
  shows "\<lbrakk>a \<sqinter>\<^sub>S b\<rbrakk>\<^sub>S = \<lbrakk>a\<rbrakk>\<^sub>S \<inter> \<lbrakk>b\<rbrakk>\<^sub>S"
proof -
  have "\<lbrakk>a \<sqinter>\<^sub>S b\<rbrakk>\<^sub>S = \<lbrakk>- (- a \<squnion>\<^sub>S - b)\<rbrakk>\<^sub>S"
    by (simp add: inf_scene_def)
  also have "... = set Vars - (set Vars - \<lbrakk>a\<rbrakk>\<^sub>S - {\<bottom>\<^sub>S} \<union> (set Vars - \<lbrakk>b\<rbrakk>\<^sub>S - {\<bottom>\<^sub>S})) - {\<bottom>\<^sub>S}"
    by (simp add: scene_decomp_uminus scene_decomp_union assms union_scene_space scene_space_uminus )
  also have "... = \<lbrakk>a\<rbrakk>\<^sub>S \<inter> \<lbrakk>b\<rbrakk>\<^sub>S"
    using assms decomp_Vars by force
  finally show ?thesis .
qed

lemma scene_decomp_foldr_scene:
  assumes "set xs \<subseteq> scene_space"
  shows "\<lbrakk>\<Squnion>\<^sub>S xs\<rbrakk>\<^sub>S = \<Union> (scene_decomp ` set xs)"
  using assms
proof (induct xs)
  case Nil
  then show ?case
    by (simp add: scene_decomp_bot)
next
  case (Cons a xs)
  then show ?case
    by (simp add: scene_decomp_union scene_space_foldr)
qed

lemma scene_decomp_atom:
  assumes "a \<in> set Vars"
  shows "\<lbrakk>a\<rbrakk>\<^sub>S = {a} - {\<bottom>\<^sub>S}"
proof -
  have "\<lbrakk>a\<rbrakk>\<^sub>S = \<lbrakk>\<Squnion>\<^sub>S [a]\<rbrakk>\<^sub>S"
    by simp
  also have "... = {a} - {\<bottom>\<^sub>S}"
    by (metis assms empty_set empty_subsetI insert_subset list.simps(15) scene_decomp_foldr_nbot)
  finally show ?thesis .
qed

lemma scene_equiv_decomp:
  assumes "a \<in> scene_space"
  shows "s \<approx>\<^sub>S s' on a \<longleftrightarrow> (\<forall> b \<in> \<lbrakk>a\<rbrakk>\<^sub>S. s \<approx>\<^sub>S s' on b)"
  by (metis assms decomp_Vars decomp_foldr_scene mem_Vars_scene_space scene_space_equiv_foldr)

subsection \<open> Mapping a lens over a scene list \<close>

definition map_lcomp :: "'b scene list \<Rightarrow> ('b \<Longrightarrow> 'a) \<Rightarrow> 'a scene list" where
"map_lcomp ss a = map (\<lambda> x. x ;\<^sub>S a) ss"

lemma map_lcomp_dist: 
  "\<lbrakk> pairwise (##\<^sub>S) (set xs); vwb_lens a \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>S (map_lcomp xs a) = \<Squnion>\<^sub>S xs ;\<^sub>S a"
  by (simp add: foldr_compat_dist map_lcomp_def)

lemma map_lcomp_Vars_is_lens [simp]: "vwb_lens a \<Longrightarrow> \<Squnion>\<^sub>S (map_lcomp Vars a) = \<lbrakk>a\<rbrakk>\<^sub>\<sim>"
  by (metis map_lcomp_dist scene_comp_top_scene scene_space_compats top_scene_eq)

lemma set_map_lcomp [simp]: "set (map_lcomp xs a) = (\<lambda>x. x ;\<^sub>S a) ` set xs"
  by (simp add: map_lcomp_def)

subsection \<open> Instances \<close>

instantiation unit :: scene_space
begin

definition Vars_unit :: "unit scene list" where [simp]: "Vars_unit = []"

instance
  by (intro_classes, simp_all add: scene_indeps_def scene_span_def unit_scene_top_eq_bot)

end

instantiation prod :: (scene_space, scene_space) scene_space
begin

definition Vars_prod :: "('a \<times> 'b) scene list" where "Vars_prod = map_lcomp Vars fst\<^sub>L @ map_lcomp Vars snd\<^sub>L"

instance proof
  have pw: "pairwise (\<bowtie>\<^sub>S) (set (map_lcomp Vars fst\<^sub>L @ map_lcomp Vars snd\<^sub>L))"
    by (auto simp add: pairwise_def Vars_ext_lens_indep scene_comp_pres_indep scene_indep_sym)
  show "\<And>x:: ('a \<times> 'b) scene. x \<in> set Vars \<Longrightarrow> idem_scene x"
    by (auto simp add: Vars_prod_def)
  from pw show "scene_indeps (set (Vars :: ('a \<times> 'b) scene list))"
    by (simp add: Vars_prod_def scene_indeps_def)
  show "scene_span (Vars :: ('a \<times> 'b) scene list)"
    by (simp only: scene_span_def Vars_prod_def foldr_scene_append pw pairwise_indep_then_compat map_lcomp_Vars_is_lens fst_vwb_lens snd_vwb_lens)
       (metis fst_vwb_lens lens_plus_scene lens_scene_top_iff_bij_lens plus_mwb_lens scene_union_commute snd_fst_lens_indep snd_vwb_lens swap_bij_lens vwb_lens_mwb)
qed  

end

subsection \<open> Complete lattice of scenes \<close>

definition Sup_scene :: "'a::scene_space scene set \<Rightarrow> 'a scene" ("\<Union>\<^sub>S") where 
"Sup_scene A = \<Squnion>\<^sub>S (SOME xs. set xs = (A \<inter> scene_space))"

lemma Sup_scene_is_foldr_scene:
  assumes "set xs \<subseteq> scene_space"
  shows "\<Union>\<^sub>S (set xs) = \<Squnion>\<^sub>S xs"
proof -
  have "set (SOME ys. set ys = set xs) = set xs"
    by (rule someI[where x="xs"], simp)
  thus ?thesis
    by (metis Sup_scene_def assms foldr_scene_union_eq_scene_space inf.absorb_iff1)
qed

lemma Sup_scene_decomp_transfer:
  assumes "A \<subseteq> scene_space"
  shows "\<lbrakk>\<Union>\<^sub>S A\<rbrakk>\<^sub>S = (\<Union>x\<in>A. \<lbrakk>x\<rbrakk>\<^sub>S)" 
proof -
  obtain xs where xs: "set xs = A"
    by (metis assms finite_list finite_scene_space rev_finite_subset)
  have "\<lbrakk>\<Union>\<^sub>S A\<rbrakk>\<^sub>S = \<lbrakk>\<Squnion>\<^sub>S xs\<rbrakk>\<^sub>S"
    by (metis Sup_scene_is_foldr_scene assms xs)
  also have "... = \<Union> (scene_decomp ` set xs)"
    using assms scene_decomp_foldr_scene xs by blast
  also have "... = (\<Union>x\<in>A. \<lbrakk>x\<rbrakk>\<^sub>S)"
    by (simp add: Setcompr_eq_image xs)
  finally show ?thesis .
qed

lemma Sup_scene_decomp_Vars_transfer:
  assumes "A \<subseteq> set Vars"
  shows "\<lbrakk>\<Union>\<^sub>S A\<rbrakk>\<^sub>S = A - {\<bottom>\<^sub>S}" 
proof -
  have "\<lbrakk>\<Union>\<^sub>S A\<rbrakk>\<^sub>S = (\<Union>x\<in>A. \<lbrakk>x\<rbrakk>\<^sub>S)"
    by (simp add: Sup_scene_decomp_transfer assms)
  also have "... = (\<Union>x\<in>A. {x} - {\<bottom>\<^sub>S})"
    by (meson Sup.SUP_cong assms scene_decomp_atom subset_iff)
  also have "... = A - {\<bottom>\<^sub>S}"
    by blast
  finally show ?thesis .
qed

lemma Sup_scene_closed: "\<Union>\<^sub>S A \<in> scene_space"
  unfolding Sup_scene_def proof -
  fix A :: "'a scene set"
  obtain xs where A: "A \<inter> scene_space = set xs"
    by (metis finite_Int finite_list finite_scene_space)
  hence "\<Squnion>\<^sub>S xs \<in> scene_space"
    using scene_space_foldr by auto
  moreover have "\<Squnion>\<^sub>S (SOME xs. set xs = A \<inter> scene_space) = \<Squnion>\<^sub>S xs"
    by (metis (mono_tags, lifting) A Int_iff foldr_scene_union_eq_scene_space someI subsetI)
  ultimately show "\<Squnion>\<^sub>S (SOME xs. set xs = A \<inter> scene_space) \<in> scene_space"
    by simp
qed

lemma Sup_scene_bot [simp]: "\<Union>\<^sub>S {} = bot"
  by (simp add: Sup_scene_def)

definition Inf_scene :: "'a::scene_space scene set \<Rightarrow> 'a scene" where
 "Inf_scene A = - (\<Union>\<^sub>S (uminus ` A))"

notation Inf_scene ("\<Inter>\<^sub>S")

lemma Inf_scene_decomp_transfer:
  assumes "A \<subseteq> scene_space" "A \<noteq> {}"
  shows "\<lbrakk>\<Inter>\<^sub>S A\<rbrakk>\<^sub>S = (\<Inter>x\<in>A. \<lbrakk>x\<rbrakk>\<^sub>S)" 
proof -
  have "\<lbrakk>\<Inter>\<^sub>S A\<rbrakk>\<^sub>S = \<lbrakk>- (\<Union>\<^sub>S (uminus ` A))\<rbrakk>\<^sub>S"
    by (simp add: Inf_scene_def)
  also have "... = set Vars - \<Union> {\<lbrakk>a\<rbrakk>\<^sub>S |a. a \<in> uminus ` A} - {\<bottom>\<^sub>S}"
  proof -
    have "uminus ` A \<subseteq> scene_space"
      by (metis assms(1) image_mono uminus_image_scene_space)
    thus ?thesis
      by (auto simp add: scene_decomp_uminus Sup_scene_decomp_transfer Sup_scene_closed assms)
  qed
  also have "... = set Vars \<inter> - \<Union> ((scene_decomp \<circ> uminus) ` A) \<inter> - {\<bottom>\<^sub>S}"
    by auto
  also from assms scene_decomp_uminus have "... = (set Vars \<inter> (\<Inter>x\<in>A. \<lbrakk>x\<rbrakk>\<^sub>S)) \<inter> - {\<bottom>\<^sub>S}"
    by auto
  also from assms scene_decomp_uminus have "... = (\<Inter>x\<in>A. \<lbrakk>x\<rbrakk>\<^sub>S) \<inter> - {\<bottom>\<^sub>S}"
  proof -
    have "\<forall> x\<in>A. \<lbrakk>x\<rbrakk>\<^sub>S \<subseteq> set Vars"
      using assms decomp_Vars by blast
    with assms(2) have "(\<Inter>x\<in>A. \<lbrakk>x\<rbrakk>\<^sub>S) \<subseteq> set Vars"
      by blast
    thus ?thesis
      by auto
  qed
  also from assms have "... = (\<Inter>x\<in>A. \<lbrakk>x\<rbrakk>\<^sub>S)"
    by (metis INF_eq_const INT_E decomp_nbot in_mono inf.order_iff subset_Compl_singleton)
  finally show ?thesis .
qed

lemmas scene_decomp_transfer = 
  scene_decomp_top scene_decomp_bot scene_decomp_union scene_decomp_uminus scene_decomp_inter
  Sup_scene_decomp_transfer Inf_scene_decomp_transfer

lemma Inf_scene_top:  "\<Inter>\<^sub>S {} = top_class.top"
  by (simp add: Inf_scene_def)

lemma uminus_scene_Inf: "- \<Inter>\<^sub>S A = \<Union>\<^sub>S (uminus ` A)"
  by (simp add: Inf_scene_def uminus_scene_twice)

lemma uminus_scene_Sup: "- \<Union>\<^sub>S A = \<Inter>\<^sub>S (uminus ` A)"
  by (metis (no_types, lifting) ext image_ident image_image uminus_scene_Inf uminus_scene_twice)
  
definition scene_gorder :: "'a::scene_space scene gorder" where 
"scene_gorder = \<lparr> carrier = scene_space, eq = (=), le = (\<le>) \<rparr>"

lemma carrier_scene_gorder [simp]: "carrier scene_gorder = scene_space"
  by (simp add: scene_gorder_def)

lemma eq_scene_gorder [simp]: "eq scene_gorder = (=)"
  by (simp add: scene_gorder_def)

lemma le_scene_gorder [simp]: "le scene_gorder = (\<subseteq>\<^sub>S)"
  by (simp add: scene_gorder_def)

lemma Sup_scene_props:
  assumes "A \<subseteq> scene_space"
  shows le_Sup_scene: "x \<in> A \<Longrightarrow> x \<subseteq>\<^sub>S \<Union>\<^sub>S A" 
  and Sup_scene_le: "\<lbrakk> z \<in> scene_space; \<And>x. x \<in> A \<Longrightarrow> x \<subseteq>\<^sub>S z \<rbrakk> \<Longrightarrow> \<Union>\<^sub>S A \<subseteq>\<^sub>S z"
proof -  
  obtain xs where xs: "A = set xs"
    by (metis assms(1) finite_list finite_scene_space rev_finite_subset)
  have xs_ss: "set xs \<subseteq> scene_space"
    using assms(1) xs by auto
  show 1: "x \<in> A \<Longrightarrow> x \<le> \<Union>\<^sub>S A"
    by (simp add: Sup_scene_is_foldr_scene scene_space_in_foldr xs xs_ss)
  show 2: "\<lbrakk> z \<in> scene_space; \<And>x. x \<in> A \<Longrightarrow> x \<le> z \<rbrakk> \<Longrightarrow> \<Union>\<^sub>S A \<le> z"
    by (simp add: Upper_def Sup_scene_is_foldr_scene xs xs_ss)
       (meson scene_space_foldr_lb subset_iff xs_ss)    
qed

lemma Sup_scene_lub: "A \<subseteq> scene_space \<Longrightarrow> is_lub scene_gorder (\<Union>\<^sub>S A) A"
  by (rule_tac least_UpperI) 
     (auto simp add: Upper_def intro!: Sup_scene_props Sup_scene_closed)

definition ss_union :: "'a::scene_space scene \<Rightarrow> 'a scene \<Rightarrow> 'a scene" (infixl \<open>\<union>\<^sub>S\<close> 65) where
"ss_union x y = Sup_scene {x, y}"

definition ss_inter :: "'a::scene_space scene \<Rightarrow> 'a scene \<Rightarrow> 'a scene" (infixl \<open>\<inter>\<^sub>S\<close> 65) where
"ss_inter x y = Inf_scene {x, y}"

lemma sup_scene_union: 
  assumes "x \<in> scene_space" "y \<in> scene_space"
  shows "x \<union>\<^sub>S y = x \<squnion>\<^sub>S y"
proof -
  have "x \<union>\<^sub>S y = \<Squnion>\<^sub>S [x, y]"
    by (metis ss_union_def Sup_scene_is_foldr_scene assms(1,2) bot.extremum insert_subset list.set(1) list.simps(15))
  thus ?thesis
    by simp
qed

lemma inf_scene_inter: 
  assumes "x \<in> scene_space" "y \<in> scene_space"
  shows "x \<inter>\<^sub>S y = x \<sqinter>\<^sub>S y"
proof -
  have "x \<inter>\<^sub>S y = - \<Squnion>\<^sub>S (map uminus [x, y])"
    by (metis (mono_tags, lifting) Inf_scene_def Sup_scene_is_foldr_scene assms(1,2) empty_iff empty_set image_iff insert_subset list.set_map list.simps(15,9) ss_inter_def
        subsetI uminus_image_scene_space)
  also have "... = - \<Squnion>\<^sub>S [-x, -y]"
    by simp
  also have "... = -(-x \<squnion>\<^sub>S -y)"
    by simp
  also have "... = x \<sqinter>\<^sub>S y"
    by (simp add: inf_scene_def)  
  finally show ?thesis .
qed

lemma Inf_scene_glb:
  assumes "A \<subseteq> scene_space"
  shows "is_glb scene_gorder (\<Inter>\<^sub>S A) A"
proof (rule greatest_LowerI, simp_all add: Lower_def assms)
  fix x :: \<open>'a scene\<close>
  assume xA: \<open>x \<in> A\<close>
  have "\<Inter>\<^sub>S A \<le> x \<longleftrightarrow> (- \<Union>\<^sub>S (uminus ` A) \<le> x)"
    by (simp add: Inf_scene_def)
  also have "... \<longleftrightarrow> (- x \<le> \<Union>\<^sub>S (uminus ` A))"
    using scene_indep_sym scene_le_iff_indep_inv by blast
  also have "..."
    by (metis assms image_eqI image_subset_iff in_mono le_Sup_scene scene_space_uminus xA)
  finally show "\<Inter>\<^sub>S A \<le> x" .
next
  fix y
  assume a:"(\<forall>x. x \<in> A \<and> x \<in> scene_space \<longrightarrow> y \<subseteq>\<^sub>S x) \<and> y \<in> scene_space"
  have "y \<le> \<Inter>\<^sub>S A \<longleftrightarrow> \<Union>\<^sub>S (uminus ` A) \<le> - y"
    by (metis Inf_scene_def scene_indep_sym scene_le_iff_indep_inv uminus_scene_twice)
  also from assms a have "..."
    using scene_space_uminus scene_compl_subset_iff
    by (force intro!: Sup_scene_le)
  finally show "y \<subseteq>\<^sub>S \<Inter>\<^sub>S A"
    by blast
next 
  show "\<Inter>\<^sub>S A \<in> scene_space"
    by (metis Inf_scene_def Sup_scene_closed scene_space_uminus)
qed

lemma scene_space_complete_lattice: "complete_lattice scene_gorder"
proof (unfold_locales, simp_all add: scene_gorder_def)
  fix x :: \<open>'a scene\<close>
  assume \<open>x \<in> scene_space\<close>
  show \<open>x \<subseteq>\<^sub>S x\<close>
    by (simp add: subscene_refl) 
next
  fix x :: \<open>'a scene\<close> and y :: \<open>'a scene\<close>
  assume 
    \<open>x \<subseteq>\<^sub>S y\<close> and
    \<open>y \<subseteq>\<^sub>S x\<close> and
    \<open>x \<in> scene_space\<close> and
    \<open>y \<in> scene_space\<close>
  thus \<open>x = y\<close>
    using idem_scene_space subscene_antisym by auto 
next
  fix x :: \<open>'a scene\<close> and y :: \<open>'a scene\<close> and z :: \<open>'a scene\<close>
  assume 
    \<open>x \<subseteq>\<^sub>S y\<close> and
    \<open>y \<subseteq>\<^sub>S z\<close> and
    \<open>x \<in> scene_space\<close> and
    \<open>y \<in> scene_space\<close> and
    \<open>z \<in> scene_space\<close>
  thus \<open>x \<subseteq>\<^sub>S z\<close>
    using idem_scene_space subscene_trans by auto 
next
  fix A :: \<open>'a scene set\<close>
  assume A: \<open>A \<subseteq> scene_space\<close>
  
  hence "is_lub \<lparr>carrier = scene_space, eq = (=), le = (\<subseteq>\<^sub>S)\<rparr> (\<Union>\<^sub>S A) A"
    by (rule_tac least_UpperI) 
       (auto simp add: Upper_def intro!: Sup_scene_props Sup_scene_closed)
  thus "\<exists>s. is_lub \<lparr>carrier = scene_space, eq = (=), le = (\<subseteq>\<^sub>S)\<rparr> s A"
    by blast
next
  fix A :: \<open>'a scene set\<close>
  assume A: \<open>A \<subseteq> scene_space\<close>
  have "is_glb \<lparr>carrier = scene_space, eq = (=), le = (\<subseteq>\<^sub>S)\<rparr> (\<Inter>\<^sub>S A) A"
    by (metis A Inf_scene_glb scene_gorder_def)
  thus "\<exists>i. is_glb \<lparr>carrier = scene_space, eq = (=), le = (\<subseteq>\<^sub>S)\<rparr> i A"
    by blast
qed

lemma Sup_scene_decomp:
  assumes "a \<in> scene_space"
  shows "\<Union>\<^sub>S \<lbrakk>a\<rbrakk>\<^sub>S = a"
  by (metis Sup_scene_is_foldr_scene assms decomp_Vars decomp_foldr_scene mem_Vars_scene_space)

lemma basis_scene_decomposition:
  assumes "a \<in> scene_space"
  shows "\<exists> B\<subseteq>set Vars. a = \<Union>\<^sub>S B"
  by (metis Sup_scene_decomp assms decomp_Vars)

lemma (in complete_lattice) is_lub_modulo_carrier:
  "is_lub L x A \<longleftrightarrow> is_lub L x (A \<inter> carrier L)"
  by (simp add: Upper_def)

lemma (in complete_lattice) is_glb_modulo_carrier:
  "is_glb L x A \<longleftrightarrow> is_glb L x (A \<inter> carrier L)"
  by (simp add: Lower_def)

lemma sup_scene_space:
  assumes "A \<subseteq> scene_space"
  shows "Lattice.sup scene_gorder A = \<Union>\<^sub>S A"
proof -
  interpret ss_clat: complete_lattice scene_gorder
    by (simp add: scene_space_complete_lattice)
  show ?thesis
    by (metis Sup_scene_lub assms carrier_scene_gorder ss_clat.least_unique ss_clat.sup_lub)
qed

lemma sup_scene_space_eq: "Lattice.sup scene_gorder A = \<Union>\<^sub>S A"
proof -  
  have "Lattice.sup scene_gorder A = Lattice.sup scene_gorder (A \<inter> scene_space)"
    by (metis Eps_cong carrier_scene_gorder complete_lattice.is_lub_modulo_carrier scene_space_complete_lattice sup_def)
  also have "... = \<Union>\<^sub>S (A \<inter> scene_space)"
    by (simp add: sup_scene_space)
  also have "... = \<Union>\<^sub>S A"
    by (simp add: Sup_scene_def)
  finally show ?thesis .
qed

lemma sup_scene_space_def: "Lattice.sup scene_gorder = \<Union>\<^sub>S"
  using sup_scene_space_eq by auto

lemma inf_scene_space:
  assumes "A \<subseteq> scene_space"
  shows "Lattice.inf scene_gorder A = \<Inter>\<^sub>S A"
proof -
  interpret ss_clat: complete_lattice scene_gorder
    by (simp add: scene_space_complete_lattice)
  show ?thesis
    by (metis Inf_scene_glb assms carrier_scene_gorder ss_clat.greatest_unique ss_clat.inf_glb)
qed

lemma inf_scene_space_eq: "Lattice.inf scene_gorder A = \<Inter>\<^sub>S A"
proof -
  have "Lattice.inf scene_gorder A = Lattice.inf scene_gorder (A \<inter> scene_space)"
    by (metis Eps_cong carrier_scene_gorder complete_lattice.is_glb_modulo_carrier scene_space_complete_lattice inf_def)
  also have "... = \<Inter>\<^sub>S (A \<inter> scene_space)"
    by (simp add: inf_scene_space)
  also have "... = \<Inter>\<^sub>S A"
    by (simp add: Inf_scene_def inj_uminus_scene image_Int Sup_scene_def uminus_image_scene_space)
  finally show ?thesis .
qed

lemma scene_gorder_eqs [simp]:
  "Order.top scene_gorder = \<top>\<^sub>S"
  "Order.bottom scene_gorder = \<bottom>\<^sub>S"
proof -
  interpret ss_clat: complete_lattice scene_gorder
    by (simp add: scene_space_complete_lattice)
  show "Order.top scene_gorder = \<top>\<^sub>S"
    by (metis gorder.simps(1) partial_object.simps(1) scene_gorder_def scene_top_greatest ss_clat.le_antisym ss_clat.top_closed ss_clat.top_higher top_scene_space)
  show "Order.bottom scene_gorder = \<bottom>\<^sub>S"
    by (metis gorder.simps(1) partial_object.simps(1) scene_bot_least scene_gorder_def scene_space.intros(1) ss_clat.bottom_lower ss_clat.le_antisym ss_clat.weak_partial_order_bottom_axioms
        weak_partial_order_bottom.bottom_closed)
qed

interpretation ss_clat: complete_lattice scene_gorder  
  rewrites "carrier scene_gorder = scene_space" and "elem scene_gorder = (\<in>)"  and "le scene_gorder = (\<subseteq>\<^sub>S)" and "eq scene_gorder = (=)" and "Order.top scene_gorder = \<top>\<^sub>S" and "Order.bottom scene_gorder = \<bottom>\<^sub>S"
  and "Lattice.sup scene_gorder = (\<Union>\<^sub>S)" and "Lattice.inf scene_gorder = (\<Inter>\<^sub>S)" and "Lattice.join scene_gorder = (\<union>\<^sub>S)" and "Lattice.meet scene_gorder = (\<inter>\<^sub>S)"
  by (auto simp add: scene_space_complete_lattice elem_def set_eq_def sup_scene_space_def fun_eq_iff join_def meet_def ss_union_def ss_inter_def sup_scene_space_eq inf_scene_space_eq)

(* Remove some unhelpful theorems *)

hide_fact Congruence.set_eqI
declare ss_clat.refl [simp del]
declare ss_clat.mem_imp_elem [simp del]

text \<open> Laws of Boolean algebra \<close>

lemma scene_space_compl1: 
  assumes "A \<in> scene_space"
  shows "A \<inter>\<^sub>S -A = \<bottom>\<^sub>S"
  by (metis assms idem_scene_space image_iff inf_scene_def inf_scene_inter scene_union_compl uminus_bot_scene uminus_image_scene_space uminus_scene_twice)

lemma scene_space_compl2:
  assumes "A \<in> scene_space"
  shows "A \<union>\<^sub>S -A = \<top>\<^sub>S"
  by (simp add: assms idem_scene_space scene_space_uminus scene_union_compl sup_scene_union)

lemma minus_scene_space:
  assumes "A \<in> scene_space" "B \<in> scene_space"
  shows "A - B = A \<inter>\<^sub>S - B"
  by (simp add: assms inf_scene_inter minus_scene_def scene_space_uminus)

lemma scene_union_dist: 
  assumes "A \<in> scene_space" "B \<in> scene_space" "C \<in> scene_space"
  shows "A \<union>\<^sub>S (B \<inter>\<^sub>S C) = (A \<union>\<^sub>S B) \<inter>\<^sub>S (A \<union>\<^sub>S C)"
  by (metis assms(1,2,3) inf_scene_inter scene_space_class.scene_union_inter_distrib ss_clat.join_closed ss_clat.meet_closed sup_scene_union)

lemma Sup_scene_dist:
  assumes "a \<in> scene_space" "B \<subseteq> scene_space"
  shows "a \<union>\<^sub>S (\<Inter>\<^sub>S B) = \<Inter>\<^sub>S {a \<union>\<^sub>S b | b. b \<in> B}"
proof -
  have fB: "finite B"
    using assms(2) finite_scene_space rev_finite_subset by blast
  from fB assms show ?thesis
  proof (induct arbitrary: a rule: finite_induct)
    case empty
    then show ?case
      using ss_clat.weak_le_iff_meet by auto
  next
    case (insert x F)
    then show ?case
    proof -
      from insert have ss_a: "{a \<union>\<^sub>S b |b. b \<in> F} \<subseteq> scene_space"
        by auto
      have "a \<union>\<^sub>S \<Inter>\<^sub>S (insert x F) = a \<union>\<^sub>S (x \<inter>\<^sub>S \<Inter>\<^sub>S F)"
        using insert by (simp)
      moreover have "... = (a \<union>\<^sub>S x) \<inter>\<^sub>S (a \<union>\<^sub>S \<Inter>\<^sub>S F)"
        using insert by (simp add: scene_union_dist)
      moreover from insert have "... = (a \<union>\<^sub>S x) \<inter>\<^sub>S \<Inter>\<^sub>S {a \<union>\<^sub>S b | b. b \<in> F}"
        by simp
      moreover from insert ss_a have "... = \<Inter>\<^sub>S (insert (a \<union>\<^sub>S x) {a \<union>\<^sub>S b | b. b \<in> F})"
        by simp
      moreover have "... = \<Inter>\<^sub>S {a \<union>\<^sub>S b |b. b \<in> insert x F}"
      proof -
        from insert have "insert (a \<union>\<^sub>S x) {a \<union>\<^sub>S b |b. b \<in> F} = {a \<union>\<^sub>S b |b. b \<in> insert x F}"
          by auto
        thus ?thesis by simp
      qed
      ultimately show ?thesis
        using insert ss_a by simp
    qed
  qed
qed

lemma scene_inter_dist: 
  assumes "A \<in> scene_space" "B \<in> scene_space" "C \<in> scene_space"
  shows "A \<inter>\<^sub>S (B \<union>\<^sub>S C) = (A \<inter>\<^sub>S B) \<union>\<^sub>S (A \<inter>\<^sub>S C)"
  by (metis (no_types, opaque_lifting) Sup_scene_closed assms(1,2,3) inf_scene_inter scene_inter_union_distrib ss_clat.meet_closed ss_union_def sup_scene_union)

lemma Inf_scene_dist:
  assumes "a \<in> scene_space" "B \<subseteq> scene_space"
  shows "a \<inter>\<^sub>S (\<Union>\<^sub>S B) = \<Union>\<^sub>S {a \<inter>\<^sub>S b | b. b \<in> B}"
proof -
  have 1: "{a \<inter>\<^sub>S b |b. b \<in> B} \<subseteq> scene_space"
    using assms(1,2) ss_clat.meet_closed by auto
  have "\<lbrakk>a\<rbrakk>\<^sub>S \<inter> \<Union> (scene_decomp ` B) = (\<Union> b\<in>B. \<lbrakk>a\<rbrakk>\<^sub>S \<inter> \<lbrakk>b\<rbrakk>\<^sub>S)"
    by blast
  also have "... = (\<Union> b\<in>B. \<lbrakk>a \<inter>\<^sub>S b\<rbrakk>\<^sub>S)"
    by (metis (no_types, lifting) SUP_cong assms(1,2) inf_scene_inter scene_decomp_inter subset_eq)
  also have "... = \<Union> (scene_decomp ` {a \<inter>\<^sub>S b |b. b \<in> B})"
    by auto
  finally show ?thesis
    by (force intro: scene_decomp_eq_transfer simp add: scene_decomp_transfer Sup_scene_closed scene_space_inter inf_scene_inter assms 1)
qed

lemma scene_union_diff: 
  assumes "A \<in> scene_space" "B \<in> scene_space" "C \<in> scene_space"
  shows "(A \<union>\<^sub>S B) - C = (A - C) \<union>\<^sub>S (B - C)"
  by (metis assms minus_scene_def minus_scene_space scene_inter_commute scene_inter_union_distrib scene_space_uminus ss_clat.meet_closed sup_scene_union)

lemma Sup_Vars_top: "\<Union>\<^sub>S (set Vars) = \<top>\<^sub>S"
  by (simp add: Sup_scene_is_foldr_scene top_scene_eq)

subsection \<open> Scene space and basis lenses \<close>

locale var_lens = vwb_lens +
  assumes lens_in_scene_space: "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> scene_space"

declare var_lens.lens_in_scene_space [simp]
declare var_lens.axioms(1) [simp]

locale basis_lens = vwb_lens +
  assumes lens_in_basis: "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> set Vars"

sublocale basis_lens \<subseteq> var_lens
  using lens_in_basis var_lens_axioms_def var_lens_def vwb_lens_axioms by blast

declare basis_lens.lens_in_basis [simp]

text \<open> Effectual variable and basis lenses need to have at least two view elements \<close>

abbreviation (input) evar_lens :: "('a::two \<Longrightarrow> 's::scene_space) \<Rightarrow> bool" 
  where "evar_lens \<equiv> var_lens"

abbreviation (input) ebasis_lens :: "('a::two \<Longrightarrow> 's::scene_space) \<Rightarrow> bool" 
  where "ebasis_lens \<equiv> basis_lens"

lemma basis_then_var [simp]: "basis_lens x \<Longrightarrow> var_lens x"
  using basis_lens.lens_in_basis basis_lens_def var_lens_axioms_def var_lens_def by blast

lemma basis_lens_intro: "\<lbrakk> vwb_lens x; \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> set Vars \<rbrakk> \<Longrightarrow> basis_lens x"
  using basis_lens.intro basis_lens_axioms.intro by blast

subsection \<open> Composite lenses \<close>

locale composite_lens = vwb_lens +
  assumes comp_in_Vars: "(\<lambda> a. a ;\<^sub>S x) ` set Vars \<subseteq> set Vars"
begin

lemma Vars_closed_comp: "a \<in> set Vars \<Longrightarrow> a ;\<^sub>S x \<in> set Vars"
  using comp_in_Vars by blast

lemma scene_space_closed_comp:
  assumes "a \<in> scene_space"
  shows "a ;\<^sub>S x \<in> scene_space"
proof -
  obtain xs where xs: "a = \<Squnion>\<^sub>S xs" "set xs \<subseteq> set Vars"
    using assms scene_space_vars_decomp by blast
  have "(\<Squnion>\<^sub>S xs) ;\<^sub>S x = \<Squnion>\<^sub>S (map (\<lambda> a. a ;\<^sub>S x) xs)"
    by (metis foldr_compat_dist pairwise_subset scene_space_compats xs(2))
  also have "... \<in> scene_space"
    by (auto simp add: scene_space_vars_decomp_iff)
       (metis comp_in_Vars image_Un le_iff_sup le_supE list.set_map xs(2))
  finally show ?thesis
    by (simp add: xs)
qed

sublocale var_lens
proof
  show "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> scene_space"
    by (metis scene_comp_top_scene scene_space_closed_comp top_scene_space vwb_lens_axioms)
qed

end

lemma composite_implies_var_lens [simp]:
  "composite_lens x \<Longrightarrow> var_lens x"
  by (metis composite_lens.axioms(1) composite_lens.scene_space_closed_comp scene_comp_top_scene top_scene_space var_lens_axioms.intro var_lens_def)

text \<open> The extension of any lens in the scene space remains in the scene space \<close>

lemma composite_lens_comp [simp]:
  "\<lbrakk> composite_lens a; var_lens x \<rbrakk> \<Longrightarrow> var_lens (x ;\<^sub>L a)"
  by (metis comp_vwb_lens composite_lens.scene_space_closed_comp composite_lens_def lens_scene_comp var_lens_axioms_def var_lens_def)

lemma comp_composite_lens [simp]:
  "\<lbrakk> composite_lens a; composite_lens x \<rbrakk> \<Longrightarrow> composite_lens (x ;\<^sub>L a)"
  by (auto intro!: composite_lens.intro simp add: composite_lens_axioms_def)
     (metis composite_lens.Vars_closed_comp composite_lens.axioms(1) scene_comp_assoc)

text \<open> A basis lens within a composite lens remains a basis lens (i.e. it remains atomic) \<close>

lemma composite_lens_basis_comp [simp]:
  "\<lbrakk> composite_lens a; basis_lens x \<rbrakk> \<Longrightarrow> basis_lens (x ;\<^sub>L a)"
  by (metis basis_lens.lens_in_basis basis_lens_def basis_lens_intro comp_vwb_lens composite_lens.Vars_closed_comp composite_lens_def lens_scene_comp)

lemma id_composite_lens: "composite_lens 1\<^sub>L"
  by (force intro: composite_lens.intro composite_lens_axioms.intro)

lemma fst_composite_lens: "composite_lens fst\<^sub>L"
  by (rule composite_lens.intro, simp add: fst_vwb_lens, rule composite_lens_axioms.intro, simp add: Vars_prod_def)

lemma snd_composite_lens: "composite_lens snd\<^sub>L"
  by (rule composite_lens.intro, simp add: snd_vwb_lens, rule composite_lens_axioms.intro, simp add: Vars_prod_def)

end