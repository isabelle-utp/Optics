section \<open> Scene Spaces \<close>

theory Scene_Spaces            
  imports Scenes Lens_Instances
begin

subsection \<open> Preliminaries \<close>

abbreviation foldr_scene :: "'a scene list \<Rightarrow> 'a scene" ("\<Squnion>\<^sub>S") where
"foldr_scene as \<equiv> foldr (\<squnion>\<^sub>S) as \<bottom>\<^sub>S"

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

lemma pairwise_compat_Vars_subset: "set xs \<subseteq> set Vars \<Longrightarrow> pairwise (##\<^sub>S) (set xs)"
  using pairwise_subset scene_space_compats by blast

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
  apply (auto simp add: scene_space_vars_decomp scene_space.Vars_scene_space scene_space_foldr)
  apply (simp add: scene_space.Vars_scene_space scene_space_foldr subset_eq)
  using scene_space_vars_decomp apply auto[1]
  by (meson dual_order.trans scene_space_foldr set_Vars_scene_space)

lemma "fold (\<squnion>\<^sub>S) (map (\<lambda>x. x ;\<^sub>S a) Vars) b = \<lbrakk>a\<rbrakk>\<^sub>\<sim> \<squnion>\<^sub>S b"
  oops

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

lemma scene_space_inter: "\<lbrakk> a \<in> scene_space; b \<in> scene_space \<rbrakk> \<Longrightarrow> a \<sqinter>\<^sub>S b \<in> scene_space"
  by (simp add: inf_scene_def scene_space.union_scene_space scene_space_uminus)

lemma scene_union_foldr_remove_element:
  assumes "set xs \<subseteq> set Vars"
  shows "a \<squnion>\<^sub>S \<Squnion>\<^sub>S xs = a \<squnion>\<^sub>S \<Squnion>\<^sub>S (removeAll a xs)"
using assms proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case apply auto
    apply (metis order_trans scene_space.Vars_scene_space scene_space_foldr scene_space_union_assoc scene_union_idem set_Vars_scene_space)
    apply (smt (verit, best) Diff_subset dual_order.trans removeAll_id scene_space_foldr scene_space_union_assoc scene_union_commute set_Vars_scene_space set_removeAll subset_iff)
    done
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
  using assms
  apply (auto simp add: scene_space_vars_decomp_iff union_scene_space_foldrs)
  by (smt (verit, ccfv_SIG) foldr_append scene_union_foldr_subset set_append sup.bounded_iff sup_commute sup_ge2)

find_theorems "- ?A \<subseteq>  ?B"

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
  using assms
  apply (simp only: union_scene_space_foldrs inter_scene_space_foldrs)
  apply (subst union_scene_space_foldrs)
    apply (simp add: assms)
   apply (simp add: assms)
  apply (subst inter_scene_space_foldrs)
    apply (simp)
   apply (simp)
  apply (rule foldr_scene_union_eq_sets)
  apply (simp)
   apply (smt (verit, ccfv_threshold) Un_subset_iff mem_Collect_eq pairwise_subset scene_space_compats subset_iff)
  apply (auto)
  done

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

lemma prop1:
  assumes "a \<in> scene_space" "b \<in> scene_space"
  shows "a \<squnion>\<^sub>S (b \<sqinter>\<^sub>S - a) = a \<squnion>\<^sub>S b"
  by (metis assms(1) assms(2) bot_idem_scene idem_scene_space idem_scene_uminus local.scene_union_inter_distrib scene_demorgan1 scene_space_uminus scene_union_compl scene_union_unit(1) uminus_scene_twice)

find_theorems "(##\<^sub>S)" "(\<sqinter>\<^sub>S)"

find_theorems "scene_space" "\<Squnion>\<^sub>S"

find_theorems "(##\<^sub>S)" scene_space

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
    apply (metis Cons.prems(2) assms(1) insert_subset list.simps(15) prop1 scene_union_commute)
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

find_theorems "(\<squnion>\<^sub>S)" "(\<le>)"

lemma scene_space_foldr_lb: 
  "\<lbrakk> a \<in> scene_space; set xs \<subseteq> scene_space; \<forall> b\<in>set xs. b \<le> a \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>S xs \<subseteq>\<^sub>S a"
proof (induct xs arbitrary: a)
  case Nil
  then show ?case
    by (simp add: scene_bot_least)
next
  case (Cons x xs)
  then show ?case apply (auto)
    apply (rule scene_union_lb)
    using scene_space_compat scene_space_foldr apply presburger
      apply blast
     apply (rule Cons(1))
      apply (simp_all)
  done
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

lemma foldr_scene_union_eq_scene_space: 
  "\<lbrakk> set xs \<subseteq> scene_space; set xs = set ys \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>S xs = \<Squnion>\<^sub>S ys"
  by (metis foldr_scene_union_eq_sets pairwise_def pairwise_subset scene_space_compat)
subsection \<open> Frame type \<close>

typedef (overloaded) 'a::scene_space frame = "scene_space :: 'a scene set"
  by blast

setup_lifting type_definition_frame

lemma UNIV_frame_scene_space: "UNIV = Abs_frame ` scene_space"
  by (metis Rep_frame Rep_frame_inverse UNIV_eq_I imageI)

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

instantiation frame :: (scene_space) bounded_lattice
begin

lift_definition bot_frame :: "'a frame" is "\<bottom>\<^sub>S" by (simp add: bot_scene_space)
lift_definition top_frame :: "'a frame" is "\<top>\<^sub>S" by (simp add: top_scene_space)

instance by (intro_classes; transfer; simp add: scene_bot_least scene_top_greatest)

end

abbreviation frame_empty :: "'s::scene_space frame" ("\<lbrace>\<rbrace>")
  where "\<lbrace>\<rbrace> \<equiv> bot"

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

instance frame :: (scene_space) complete_lattice
proof
  show Sup: "Sup ({} :: 'a frame set) = bot"
    by (transfer, simp)
  show Inf: "Inf ({} :: 'a frame set) = top"
    by (simp add: Inf_frame_def Sup)
  show le_Sup: "\<And>(x::'a frame) A. x \<in> A \<Longrightarrow> x \<le> Sup A"
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
  show "\<And>(x:: 'a frame) A. x \<in> A \<Longrightarrow> Inf A \<le> x"
  proof -
    fix x and A :: "'a frame set"
    assume xA: "x \<in> A"
    have "Inf A \<le> x \<longleftrightarrow> - Sup (uminus ` A) \<le> x"
      by (simp add: Inf_frame_def)
    also have "... \<longleftrightarrow> -x \<le> Sup (uminus ` A)"
      using compl_le_swap2 by blast
    also have "..."
      by (simp add: le_Sup xA)
    finally show "Inf A \<le> x" .
  qed
  show Sup_le: "\<And>(A::'a frame set) z. (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z"
  proof transfer
    fix z and A :: "'a scene set"
    assume a: "\<forall>x\<in>A. x \<in> scene_space" "z \<in> scene_space" "\<And>x. x \<in> scene_space \<Longrightarrow> x \<in> A \<Longrightarrow> x \<subseteq>\<^sub>S z"
    then obtain xs where xs: "set xs = A"
      by (metis finite_list finite_scene_space rev_finite_subset subsetI)
    with a show "\<Squnion>\<^sub>S (SOME xs. set xs = A) \<subseteq>\<^sub>S z"
      by (metis (mono_tags, lifting) scene_space_foldr_lb subset_iff tfl_some)
  qed
  show "\<And>(A :: 'a frame set) z. (\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A"
  proof -
    fix A :: "'a frame set" and z :: "'a frame"
    assume a: "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
    have "z \<le> Inf A \<longleftrightarrow> Sup (uminus ` A) \<le> - z"
      by (metis Inf_frame_def compl_le_swap1)
    also have "..."
      using a compl_le_compl_iff by (blast intro: Sup_le)
    finally show "z \<le> Inf A" .
  qed
qed

lemma uminus_frame_Inf: "- Inf (A :: 'a::scene_space frame set) = Sup (uminus ` A)"
  by (simp add: Inf_frame_def)

lemma uminus_frame_Sup: "- Sup (A :: 'a::scene_space frame set) = Inf (uminus ` A)"
  by (simp add: Inf_frame_def SUP_image)

subsection \<open> Frames as sets of basis scenes \<close>

locale basis_lens = vwb_lens +
  assumes lens_in_basis: "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> set Vars"

declare basis_lens.lens_in_basis [simp]

abbreviation (input) ebasis_lens :: "('a::two \<Longrightarrow> 's::scene_space) \<Rightarrow> bool" 
  where "ebasis_lens \<equiv> basis_lens"

lemma basis_then_vwb [simp]: "basis_lens x \<Longrightarrow> vwb_lens x"
  by (simp add: basis_lens_def)

lemma basis_lens_intro: "\<lbrakk> vwb_lens x; \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> set Vars \<rbrakk> \<Longrightarrow> basis_lens x"
  using basis_lens.intro basis_lens_axioms.intro by blast

lift_definition lens_frame :: "('a \<Longrightarrow> 's::scene_space) \<Rightarrow> 's frame" 
is "\<lambda> x. if basis_lens x then \<lbrakk>x\<rbrakk>\<^sub>\<sim> else \<bottom>\<^sub>S" by auto

definition lens_member :: "('a \<Longrightarrow> 's::scene_space) \<Rightarrow> 's frame \<Rightarrow> bool" (infix "\<in>\<^sub>F" 50)
  where "x \<in>\<^sub>F a \<longleftrightarrow> (lens_frame x \<le> a)"

abbreviation lens_not_member (infix "\<notin>\<^sub>F" 50) where "x \<notin>\<^sub>F A \<equiv> \<not> (x \<in>\<^sub>F A)"

lemma lens_member_frame [simp]: "x \<in>\<^sub>F lens_frame x"
  by (simp add: lens_member_def)

lemma lens_not_member_empty: "basis_lens x \<Longrightarrow> (x \<in>\<^sub>F \<lbrace>\<rbrace>) \<longleftrightarrow> x \<approx>\<^sub>L 0\<^sub>L"
  by (simp add: lens_member_def)
     (transfer, auto simp add: lens_equiv_scene scene_bot_least subscene_antisym zero_lens_scene)

lemma lens_not_member_empty_two: "ebasis_lens x \<Longrightarrow> x \<notin>\<^sub>F \<lbrace>\<rbrace>"
  using basis_then_vwb ief_lens_iff_zero lens_not_member_empty no_ief_two_view by blast

lemma lens_member_top: "x \<in>\<^sub>F top"
  by (simp add: lens_member_def)

lemma FUn_iff [simp]: "basis_lens x \<Longrightarrow> (x \<in>\<^sub>F a \<union>\<^sub>F b) = (x \<in>\<^sub>F a \<or> x \<in>\<^sub>F b)"
  by (simp add: lens_member_def)
     (transfer, simp add: var_le_union_iff)

lemma FCompl_iff: "ebasis_lens x \<Longrightarrow> x \<in>\<^sub>F - A \<longleftrightarrow> x \<notin>\<^sub>F A"
  apply (simp add: lens_member_def, auto)
  apply (metis (no_types, opaque_lifting) basis_then_vwb boolean_algebra.disj_cancel_right compl_le_compl_iff dual_order.trans ief_lens_iff_zero lens_member_def lens_not_member_empty no_ief_two_view sup.absorb2 top_greatest)
  apply (metis FUn_iff boolean_algebra.disj_cancel_right lens_member_def top_greatest)
  done

lemma FInter_iff [simp]: "basis_lens x \<Longrightarrow> (x \<in>\<^sub>F a \<inter>\<^sub>F b) = (x \<in>\<^sub>F a \<and> x \<in>\<^sub>F b)"
  by (simp add: lens_member_def)
  
definition lens_insert :: "('a \<Longrightarrow> 's::scene_space) \<Rightarrow> 's frame \<Rightarrow> 's frame"
  where "lens_insert x a = sup (lens_frame x) a"

lemma lens_insert_twice [simp]: "lens_insert x (lens_insert x A) = lens_insert x A"
  by (simp add: lens_insert_def)

lemma lens_insert_iff: 
  assumes "basis_lens x"
  shows "x \<in>\<^sub>F lens_insert y A \<longleftrightarrow> x \<approx>\<^sub>L 0\<^sub>L \<or> x \<approx>\<^sub>L y \<or> x \<in>\<^sub>F A"
  using assms
  apply (simp add: lens_insert_def lens_member_def)
  apply (transfer)
  apply (simp_all add: lens_equiv_scene scene_bot_least zero_lens_scene)
  apply (metis basis_lens.lens_in_basis basis_lens_axioms.intro basis_lens_def le_vars_then_equal lens_equiv_def lens_equiv_scene scene_bot_least scene_space_class.scene_space.Vars_scene_space scene_space_ub sublens_pres_vwb var_le_union_iff)
  done

lemma lens_insert_iff_two [simp]: 
  assumes "basis_lens (x :: 'a::two \<Longrightarrow> 's::scene_space)"
  shows "x \<in>\<^sub>F lens_insert y A \<longleftrightarrow> x \<approx>\<^sub>L y \<or> x \<in>\<^sub>F A"
  using assms basis_lens_def ief_lens_iff_zero lens_insert_iff no_ief_two_view by blast

lemma lens_insert_commute: "lens_insert x (lens_insert y A) = lens_insert y (lens_insert x A)"
  by (simp add: lens_insert_def sup.left_commute)
  
syntax
  "_frame_set" :: "args \<Rightarrow> 'a::scene_space frame"    ("\<lbrace>(_)\<rbrace>")
translations
  "\<lbrace>x, xs\<rbrace>" \<rightleftharpoons> "CONST lens_insert x \<lbrace>xs\<rbrace>"
  "\<lbrace>x\<rbrace>" \<rightleftharpoons> "CONST lens_insert x \<lbrace>\<rbrace>"

lift_definition frame_equiv :: "'a::scene_space \<Rightarrow> 'a \<Rightarrow> 'a frame \<Rightarrow> bool" ("_ \<approx>\<^sub>F _ on _" [65,0,66] 65)
  is "\<lambda> s\<^sub>1 s\<^sub>2 a. s\<^sub>1 \<approx>\<^sub>S s\<^sub>2 on a" .

lemma frame_equiv_empty [simp]: "s\<^sub>1 \<approx>\<^sub>F s\<^sub>2 on \<lbrace>\<rbrace>"
  by (transfer, simp)

lemma frame_equiv_refl [simp]: "s \<approx>\<^sub>F s on a"
  by (simp add: Rep_frame frame_equiv.rep_eq idem_scene_space scene_equiv_def)

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

subsection \<open> Alphabet Scene Spaces \<close>

text \<open> The scene space for an alphabet is constructed using the set of scenes corresponding to
  each lens, the base lens, and the more lens, to allow for extension. \<close>

definition alpha_scene_space :: "'s scene list \<Rightarrow> ('a \<Longrightarrow> 's) \<Rightarrow> ('b::scene_space \<Longrightarrow> 's) \<Rightarrow> 's scene list" where
"alpha_scene_space xs b\<^sub>L m\<^sub>L = xs @ map (\<lambda> x. x ;\<^sub>S m\<^sub>L) Vars"

lemma mem_alpha_scene_space_iff [simp]: 
  "x \<in> set (alpha_scene_space xs b\<^sub>L m\<^sub>L) \<longleftrightarrow> (x \<in> set xs \<or> x \<in> (\<lambda> x. x ;\<^sub>S m\<^sub>L) ` set Vars)"
  by (simp add: alpha_scene_space_def)

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
  ,simp_all add: scene_indeps_def pairwise_def lens_plus_scene[THEN sym] lens_equiv_scene[THEN sym] lens_equiv_sym
                 lens_quotient_vwb lens_quotient_indep lens_quotient_plus[THEN sym] lens_quotient_bij)

method basis_lens uses defs =
  (rule basis_lens_intro, simp_all add: defs alpha_scene_space_def lens_scene_comp[THEN sym] lens_quotient_vwb lens_quotient_comp)

alphabet test = 
  x :: bool
  y :: nat 
  z :: "int list"

alphabet test2 = test +
  u :: string

alphabet test3 = test +
  v :: string

instantiation test_ext :: (scene_space) scene_space
begin

definition Vars_test_ext :: "'a test_scheme scene list" where
"Vars_test_ext = alpha_scene_space [\<lbrakk>x\<rbrakk>\<^sub>\<sim>, \<lbrakk>y\<rbrakk>\<^sub>\<sim>, \<lbrakk>z\<rbrakk>\<^sub>\<sim>] test.base\<^sub>L test.more\<^sub>L"
  
instance by (alpha_scene_space defs: Vars_test_ext_def)

end

lemma basis_lens_x [simp]: "basis_lens x" by (basis_lens defs: Vars_test_ext_def)
lemma basis_lens_y [simp]: "basis_lens y" by (basis_lens defs: Vars_test_ext_def)
lemma basis_lens_z [simp]: "basis_lens z" by (basis_lens defs: Vars_test_ext_def)

term "\<lbrace>x, y, z\<rbrace>"

lemma "z \<in>\<^sub>F \<lbrace>x, y, z\<rbrace>"
  by simp

instantiation test2_ext :: (scene_space) scene_space
begin

definition Vars_test2_ext :: "'a test2_ext scene list" where
"Vars_test2_ext = alpha_scene_space [\<lbrakk>u /\<^sub>L test.more\<^sub>L\<rbrakk>\<^sub>\<sim>] (u /\<^sub>L test.more\<^sub>L) (test2.more\<^sub>L /\<^sub>L test.more\<^sub>L)"

instance
  by (alpha_scene_space defs: Vars_test2_ext_def)

end

lemma basis_lens_u [simp]: "basis_lens u" by (basis_lens defs: Vars_test_ext_def Vars_test2_ext_def)

(*
instantiation test3_ext :: (scene_space) scene_space
begin

definition Vars_test3_ext :: "'a test3_ext scene list" where
"Vars_test3_ext = alpha_scene_space [\<lbrakk>v /\<^sub>L test.more\<^sub>L\<rbrakk>\<^sub>\<sim>] (v /\<^sub>L test.more\<^sub>L) (test3.more\<^sub>L /\<^sub>L test.more\<^sub>L)"

instance
  by (alpha_scene_space defs: Vars_test3_ext_def)

lemma basis_lens_v [simp]: "basis_lens v" apply (basis_lens defs: Vars_test_ext_def Vars_test2_ext_def Vars_test3_ext_def)

end
*)

end