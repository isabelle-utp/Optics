section \<open> Scene Spaces \<close>

theory Scene_Spaces
  imports Scenes
begin

subsection \<open> Preliminaries \<close>

hide_const fold

abbreviation (input) "fold \<equiv> Finite_Set.fold"

locale compat_family =
  fixes S :: "'a scene set"
  assumes S_compat: "pairwise (##\<^sub>S) S"
      and S_finite: "finite S"
      and S_idem: "s \<in> S \<Longrightarrow> idem_scene s"
begin

(*
lemma cf_induct [case_names empty insert, induct set: finite]:
  \<comment> \<open>Discharging \<open>x \<notin> F\<close> entails extra work.\<close>
  assumes "A \<subseteq> S"
  assumes "P {}"
    and insert: "\<And>x A. A \<subseteq> S \<Longrightarrow> x \<notin> A \<Longrightarrow> x \<in> S \<Longrightarrow> P A \<Longrightarrow> P (insert x A)"
  shows "P A"*)

lemma union_compat_family:
  assumes "x \<in> S" "y \<in> S" "s \<in> S"
  shows "s ##\<^sub>S x \<squnion>\<^sub>S y"
proof -
  have "s ##\<^sub>S x" "s ##\<^sub>S y"
    using S_compat assms pairwiseD scene_compat_refl by metis+
  then show ?thesis
    by (rule scene_union_pres_compat)
qed

lemma fold_graph_compat:
  assumes "A \<subseteq> S" "\<forall>s \<in> S. s ##\<^sub>S z" "fold_graph (\<squnion>\<^sub>S) z A y"
  shows "\<forall>s \<in> S. s ##\<^sub>S y"
  using assms(3, 1, 2)
proof (induct set: fold_graph)
  case emptyI
  then show ?case
    by blast
next
  case (insertI x A y)
  then show ?case
    by (metis insert_subset scene_union_idem scene_union_pres_compat union_compat_family)
qed

lemma fold_graph_insertE_aux:
  assumes "A \<subseteq> S" 
  assumes "fold_graph (\<squnion>\<^sub>S) z A y" "a \<in> A" "\<forall>s \<in> S. s ##\<^sub>S z"
  shows "\<exists>y'. y = a \<squnion>\<^sub>S y' \<and> fold_graph (\<squnion>\<^sub>S) z (A - {a}) y'"
  using assms(2-,1)
proof (induct set: fold_graph)
  case emptyI
  then show ?case by simp
next
  case (insertI x A y)
  then show ?case
  proof (cases "x = a")
    case True
    with insertI show ?thesis by auto
  next
    case False
    then obtain y' where y: "y = a \<squnion>\<^sub>S y'" and y': "fold_graph (\<squnion>\<^sub>S) z (A - {a}) y'"
      using insertI by auto
    from this insertI have "x ##\<^sub>S a" "a ##\<^sub>S y'" "x ##\<^sub>S y'"
      apply simp_all
        apply (metis False S_compat in_mono pairwiseD)
        apply (metis False fold_graph_compat insert_Diff insert_subset)
        apply (metis False fold_graph_compat insert_Diff insert_subset)
      done
    then have "x \<squnion>\<^sub>S y = a \<squnion>\<^sub>S (x \<squnion>\<^sub>S y')"
      by (metis scene_compat_sym scene_union_assoc scene_union_commute y)
    moreover have "fold_graph (\<squnion>\<^sub>S) z (insert x A - {a}) (x \<squnion>\<^sub>S y')"
      using y' and \<open>x \<noteq> a\<close> and \<open>x \<notin> A\<close>
      by (simp add: insert_Diff_if fold_graph.insertI)
    ultimately show ?thesis
      by blast
  qed
qed

lemma fold_graph_insertE:
  assumes "insert x A \<subseteq> S" "\<forall>s \<in> S. s ##\<^sub>S z"
  assumes "fold_graph (\<squnion>\<^sub>S) z (insert x A) v" and "x \<notin> A"
  obtains y where "v = x \<squnion>\<^sub>S y" and "fold_graph (\<squnion>\<^sub>S) z A y"
  using assms by (auto dest: fold_graph_insertE_aux[OF \<open>insert x A \<subseteq> S\<close> _ insertI1])

lemma fold_graph_determ:
  assumes "A \<subseteq> S" "\<forall>s \<in> S. s ##\<^sub>S z"
  assumes "fold_graph (\<squnion>\<^sub>S) z A x" "fold_graph (\<squnion>\<^sub>S) z A y"
  shows "y = x"
  using assms(3-,1,2)
proof (induct arbitrary: y set: fold_graph)
  case emptyI
  then show ?case
    by (meson empty_fold_graphE)
next
  case (insertI x A y v)
  from \<open>insert x A \<subseteq> S\<close> and \<open>fold_graph (\<squnion>\<^sub>S) z (insert x A) v\<close> and \<open>x \<notin> A\<close>
  obtain y' where "v = x \<squnion>\<^sub>S y'" and "fold_graph (\<squnion>\<^sub>S) z A y'"
    by (meson compat_family.fold_graph_insertE compat_family_axioms insertI.prems(3))
  from \<open>fold_graph (\<squnion>\<^sub>S) z A y'\<close> insertI have "y' = y"
    by simp
  with \<open>v = x \<squnion>\<^sub>S y'\<close> show "v = x \<squnion>\<^sub>S y"
    by simp
qed

lemma fold_equality: 
  assumes "A \<subseteq> S" "\<forall>s \<in> S. z ##\<^sub>S s" "fold_graph (\<squnion>\<^sub>S) z A y"
  shows "fold (\<squnion>\<^sub>S) z A = y"
  unfolding Finite_Set.fold_def
proof -
  from assms(1) have "finite A"
    using S_finite rev_finite_subset by blast
  moreover have "The (fold_graph (\<squnion>\<^sub>S) z A) = y"
    by (metis assms fold_graph_determ scene_compat_sym the_equality)
  ultimately show "(if finite A then The (fold_graph (\<squnion>\<^sub>S) z A) else z) = y"
    by simp
qed

lemma fold_graph_fold:
  assumes "A \<subseteq> S" "\<forall>s \<in> S. s ##\<^sub>S z"
  assumes "finite A"
  shows "fold_graph (\<squnion>\<^sub>S) z A (fold (\<squnion>\<^sub>S) z A)"
proof -
  from \<open>finite A\<close> have "\<exists>x. fold_graph (\<squnion>\<^sub>S) z A x"
    by (rule finite_imp_fold_graph)
  moreover note fold_graph_determ[OF \<open>A \<subseteq> S\<close>]
  ultimately have "\<exists>!x. fold_graph (\<squnion>\<^sub>S) z A x"
    using assms(2) by blast
  then have "fold_graph (\<squnion>\<^sub>S) z A (The (fold_graph (\<squnion>\<^sub>S) z A))"
    by (rule theI')
  with assms show ?thesis
    by (simp add: Finite_Set.fold_def)
qed

text \<open>The various recursion equations for \<^const>\<open>fold\<close>:\<close>

lemma fold_insert':
  assumes "insert x A \<subseteq> S" "x \<notin> A" "\<forall>s \<in> S. z ##\<^sub>S s"
  shows "fold (\<squnion>\<^sub>S) z (insert x A) = (\<squnion>\<^sub>S) x (fold (\<squnion>\<^sub>S) z A)"
proof (rule fold_equality[OF \<open>insert x A \<subseteq> S\<close> \<open>\<forall>s \<in> S. z ##\<^sub>S s\<close>])
  from \<open>insert x A \<subseteq> S\<close>have "fold_graph (\<squnion>\<^sub>S) z A (fold (\<squnion>\<^sub>S) z A)"
    by (metis S_finite assms(3) finite_imp_fold_graph fold_equality insert_subset rev_finite_subset)
  with \<open>x \<notin> A\<close>  have "fold_graph (\<squnion>\<^sub>S) z (insert x A) ((\<squnion>\<^sub>S) x (fold (\<squnion>\<^sub>S) z A))"
    by (rule fold_graph.insertI)
  then show "fold_graph (\<squnion>\<^sub>S) z (insert x A) ((\<squnion>\<^sub>S) x (fold (\<squnion>\<^sub>S) z A))"
    by simp
qed

lemma fold_fun_left_comm:
  assumes "insert x A \<subseteq> S" "\<forall>s \<in> S. z ##\<^sub>S s"
  shows "x \<squnion>\<^sub>S (fold (\<squnion>\<^sub>S) z A) = fold (\<squnion>\<^sub>S) (x \<squnion>\<^sub>S z) A"
proof -
  have "finite A"
    using S_finite assms finite_subset by auto
  then show ?thesis
    using assms
proof (induct rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert y F)
  then have "fold (\<squnion>\<^sub>S) (x \<squnion>\<^sub>S z) (insert y F) = (\<squnion>\<^sub>S) y (fold (\<squnion>\<^sub>S) (x \<squnion>\<^sub>S z) F)"
    by (metis fold_insert' insert.prems(2) insert_subset scene_compat_sym scene_union_idem
              scene_union_pres_compat union_compat_family)
  also have "\<dots> = x \<squnion>\<^sub>S (y \<squnion>\<^sub>S (fold (\<squnion>\<^sub>S) z F))"
    using insert
    apply auto
    by (smt (verit, ccfv_threshold) compat_family.fold_graph_compat compat_family.fold_graph_fold compat_family.union_compat_family compat_family_axioms scene_compat_sym scene_union_assoc scene_union_commute scene_union_idem)
  also have "\<dots> = (\<squnion>\<^sub>S) x (fold (\<squnion>\<^sub>S) z (insert y F))"
  proof -
    from insert have "insert y F \<subseteq> S" by simp
    from fold_insert'[OF this] insert show ?thesis
      by simp
  qed
  finally show ?case ..
qed
qed

text \<open> Only holds for idempotent operators \<close>
lemma fold_insert[simp]:
  assumes "insert x A \<subseteq> S" "\<forall>s \<in> S. z ##\<^sub>S s"
  shows "fold (\<squnion>\<^sub>S) z (insert x A) = x \<squnion>\<^sub>S (fold (\<squnion>\<^sub>S) z A)"
proof (cases "x \<in> A")
  case True
  then obtain B where B: "A = insert x B" and "x \<notin> B"
    by (meson Set.set_insert)
  then have "x \<squnion>\<^sub>S (fold (\<squnion>\<^sub>S) z A) = x \<squnion>\<^sub>S (fold (\<squnion>\<^sub>S) z (insert x B))"
    by blast
  also have "... = x \<squnion>\<^sub>S (x \<squnion>\<^sub>S (fold (\<squnion>\<^sub>S) z B))"
    using B \<open>x \<notin> B\<close> assms fold_insert' by auto
  also have "... = (x \<squnion>\<^sub>S x) \<squnion>\<^sub>S (fold (\<squnion>\<^sub>S) z B)"
    by (metis B S_finite assms compat_family.union_compat_family compat_family_axioms fold_graph_compat fold_graph_fold insert_subset rev_finite_subset scene_compat_sym scene_union_assoc scene_union_idem)
  finally show ?thesis
    by (metis B \<open>x \<notin> B\<close> assms fold_insert' insert_absorb2 scene_union_idem)
next
  case False
  then show ?thesis
    using assms fold_insert' by presburger
qed

declare (in -) empty_fold_graphE [rule del] fold_graph.intros [rule del]
  \<comment> \<open>No more proofs involve these.\<close>

lemma fold_rec:
  assumes "A \<subseteq> S" "x \<in> A" "\<forall>s \<in> S. z ##\<^sub>S s"
  shows "fold (\<squnion>\<^sub>S) z A = x \<squnion>\<^sub>S (fold (\<squnion>\<^sub>S) z (A - {x}))"
proof -
  have A: "A = insert x (A - {x})"
    using \<open>x \<in> A\<close> by blast
  then have "fold (\<squnion>\<^sub>S) z A = fold (\<squnion>\<^sub>S) z (insert x (A - {x}))"
    by simp
  also have "\<dots> = x \<squnion>\<^sub>S (fold (\<squnion>\<^sub>S) z (A - {x}))"
    by (rule fold_insert) (use assms in \<open>auto\<close>)
  finally show ?thesis .
qed

lemma fold_insert_remove:
  assumes "insert x A \<subseteq> S" "\<forall>s \<in> S. z ##\<^sub>S s"
  assumes "finite A"
  shows "fold (\<squnion>\<^sub>S) z (insert x A) = x \<squnion>\<^sub>S (fold (\<squnion>\<^sub>S) z (A - {x}))"
proof -
  from \<open>finite A\<close> have "finite (insert x A)"
    by auto
  moreover have "x \<in> insert x A"
    by auto
  ultimately have "fold (\<squnion>\<^sub>S) z (insert x A) = x \<squnion>\<^sub>S (fold (\<squnion>\<^sub>S) z (insert x A - {x}))"
    using assms fold_rec by presburger
  then show ?thesis
    by simp
qed

lemma fold_compat_single:
  assumes "A \<subseteq> S" "\<forall>s \<in> S. z ##\<^sub>S s" "\<forall>s \<in> A. x ##\<^sub>S s" "x ##\<^sub>S z"
  shows "x ##\<^sub>S fold (\<squnion>\<^sub>S) z A"
proof -
  have "finite A"
    using S_finite assms(1) rev_finite_subset by blast
  then show ?thesis
    using assms
  proof induct
    case empty
    then show ?case
      by simp
  next
    case (insert a F)
    have "x ##\<^sub>S a" "x ##\<^sub>S fold (\<squnion>\<^sub>S) z F"
      using insert.prems insert.hyps by blast+
    then have "x ##\<^sub>S (a \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) z F)"
      using scene_union_pres_compat by blast
    then show ?case
      using insert.prems(1) insert.prems(2) by auto
  qed
qed

lemma fold_compat_folds:  
  assumes "(A \<union> B) \<subseteq> S" "\<forall>s \<in> S. z ##\<^sub>S s"
  shows "fold (\<squnion>\<^sub>S) z B ##\<^sub>S fold (\<squnion>\<^sub>S) z A"
  by (smt (verit, del_insts) assms compat_family.S_compat compat_family_axioms fold_compat_single
      in_mono pairwise_def scene_compat_refl scene_compat_sym sup.boundedE)

lemma fold_set_union_disj:
  assumes "A \<subseteq> S" "B \<subseteq> S" "A \<inter> B = {}" "\<forall>s \<in> S. z ##\<^sub>S s"
  shows "fold (\<squnion>\<^sub>S) z (A \<union> B) = fold (\<squnion>\<^sub>S) (fold (\<squnion>\<^sub>S) z A) B"
proof -
  have "finite B"
    using S_finite assms(2) infinite_super by auto
  then show ?thesis
    using assms
proof induct
case (insert x F)
  have "fold (\<squnion>\<^sub>S) z (A \<union> insert x F) = x \<squnion>\<^sub>S (fold (\<squnion>\<^sub>S) (fold (\<squnion>\<^sub>S) z A) F)"
    using insert by (simp add: fold_insert)
  also have "\<dots> = fold (\<squnion>\<^sub>S) (fold (\<squnion>\<^sub>S) z A) (insert x F)"
    using insert fold_insert apply auto
    by (metis (full_types) S_finite compat_family.fold_graph_compat compat_family_axioms finite_subset fold_graph_fold fold_insert insert.prems(2) scene_compat_sym)
  finally show ?case .
qed simp
qed

lemma fold_member_un_idem:
  assumes "x \<in> A" "A \<subseteq> S" "\<forall>s \<in> S. z ##\<^sub>S s"
  shows "x \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) z A = fold (\<squnion>\<^sub>S) z A"
proof -
  have "finite A"
    using S_finite assms(2) finite_subset by blast
  then show ?thesis
    using assms
proof (induction)
  case empty
  then show ?case by blast
next
  case (insert a F)
  then show ?case
    by (metis fold_insert insert_absorb)
qed
qed

lemma fold_un_zero_idem:
  assumes "A \<subseteq> S" "\<forall>s \<in> S. z ##\<^sub>S s"
  shows "z \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) z A = fold (\<squnion>\<^sub>S) z A"
proof -
  have "finite A"
    using S_finite assms(1) finite_subset by blast
  then show ?thesis
    using assms
proof (induction)
  case empty
  then show ?case
    by (simp add: scene_union_idem)
next
  case (insert x F)
  have "z \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) z (insert x F) = z \<squnion>\<^sub>S x \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) z F"
    apply (subst fold_insert)
    using insert apply auto
    apply (subst scene_union_assoc)
       apply blast
      apply (simp_all add: fold_compat_single scene_compat_refl subset_iff)
    by (metis S_compat fold_compat_single insert.prems(1) insert_subset pairwise_insert pairwise_subset scene_compat_sym)
  then show ?case
    by (smt (verit, ccfv_SIG) assms(2) compat_family.fold_insert' compat_family.fold_member_un_idem compat_family_axioms insert.IH insert.hyps(2) insert.prems(1) insertCI insert_subset scene_union_assoc scene_union_commute scene_union_incompat scene_union_unit(1))
qed
qed

lemma fold_subset_union_idem:
  assumes "A \<subseteq> B" "B \<subseteq> S" "\<forall>s \<in> S. z ##\<^sub>S s"
  shows "fold (\<squnion>\<^sub>S) z B = fold (\<squnion>\<^sub>S) z A \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) z B"
proof -
  have "finite A" "finite B"
    by (meson S_finite assms(1) assms(2) rev_finite_subset)+
  from this assms show ?thesis
proof (induct)
  case empty
  have "fold (\<squnion>\<^sub>S) z {} \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) z B = z \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) z B"
    by simp
  then show ?case
    using empty.prems(3,4) fold_un_zero_idem by presburger
next
  case (insert x F)
  have "fold (\<squnion>\<^sub>S) z (insert x F) \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) z B = x \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) z F \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) z B"
    by (metis dual_order.trans fold_insert insert.prems(2-4))
  also have "... = fold (\<squnion>\<^sub>S) z F \<squnion>\<^sub>S (x \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) z B)"
    apply (subst scene_union_assoc)
       apply (subst scene_compat_sym)
        apply (metis S_compat fold_compat_single insert.prems(2) insert.prems(3) insert.prems(4) insert_subset pairwise_insert pairwise_subset scene_compat_refl scene_compat_sym subset_trans)
       apply simp_all
      apply (metis fold_compat_folds insert.prems(2) insert.prems(3) insert.prems(4) insert_subset sup.order_iff)
     apply (metis S_compat fold_compat_single in_mono insert.prems(2) insert.prems(3) insert.prems(4) insert_subset pairwiseD scene_compat_refl scene_compat_sym)
    by (simp add: scene_union_commute)
  finally show ?case
    using insert by (metis fold_member_un_idem insert_subset)
qed
qed

end

lemma compat_family_subset: "X \<subseteq> Y \<Longrightarrow> compat_family Y \<Longrightarrow> compat_family X"
  by (meson compat_family_def in_mono pairwise_subset rev_finite_subset)

lemma compat_family_empty: "compat_family {}"
  by (simp add: compat_family_def)

lemma compat_family_singleton: "idem_scene x \<Longrightarrow> compat_family {x}"
  by (simp add: compat_family_def)

abbreviation fold_scene :: "'a scene set \<Rightarrow> 'a scene" ("\<Squnion>\<^sub>S") where
"fold_scene as \<equiv> Finite_Set.fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S as" 

lemma fold_scene_insert: 
  assumes "idem_scene x" "compat_family A" "\<forall>s \<in> A. x ##\<^sub>S s"
  shows "\<Squnion>\<^sub>S (insert x A) = x \<squnion>\<^sub>S (\<Squnion>\<^sub>S A)"
  by (metis (no_types, opaque_lifting) assms compat_family.fold_insert compat_family_def finite_insert insert_iff pairwise_insert scene_compat_bot(2) scene_compat_sym set_eq_subset)

lemma fold_scene_singleton: "idem_scene x \<Longrightarrow> \<Squnion>\<^sub>S {x} = x"
  by (simp add: compat_family_empty fold_scene_insert)

lemma fold_scene_union:
  assumes "pairwise (##\<^sub>S) (X \<union> Y)" "finite (X \<union> Y)" "\<forall>x \<in> (X \<union> Y). idem_scene x"
  shows "\<Squnion>\<^sub>S (X \<union> Y) = \<Squnion>\<^sub>S X \<squnion>\<^sub>S \<Squnion>\<^sub>S Y"
proof -
  have "finite Y"
    using assms(2) by fastforce
  moreover have compat_family: "compat_family X" "compat_family Y" "compat_family (X \<union> Y)"
    using assms pairwise_mono by (unfold_locales; auto)+
  ultimately show ?thesis
proof induct
    case empty
    then show ?case by simp
  next
    case (insert x F)
    have 1: "x \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S F = fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S (insert x F)"
      by (metis compat_family.fold_insert insert.prems(2) insertCI insert_subset scene_compat_bot(2) subset_insertI)
    have "fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S (X \<union> insert x F) = x \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S (X \<union> F)"
      by (metis Un_insert_right compat_family.fold_insert dual_order.refl insert.prems(3) scene_compat_bot(2))
    also have "... = x \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S X \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S F"
      apply (subst insert)
         apply (simp add: insert)
        apply (meson compat_family_subset insert.prems(2) subset_insertI)
       apply (metis Un_insert_right compat_family_subset insert.prems(3) subset_insertI)
      apply (rule scene_union_assoc)
        apply (meson compat_family.S_finite compat_family.fold_graph_compat compat_family.fold_graph_fold insert.prems insertCI scene_compat_bot(1) subset_iff sup_ge1 sup_ge2)
       apply (meson compat_family.fold_graph_compat compat_family.fold_graph_fold insert.hyps(1) insert.prems(2) insert_iff scene_compat_bot(1) subset_insertI)
      by (metis Un_insert_right compat_family.fold_compat_folds inf_sup_aci(5) insert.prems(3) le_supI scene_compat_bot(2) sup.cobounded1)
    also have "... = fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S X \<squnion>\<^sub>S (x \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S F)"
      apply (subst scene_union_assoc)
         apply (metis Un_insert_right assms(2) compat_family.fold_equality compat_family.fold_graph_compat finite_Un finite_imp_fold_graph insert.prems(3) insertI1 scene_compat_bot(1) scene_compat_sym sup_commute sup_ge2)
        apply (metis Un_insert_right Un_subset_iff compat_family.fold_compat_folds insert.prems(3) scene_compat_bot(2) subset_insertI)
       apply (metis compat_family.S_compat compat_family.fold_compat_single insert.prems(2) pairwise_insert scene_compat_bot(1) scene_compat_bot(2) scene_compat_refl subset_insertI)
      by (simp add: scene_union_commute)
    finally show ?case
      using 1 by presburger
  qed
qed

lemma fold_scene_idem:
  assumes "compat_family A"
  shows "idem_scene (\<Squnion>\<^sub>S A)"
proof -
  from assms have "finite A"
    by (simp add: compat_family.S_finite finite_UnionD)
  then show ?thesis
    using assms proof induct
    case empty
    then show ?case by simp
  next
    case (insert x F)
    then show ?case
      by (metis compat_family.S_idem compat_family.fold_insert' compat_family_subset dual_order.eq_iff idem_scene_union insertI1 scene_compat_bot(2) subset_insertI) 
  qed
qed

lemma compat_family_insertI:
  assumes "idem_scene x" "compat_family A" "\<forall>s \<in> A. x ##\<^sub>S s"
  shows "compat_family (insert x A)"
  by (metis (full_types) assms compat_family_def finite_insert insert_iff pairwise_insert scene_compat_sym)

lemma compat_family_Un_folds_compat:
  "compat_family (A \<union> B) \<Longrightarrow> \<Squnion>\<^sub>S A ##\<^sub>S \<Squnion>\<^sub>S B"
  by (simp add: compat_family.fold_compat_folds)

lemma compat_family_union:
  assumes "compat_family A" "B \<subseteq> A" "C \<subseteq> A"
  shows "compat_family (B \<union> C)"
  by (meson Un_least assms compat_family_subset)

lemma compat_family_fold_image:
  assumes "compat_family (\<Union> A)"
  shows "compat_family (\<Squnion>\<^sub>S ` A)"
proof -
  from assms have "finite A"
    by (simp add: compat_family.S_finite finite_UnionD)
  then show ?thesis
    using assms proof induct
    case empty
    then show ?case by simp
  next
    case (insert x F)
    have cf_UF: "compat_family (\<Union> F)"
      by (meson Union_mono compat_family_subset insert.prems subset_insertI)
    have cf_x: "compat_family x"
      by (meson Sup_upper compat_family_subset insert.prems insertI1)
    have idem: "idem_scene (\<Squnion>\<^sub>S x)"
      using cf_x fold_scene_idem by blast
    have compats: "\<forall>s\<in>\<Squnion>\<^sub>S ` F. \<Squnion>\<^sub>S x ##\<^sub>S s"
      by auto
        (meson Sup_upper compat_family.fold_compat_folds insert.prems insertCI le_sup_iff scene_compat_bot(2))
    show ?case
      by (simp add: cf_UF compat_family_insertI compats idem insert.hyps(3))
  qed
qed

lemma fold_scene_Union:
  assumes "compat_family (\<Union> xs)"
  shows "\<Squnion>\<^sub>S (\<Union> xs) = \<Squnion>\<^sub>S (\<Squnion>\<^sub>S ` xs)"
proof -
  from assms have "finite xs"
    by (simp add: compat_family.S_finite finite_UnionD)
  then show ?thesis
    using assms
proof induct
  case empty
  then show ?case by auto
next
  case (insert x F)
  have cf_UF: "compat_family (\<Union> F)"
    by (meson Union_mono compat_family_subset insert.prems subset_insertI)
  have cf_x: "compat_family x"
    by (meson Sup_upper compat_family_subset insert.prems insertI1)
  with insert have "\<Squnion>\<^sub>S (\<Union> F) = \<Squnion>\<^sub>S (\<Squnion>\<^sub>S ` F)"
    using cf_UF by blast
  then show ?case
    apply (simp)
    apply (subst fold_scene_union)
    apply (metis Sup_insert compat_family.S_compat insert.prems)
    apply (metis Union_insert compat_family.S_finite insert.prems)
     apply (metis Sup_insert compat_family.S_idem insert.prems)
    apply (simp)
    apply (subst fold_scene_insert)
       apply (simp_all)
    apply (rule fold_scene_idem)
    using cf_x apply linarith
    using cf_UF compat_family_fold_image apply blast
    apply (meson Sup_upper compat_family_Un_folds_compat compat_family_union insert.prems insert_iff)
    done
  qed
qed

lemma fold_scene_indeps:
  assumes "\<forall> x \<in> xs. y \<bowtie>\<^sub>S x" "compat_family xs"
  shows "y \<bowtie>\<^sub>S \<Squnion>\<^sub>S xs"
proof (induct xs)
  oops

subsection \<open> Predicates \<close>

text \<open> All scenes in the set are independent \<close>

definition scene_indeps :: "'s scene set \<Rightarrow> bool" where
"scene_indeps = pairwise (\<bowtie>\<^sub>S)"

text \<open> All scenes in the set cover the entire state space \<close>

definition scene_span :: "'s scene set \<Rightarrow> bool" where
"scene_span S = (Finite_Set.fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S S = \<top>\<^sub>S)"

text \<open> cf. @{term finite_dimensional_vector_space}, which scene spaces are based on. \<close>  

subsection \<open> Scene space class \<close>

class scene_space =
  fixes Vars :: "'a scene set"
  assumes idem_scene_Vars [simp]: "\<And> x. x \<in> Vars \<Longrightarrow> idem_scene x"
  and finite_Vars: "finite Vars"
  and indep_Vars: "scene_indeps Vars"
  and span_Vars: "scene_span Vars"
begin

lemma scene_space_compats [simp]: "pairwise (##\<^sub>S) Vars"
  by (metis local.indep_Vars pairwise_alt scene_indep_compat scene_indeps_def)

lemma Vars_ext_lens_indep: "\<lbrakk> a ;\<^sub>S x \<noteq> b ;\<^sub>S x; a \<in> Vars; b \<in> Vars \<rbrakk> \<Longrightarrow> a ;\<^sub>S x \<bowtie>\<^sub>S b ;\<^sub>S x"
  by (metis indep_Vars pairwiseD scene_comp_indep scene_indeps_def)

inductive_set scene_space :: "'a scene set" where
bot_scene_space [intro]: "\<bottom>\<^sub>S \<in> scene_space" | 
Vars_scene_space [intro]: "x \<in> Vars \<Longrightarrow> x \<in> scene_space" |
union_scene_space [intro]: "\<lbrakk> x \<in> scene_space; y \<in> scene_space \<rbrakk> \<Longrightarrow> x \<squnion>\<^sub>S y \<in> scene_space"

lemma idem_scene_space: "a \<in> scene_space \<Longrightarrow> idem_scene a"
  by (induct rule: scene_space.induct)
     (auto simp add: idem_scene_Vars)

lemma set_Vars_scene_space [simp]: "Vars \<subseteq> scene_space"
  by blast

lemma pairwise_compat_Vars_subset: "xs \<subseteq> Vars \<Longrightarrow> pairwise (##\<^sub>S) xs"
  using pairwise_subset scene_space_compats by blast

lemma Vars_compat_scene_space: "\<lbrakk> b \<in> scene_space; x \<in> Vars \<rbrakk> \<Longrightarrow> x ##\<^sub>S b"
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

lemma scene_space_vars_decomp: "a \<in> scene_space \<Longrightarrow> \<exists>xs. xs \<subseteq> Vars \<and> \<Squnion>\<^sub>S xs = a"
proof (induct rule: scene_space.induct)
  case bot_scene_space
  then show ?case
    by (simp add: exI[where x="{}"])
next
  case (Vars_scene_space x)
  show ?case
    apply (rule exI[where x="{x}"])
    by (simp add: Vars_scene_space fold_scene_singleton)
next
  case (union_scene_space x y)
  then obtain xs ys where xsys: "xs \<subseteq> Vars \<and> \<Squnion>\<^sub>S xs = x"
                                "ys \<subseteq> Vars \<and> \<Squnion>\<^sub>S ys = y"
    by blast+    
  show ?case
    by (rule exI[where x="xs \<union> ys"])
       (metis Un_subset_iff compat_family.S_idem compat_family.intro compat_family_subset fold_scene_union infinite_super local.finite_Vars local.idem_scene_Vars pairwise_compat_Vars_subset scene_space_compats xsys(1) xsys(2))
qed

lemma fold_Vars_in_scene_space:
  assumes "A \<subseteq> Vars"
  shows "\<Squnion>\<^sub>S A \<in> scene_space"
proof -
  have f: "finite A"
    using assms finite_subset local.finite_Vars by blast
  from f assms show ?thesis
  proof induct
    case empty
    then show ?case
      by auto
  next
    case (insert x F)
    then show ?case 
      apply (subst fold_scene_insert)
      apply (auto)
      using compat_family.intro compat_family_subset local.finite_Vars local.idem_scene_Vars scene_space_compats apply blast
      apply (simp add: Vars_compat_scene_space scene_space.Vars_scene_space subset_iff)
      done
  qed
qed

lemma scene_space_as_image_power:
  "scene_space = \<Squnion>\<^sub>S ` Pow Vars"
proof (rule Set.set_eqI, rule iffI)
  fix a
  assume "a \<in> scene_space"
  then obtain xs where xs: "xs \<subseteq> Vars" "\<Squnion>\<^sub>S xs = a"
    using scene_space_vars_decomp by blast
  thus "a \<in> \<Squnion>\<^sub>S ` Pow Vars"
    by blast
next
  fix a
  assume "a \<in> \<Squnion>\<^sub>S ` Pow Vars"
  thus "a \<in> scene_space"
    using fold_Vars_in_scene_space by blast 
qed

lemma finite_scene_space: "finite scene_space"
proof -
  have "scene_space = \<Squnion>\<^sub>S ` Pow Vars"
    using scene_space_as_image_power by blast
  also have "finite ..."
    using local.finite_Vars by blast
  finally show ?thesis .
qed 

lemma compat_scene_space: "compat_family scene_space"
proof
  show "pairwise (##\<^sub>S) scene_space"
    using pairwise_def scene_space_compat by blast
  show "finite scene_space"
    by (simp add: finite_scene_space)
  show "\<And>s. s \<in> scene_space \<Longrightarrow> idem_scene s"
    by (simp add: idem_scene_space)
qed

lemma scene_space_fold: "xs \<subseteq> scene_space \<Longrightarrow> \<Squnion>\<^sub>S xs \<in> scene_space"
proof -
  assume *: "xs \<subseteq> scene_space"
  then have "finite xs"
    using finite_scene_space rev_finite_subset by blast
  from this * show ?thesis
proof (induct xs)
  case empty
  then show ?case by fastforce
next
  case (insert x F)
  have "x \<squnion>\<^sub>S fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S F \<in> scene_space"
    using insert.hyps(3) insert.prems by blast
  then show ?case
    apply (subst compat_family.fold_insert[where S="scene_space"])
       apply (rule compat_scene_space)
    using insert.prems by auto
qed
qed

lemma top_scene_eq: "\<top>\<^sub>S = \<Squnion>\<^sub>S Vars"
  using local.span_Vars scene_span_def by force

lemma top_scene_space: "\<top>\<^sub>S \<in> scene_space"
proof -
  have "\<top>\<^sub>S = fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S  Vars"
    using span_Vars by (simp add: scene_span_def)
  also have "... \<in> scene_space"
    by (simp add: scene_space_fold)
  finally show ?thesis .
qed


(*
text \<open> Difficult proof, delaying \<close>
lemma basis_decomp_unique: "\<bottom>\<^sub>S \<notin> Vars \<Longrightarrow> xs \<subseteq> Vars \<and> \<Squnion>\<^sub>S xs = s \<Longrightarrow> ys \<subseteq> Vars \<and> \<Squnion>\<^sub>S ys = s \<Longrightarrow> xs = ys"
proof (rule ccontr)
  assume bot: "\<bottom>\<^sub>S \<notin> Vars" 
     and xs: "xs \<subseteq> Vars \<and> fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S xs = s"
     and ys: "ys \<subseteq> Vars \<and> fold (\<squnion>\<^sub>S) \<bottom>\<^sub>S ys = s"
    and neq: "xs \<noteq> ys"
  then show False
  proof (cases "s = \<bottom>\<^sub>S")
    case True
    then have "xs = {}"
      sorry
    moreover have "ys = {}"
      sorry
    ultimately show ?thesis
      using neq by simp
  next
    case False
    then show ?thesis sorry
  qed
qed

text \<open> Obtain the smallest set of basis scenes (omitting the bottom scene) for a given scene \<close>

definition basis_decomp :: "'a scene \<Rightarrow> 'a scene set" where
"basis_decomp s = (LEAST xs. xs \<subseteq> Vars \<and> \<Squnion>\<^sub>S xs = s)"

lemma basis_decomp_Un: "s \<in> scene_space \<Longrightarrow> \<Squnion>\<^sub>S (basis_decomp s) = s"
  unfolding basis_decomp_def using scene_space_vars_decomp oops

lemma basis_decomp_Vars: "s \<in> scene_space \<Longrightarrow> basis_decomp s \<subseteq> Vars"
  oops

lemma scene_space_algebra: "algebra Vars (basis_decomp ` scene_space)"
proof
  show "(set \<circ> basis_decomp) ` scene_space \<subseteq> Pow (Vars)"
    using basis_decomp_Vars by auto
  show "{} \<in> (set \<circ> basis_decomp) ` scene_space"
  proof
    show "{} = (set \<circ> basis_decomp) \<bottom>\<^sub>S"
      unfolding basis_decomp_def
      apply auto
      sorry
    show "\<bottom>\<^sub>S \<in> scene_space"
      by blast
  qed
  oops

lemma scene_space_vars_decomp_iff: "a \<in> scene_space \<longleftrightarrow> (\<exists>xs. set xs \<subseteq> Vars \<and> a = foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S)"
  apply (auto simp add: scene_space_vars_decomp scene_space.Vars_scene_space scene_space_foldr)
  apply (simp add: scene_space.Vars_scene_space scene_space_foldr subset_eq)
  using scene_space_vars_decomp apply auto[1]
  by (meson dual_order.trans scene_space_foldr set_Vars_scene_space)
*)

lemma "fold (\<squnion>\<^sub>S) b ((\<lambda>x. x ;\<^sub>S a) ` Vars) = \<lbrakk>a\<rbrakk>\<^sub>\<sim> \<squnion>\<^sub>S b"
  oops

lemma Vars_indep_foldr:
  assumes "x \<in> Vars" "xs \<subseteq> Vars"
  shows "x \<bowtie>\<^sub>S \<Squnion>\<^sub>S (xs - {x})"
proof (rule fold_scene_indep)
  show "pairwise (##\<^sub>S) (set (removeAll x xs))"
    by (simp, metis Diff_subset assms(2) pairwise_mono scene_space_compats)
  from assms show "\<forall>b\<in>set (removeAll x xs). x \<bowtie>\<^sub>S b"
    by (simp)
       (metis DiffE insertI1 local.indep_Vars pairwiseD scene_indeps_def subset_iff)
qed

lemma Vars_indeps_foldr:
  assumes "set xs \<subseteq> Vars"
  shows "foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S \<bowtie>\<^sub>S foldr (\<squnion>\<^sub>S) (filter (\<lambda>x. x \<notin> set xs) Vars) \<bottom>\<^sub>S"
  apply (rule foldr_scene_indep)
   apply (meson filter_is_subset pairwise_subset scene_space_compats)
  apply (simp)
  apply auto
  apply (rule scene_indep_sym)
  apply (metis (no_types, lifting) assms foldr_scene_indep local.indep_Vars pairwiseD pairwise_mono scene_indeps_def scene_space_compats subset_iff)
  done
  
lemma uminus_var_other_vars:
  assumes "x \<in> Vars"
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
  assumes "set xs \<subseteq> Vars"
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
  assumes "set xs \<subseteq> Vars"
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
  assumes "set xs \<subseteq> Vars" "a \<in> set xs"
  shows "foldr (\<squnion>\<^sub>S) xs \<bottom>\<^sub>S = foldr (\<squnion>\<^sub>S) (a # removeAll a xs) \<bottom>\<^sub>S"
  by (metis assms(1) assms(2) foldr_scene_union_eq_sets insert_Diff list.simps(15) pairwise_subset scene_space_compats set_removeAll)

lemma scene_union_foldr_Cons_removeAll':
  assumes "set xs \<subseteq> Vars" "a \<in> Vars"
  shows "foldr (\<squnion>\<^sub>S) (a # xs) \<bottom>\<^sub>S = foldr (\<squnion>\<^sub>S) (a # removeAll a xs) \<bottom>\<^sub>S"
  by (simp add: assms(1) scene_union_foldr_remove_element)

lemma scene_in_foldr: "\<lbrakk> a \<in> set xs; set xs \<subseteq> Vars \<rbrakk> \<Longrightarrow> a \<subseteq>\<^sub>S \<Squnion>\<^sub>S xs"
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
  assumes "set xs \<subseteq> set ys" "set ys \<subseteq> Vars"
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
  assumes "set xs \<subseteq> Vars" "set ys \<subseteq> Vars"
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

lemma scene_compl_subset_iff:
  assumes "a \<in> scene_space" "b \<in> scene_space"
  shows "- a \<subseteq>\<^sub>S -b \<longleftrightarrow> b \<subseteq>\<^sub>S a"
  by (metis scene_indep_sym scene_le_iff_indep_inv uminus_scene_twice)

lemma inter_scene_space_foldrs:
  assumes "set xs \<subseteq> Vars" "set ys \<subseteq> Vars"
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
    have "\<And>x. x \<in> Vars \<Longrightarrow> ((x \<in> Vars \<longrightarrow> x \<in> set xs) \<and> (x \<in> Vars \<longrightarrow> x \<in> set ys)) = (x \<in> set xs \<and> x \<in> set ys)"
      by auto
    thus ?thesis
      by (simp cong: arg_cong[where f="\<Squnion>\<^sub>S"] filter_cong add: assms)
  qed
  finally show ?thesis .
qed

lemma scene_inter_distrib_lemma:
  assumes "set xs \<subseteq> Vars" "set ys \<subseteq> Vars" "set zs \<subseteq> Vars"
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

lemma foldr_scene_union_remdups: "set xs \<subseteq> Vars \<Longrightarrow> \<Squnion>\<^sub>S (remdups xs) = \<Squnion>\<^sub>S xs"
  by (auto intro: foldr_scene_union_eq_sets simp add: pairwise_compat_Vars_subset)


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
  "\<lbrakk> x \<in> Vars; a \<in> scene_space; b \<in> scene_space; x \<le> a \<squnion>\<^sub>S b \<rbrakk> \<Longrightarrow> (x \<le> a \<or> x \<le> b)"
  by (auto simp add: scene_space_vars_decomp_iff)
     (metis Vars_indep_foldr bot_idem_scene idem_scene_space removeAll_id scene_bot_least scene_indep_pres_compat scene_le_iff_indep_inv scene_space.union_scene_space scene_space_foldr scene_space_in_foldr scene_union_compl set_Vars_scene_space subscene_trans subset_trans uminus_scene_twice uminus_top_scene)

lemma var_le_union_iff:
  "\<lbrakk> x \<in> Vars; a \<in> scene_space; b \<in> scene_space \<rbrakk> \<Longrightarrow> x \<le> a \<squnion>\<^sub>S b \<longleftrightarrow> (x \<le> a \<or> x \<le> b)"
  apply (rule iffI, simp add: var_le_union_choice)
  apply (auto)
  apply (meson idem_scene_space scene_space_ub subscene_trans)
  apply (metis idem_scene_space scene_space_ub scene_union_commute subscene_trans)
  done

text \<open> @{term Vars} may contain the empty scene, as we want to allow vacuous lenses in alphabets \<close>

lemma le_vars_then_equal: "\<lbrakk> x \<in> Vars; y \<in> Vars; x \<le> y; x \<noteq> \<bottom>\<^sub>S \<rbrakk> \<Longrightarrow> x = y"
  by (metis bot_idem_scene foldr_scene_removeAll local.idem_scene_Vars local.indep_Vars local.span_Vars pairwiseD scene_bot_least scene_indep_pres_compat scene_indeps_def scene_le_iff_indep_inv scene_space_compats scene_span_def scene_union_annhil subscene_antisym uminus_scene_twice uminus_top_scene uminus_var_other_vars)

end

lemma foldr_scene_union_eq_scene_space: 
  "\<lbrakk> set xs \<subseteq> scene_space; set xs = set ys \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>S xs = \<Squnion>\<^sub>S ys"
  by (metis foldr_scene_union_eq_sets pairwise_def pairwise_subset scene_space_compat)

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
  by (intro_classes, simp_all add: scene_indeps_def scene_span_def)

end

find_theorems vwb_lens fst\<^sub>L

find_theorems "(\<Squnion>\<^sub>S)" "(@)"

instantiation prod :: (scene_space, scene_space) scene_space
begin

definition Vars_prod :: "('a \<times> 'b) scene list" where "Vars_prod = map_lcomp Vars fst\<^sub>L @ map_lcomp Vars snd\<^sub>L"

instance proof
  have pw: "pairwise (\<bowtie>\<^sub>S) (set (map_lcomp Vars fst\<^sub>L @ map_lcomp Vars snd\<^sub>L))"
    by (auto simp add: pairwise_def Vars_ext_lens_indep scene_comp_pres_indep scene_indep_sym)
  show "\<And>x:: ('a \<times> 'b) scene. x \<in> Vars \<Longrightarrow> idem_scene x"
    by (auto simp add: Vars_prod_def)
  from pw show "scene_indeps (set (Vars :: ('a \<times> 'b) scene list))"
    by (simp add: Vars_prod_def scene_indeps_def)
  show "scene_span (Vars :: ('a \<times> 'b) scene list)"
    by (simp only: scene_span_def Vars_prod_def foldr_scene_append pw pairwise_indep_then_compat map_lcomp_Vars_is_lens fst_vwb_lens snd_vwb_lens)
       (metis fst_vwb_lens lens_plus_scene lens_scene_top_iff_bij_lens plus_mwb_lens scene_union_commute snd_fst_lens_indep snd_vwb_lens swap_bij_lens vwb_lens_mwb)
qed  

end

subsection \<open> Scene space and basis lenses \<close>

locale var_lens = vwb_lens +
  assumes lens_in_scene_space: "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> scene_space"

declare var_lens.lens_in_scene_space [simp]
declare var_lens.axioms(1) [simp]

locale basis_lens = vwb_lens +
  assumes lens_in_basis: "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> Vars"

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

lemma basis_lens_intro: "\<lbrakk> vwb_lens x; \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> Vars \<rbrakk> \<Longrightarrow> basis_lens x"
  using basis_lens.intro basis_lens_axioms.intro by blast

subsection \<open> Composite lenses \<close>

locale composite_lens = vwb_lens +
  assumes comp_in_Vars: "(\<lambda> a. a ;\<^sub>S x) ` Vars \<subseteq> Vars"
begin

lemma Vars_closed_comp: "a \<in> Vars \<Longrightarrow> a ;\<^sub>S x \<in> Vars"
  using comp_in_Vars by blast

lemma scene_space_closed_comp:
  assumes "a \<in> scene_space"
  shows "a ;\<^sub>S x \<in> scene_space"
proof -
  obtain xs where xs: "a = \<Squnion>\<^sub>S xs" "set xs \<subseteq> Vars"
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
