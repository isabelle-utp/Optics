section \<open>Prisms\<close>

theory Prisms
  imports Lenses
begin

subsection \<open> Signature and Axioms \<close>

text \<open>Prisms are like lenses, but they act on sum types rather than product types~\cite{Gibbons17}.
  See \url{https://hackage.haskell.org/package/lens-4.15.2/docs/Control-Lens-Prism.html}
  for more information.\<close>

record ('v, 's) prism =
  prism_match :: "'s \<Rightarrow> 'v option" ("match\<index>")
  prism_build :: "'v \<Rightarrow> 's" ("build\<index>")

type_notation
  prism (infixr "\<Longrightarrow>\<^sub>\<triangle>" 0)

definition prism_matches :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'e \<Rightarrow> bool" ("matches\<index>") where
"prism_matches a e = (match\<^bsub>a\<^esub> e \<noteq> None)"

locale wb_prism =
  fixes x :: "'v \<Longrightarrow>\<^sub>\<triangle> 's" (structure)
  assumes match_build: "match (build v) = Some v"
  and build_match: "match s = Some v \<Longrightarrow> s = build v"
begin

  lemma build_match_iff: "match s = Some v \<longleftrightarrow> s = build v"
    using build_match match_build by blast

  lemma range_build: "range build = dom match"
    using build_match match_build by fastforce

  lemma inj_build: "inj build"
    by (metis injI match_build option.inject)

  lemma matches_build: "matches (build v)"
    by (simp add: prism_matches_def match_build)

end

declare wb_prism.match_build [simp]
declare wb_prism.build_match [simp]
declare wb_prism.matches_build [simp]

subsection \<open> Co-dependence \<close>

text \<open> The relation states that two prisms construct disjoint elements of the source. This
  can occur, for example, when the two prisms characterise different constructors of an
  algebraic datatype. \<close>

definition prism_diff :: "('a \<Longrightarrow>\<^sub>\<triangle> 's) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 's) \<Rightarrow> bool" (infix "\<nabla>" 50) where
[lens_defs]: "prism_diff X Y = (range build\<^bsub>X\<^esub> \<inter> range build\<^bsub>Y\<^esub> = {})"

lemma prism_diff_intro:
  "(\<And> s\<^sub>1 s\<^sub>2. build\<^bsub>X\<^esub> s\<^sub>1 = build\<^bsub>Y\<^esub> s\<^sub>2 \<Longrightarrow> False) \<Longrightarrow> X \<nabla> Y"
  by (auto simp add: prism_diff_def)

lemma prism_diff_irrefl: "\<not> X \<nabla> X"
  by (simp add: prism_diff_def)

lemma prism_diff_sym: "X \<nabla> Y \<Longrightarrow> Y \<nabla> X"
  by (auto simp add: prism_diff_def)

lemma prism_diff_build: "X \<nabla> Y \<Longrightarrow> build\<^bsub>X\<^esub> u \<noteq> build\<^bsub>Y\<^esub> v"
  by (simp add: disjoint_iff_not_equal prism_diff_def)

lemma prism_diff_build_match: "\<lbrakk> wb_prism X; X \<nabla> Y \<rbrakk> \<Longrightarrow> match\<^bsub>X\<^esub> (build\<^bsub>Y\<^esub> v) = None" 
  using UNIV_I wb_prism.range_build by (fastforce simp add: prism_diff_def)

subsection \<open> Canonical prisms \<close>

definition prism_id :: "('a \<Longrightarrow>\<^sub>\<triangle> 'a)" ("1\<^sub>\<triangle>") where
[lens_defs]: "prism_id = \<lparr> prism_match = Some, prism_build = id \<rparr>"

lemma wb_prism_id: "wb_prism 1\<^sub>\<triangle>"
  unfolding prism_id_def wb_prism_def by simp

lemma prism_id_never_diff: "\<not> 1\<^sub>\<triangle> \<nabla> X"
  by (simp add: prism_diff_def prism_id_def)

subsection \<open> Summation \<close>

definition prism_plus :: "('a \<Longrightarrow>\<^sub>\<triangle> 's) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 's) \<Rightarrow> 'a + 'b \<Longrightarrow>\<^sub>\<triangle> 's" (infixl "+\<^sub>\<triangle>" 85) 
  where
[lens_defs]: "X +\<^sub>\<triangle> Y = \<lparr> prism_match = (\<lambda> s. case (match\<^bsub>X\<^esub> s, match\<^bsub>Y\<^esub> s) of
                                 (Some u, _) \<Rightarrow> Some (Inl u) |
                                 (None, Some v) \<Rightarrow> Some (Inr v) |
                                 (None, None) \<Rightarrow> None),
           prism_build = (\<lambda> v. case v of Inl x \<Rightarrow> build\<^bsub>X\<^esub> x | Inr y \<Rightarrow> build\<^bsub>Y\<^esub> y) \<rparr>"

lemma prism_plus_wb [simp]: "\<lbrakk> wb_prism X; wb_prism Y; X \<nabla> Y \<rbrakk> \<Longrightarrow> wb_prism (X +\<^sub>\<triangle> Y)"
  apply (unfold_locales)
   apply (auto simp add: prism_plus_def sum.case_eq_if option.case_eq_if prism_diff_build_match)
  apply (metis map_option_case map_option_eq_Some option.exhaust option.sel sum.disc(2) sum.sel(1) wb_prism.build_match_iff)
  apply (metis (no_types, lifting) isl_def not_None_eq option.case_eq_if option.sel sum.sel(2) wb_prism.build_match)
  done

lemma build_plus_Inl [simp]: "build\<^bsub>c +\<^sub>\<triangle> d\<^esub> (Inl x) = build\<^bsub>c\<^esub> x"
  by (simp add: prism_plus_def)

lemma build_plus_Inr [simp]: "build\<^bsub>c +\<^sub>\<triangle> d\<^esub> (Inr y) = build\<^bsub>d\<^esub> y"
  by (simp add: prism_plus_def)

lemma prism_diff_preserved_1 [simp]: "\<lbrakk> X \<nabla> Y; X \<nabla> Z \<rbrakk> \<Longrightarrow> X \<nabla> Y +\<^sub>\<triangle> Z"
  by (auto simp add: lens_defs sum.case_eq_if)

lemma prism_diff_preserved_2 [simp]: "\<lbrakk> X \<nabla> Z; Y \<nabla> Z \<rbrakk> \<Longrightarrow> X +\<^sub>\<triangle> Y \<nabla> Z"
  by (meson prism_diff_preserved_1 prism_diff_sym)

text \<open> The following two lemmas are useful for reasoning about prism sums \<close>

lemma Bex_Sum_iff: "(\<exists>x\<in>A<+>B. P x) \<longleftrightarrow> (\<exists> x\<in>A. P (Inl x)) \<or> (\<exists> y\<in>B. P (Inr y))"
  by (auto)

lemma Ball_Sum_iff: "(\<forall>x\<in>A<+>B. P x) \<longleftrightarrow> (\<forall> x\<in>A. P (Inl x)) \<and> (\<forall> y\<in>B. P (Inr y))"
  by (auto)

subsection \<open> Instances \<close>

definition prism_suml :: "('a, 'a + 'b) prism" ("Inl\<^sub>\<triangle>") where
[lens_defs]: "prism_suml = \<lparr> prism_match = (\<lambda> v. case v of Inl x \<Rightarrow> Some x | _ \<Rightarrow> None), prism_build = Inl \<rparr>"

definition prism_sumr :: "('b, 'a + 'b) prism" ("Inr\<^sub>\<triangle>") where
[lens_defs]: "prism_sumr = \<lparr> prism_match = (\<lambda> v. case v of Inr x \<Rightarrow> Some x | _ \<Rightarrow> None), prism_build = Inr \<rparr>"

lemma wb_prim_suml [simp]: "wb_prism Inl\<^sub>\<triangle>"
  apply (unfold_locales)
   apply (simp_all add: prism_suml_def sum.case_eq_if)
  apply (metis option.inject option.simps(3) sum.collapse(1))
  done

lemma wb_prim_sumr [simp]: "wb_prism Inr\<^sub>\<triangle>"
  apply (unfold_locales)
   apply (simp_all add: prism_sumr_def sum.case_eq_if)
  apply (metis option.distinct(1) option.inject sum.collapse(2))
  done

lemma prism_suml_indep_sumr [simp]: "Inl\<^sub>\<triangle> \<nabla> Inr\<^sub>\<triangle>"
  by (auto simp add: lens_defs)

lemma prism_sum_plus: "Inl\<^sub>\<triangle> +\<^sub>\<triangle> Inr\<^sub>\<triangle> = 1\<^sub>\<triangle>"
  unfolding lens_defs prism_plus_def by (auto simp add: Inr_Inl_False sum.case_eq_if)

subsection \<open> Lens correspondence \<close>

text \<open> Every well-behaved prism can be represented by a partial bijective lens. We prove 
  this by exhibiting conversion functions and showing they are (almost) inverses. \<close>

definition prism_lens :: "('a, 's) prism \<Rightarrow> ('a \<Longrightarrow> 's)" where
"prism_lens X = \<lparr> lens_get = (\<lambda> s. the (match\<^bsub>X\<^esub> s)), lens_put = (\<lambda> s v. build\<^bsub>X\<^esub> v) \<rparr>"

definition lens_prism :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) prism" where
"lens_prism X = \<lparr> prism_match = (\<lambda> s. if (s \<in> \<S>\<^bsub>X\<^esub>) then Some (get\<^bsub>X\<^esub> s) else None)
                , prism_build = create\<^bsub>X\<^esub> \<rparr>"

lemma mwb_prism_lens: "wb_prism a \<Longrightarrow> mwb_lens (prism_lens a)"
  by (simp add: mwb_lens_axioms_def mwb_lens_def weak_lens_def prism_lens_def)

lemma get_prism_lens: "get\<^bsub>prism_lens X\<^esub> = the \<circ> match\<^bsub>X\<^esub>"
  by (simp add: prism_lens_def fun_eq_iff)

lemma src_prism_lens: "\<S>\<^bsub>prism_lens X\<^esub> = range (build\<^bsub>X\<^esub>)"
  by (auto simp add: prism_lens_def lens_source_def)

lemma create_prism_lens: "create\<^bsub>prism_lens X\<^esub> = build\<^bsub>X\<^esub>"
  by (simp add: prism_lens_def lens_create_def fun_eq_iff)

lemma prism_lens_inverse:
  "wb_prism X \<Longrightarrow> lens_prism (prism_lens X) = X"
  unfolding lens_prism_def src_prism_lens create_prism_lens get_prism_lens
  by (auto intro: prism.equality simp add: fun_eq_iff domIff wb_prism.range_build)

text \<open> Function @{const lens_prism} is almost inverted by @{const prism_lens}. The $put$
  functions are identical, but the $get$ functions differ when applied to a source where
  the prism @{term X} is undefined. \<close>

lemma lens_prism_put_inverse:
  "pbij_lens X \<Longrightarrow> put\<^bsub>prism_lens (lens_prism X)\<^esub> = put\<^bsub>X\<^esub>"
  unfolding prism_lens_def lens_prism_def
  by (auto simp add: fun_eq_iff pbij_lens.put_is_create)

lemma wb_prism_implies_pbij_lens:
  "wb_prism X \<Longrightarrow> pbij_lens (prism_lens X)"
  by (unfold_locales, simp_all add: prism_lens_def)

lemma pbij_lens_implies_wb_prism:
  assumes "pbij_lens X" 
  shows "wb_prism (lens_prism X)"
proof (unfold_locales)
  fix s v
  show "match\<^bsub>lens_prism X\<^esub> (build\<^bsub>lens_prism X\<^esub> v) = Some v"
    by (simp add: lens_prism_def weak_lens.create_closure assms)
  assume a: "match\<^bsub>lens_prism X\<^esub> s = Some v"
  show "s = build\<^bsub>lens_prism X\<^esub> v"
  proof (cases "s \<in> \<S>\<^bsub>X\<^esub>")
    case True
    with a assms show ?thesis 
      by (simp add: lens_prism_def lens_create_def, 
          metis mwb_lens.weak_get_put pbij_lens.put_det pbij_lens_mwb)
  next
    case False
    with a assms show ?thesis by (simp add: lens_prism_def)
  qed
qed

ML_file \<open>Prism_Lib.ML\<close>

end
