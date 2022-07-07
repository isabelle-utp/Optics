section \<open> Example Alphabet Scene Spaces \<close>

theory Alphabet_Scene_Space_Examples
imports Alphabet_Scene_Spaces
begin

alphabet test = 
  x :: bool
  y :: nat 
  z :: "int list"

alphabet_scene_space test

lemma "UNIV\<^sub>F(test) = \<lbrace>x, y, z\<rbrace>"
  by (simp add: frame)

term "\<lbrace>x, y, z\<rbrace>"

lemma "z \<in>\<^sub>F \<lbrace>x, y, z\<rbrace>"
  by simp

lemma "\<lbrace>x\<rbrace> \<union>\<^sub>F \<lbrace>y, z\<rbrace> = \<lbrace>x, y, z\<rbrace>"
  by simp

lemma "\<lbrace>x\<rbrace> \<union>\<^sub>F \<lbrace>x, y, z\<rbrace> = \<lbrace>x, y, z\<rbrace>"
  by simp

alphabet test2 = test +
  u :: string
  v :: int

alphabet_scene_space test2

lemma "UNIV\<^sub>F(test2) = \<lbrace>x, y, z, u, v\<rbrace>"
  by (simp add: frame)

alphabet test3 = test2 +
  w :: string

alphabet_scene_space test3

lemma "UNIV\<^sub>F(test3) = \<lbrace>x, y, z, u, v, w\<rbrace>"
  by (simp add: frame)

alphabet test4 = test3 +
  j :: string

alphabet_scene_space test4

lemma "UNIV\<^sub>F(test4) = \<lbrace>x, y, z, u, v, w, j\<rbrace>"
  by (simp add: frame)

find_theorems concat set

alphabet person = 
  name :: string
  age  :: nat

alphabet_scene_space person

alphabet company =
  boss :: person
  worker :: person

definition "map_lcomp ss a = map (\<lambda> x. x ;\<^sub>S a) ss"

lemma map_lcomp_dist: 
  "\<lbrakk> pairwise (##\<^sub>S) (set xs); vwb_lens a \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>S (map_lcomp xs a) = \<Squnion>\<^sub>S xs ;\<^sub>S a"
  by (simp add: foldr_compat_dist map_lcomp_def)

lemma map_lcomp_Vars_is_lens [simp]: "vwb_lens a \<Longrightarrow> \<Squnion>\<^sub>S (map_lcomp Vars a) = \<lbrakk>a\<rbrakk>\<^sub>\<sim>"
  by (metis map_lcomp_dist scene_comp_top_scene scene_space_compats top_scene_eq)

instantiation company_ext :: (scene_space) scene_space
begin

definition Vars_company_ext :: "'a company_scheme scene list" where
[scene_space_defs]: "Vars_company_ext = alpha_scene_space' (concat [map_lcomp Vars boss, map_lcomp Vars worker]) more\<^sub>L 1\<^sub>L"

instance 
  apply (rule scene_space_class.intro)
   apply (intro_classes)[1]
  apply (unfold Vars_company_ext_def)
  apply (rule alpha_scene_space_class_intro'')
      apply (simp add: map_lcomp_def scene_space_lemmas scene_space_defs alpha_scene_space'_def alpha_scene_space_def)
     apply (simp add: map_lcomp_def scene_space_lemmas scene_space_defs alpha_scene_space'_def alpha_scene_space_def scene_indeps_def pairwise_def)
    apply (simp add: map_lcomp_def scene_space_lemmas scene_space_defs alpha_scene_space'_def alpha_scene_space_def)
      apply (simp add: map_lcomp_def scene_space_lemmas scene_space_defs alpha_scene_space'_def alpha_scene_space_def)
     apply (simp add: map_lcomp_def scene_space_lemmas scene_space_defs alpha_scene_space'_def alpha_scene_space_def)
    apply (simp add: map_lcomp_def scene_space_lemmas scene_space_defs alpha_scene_space'_def alpha_scene_space_def)
   apply (simp add: map_lcomp_def scene_space_lemmas scene_space_defs alpha_scene_space'_def alpha_scene_space_def)
  apply (simp add: scene_space_lemmas)
  done

end

end