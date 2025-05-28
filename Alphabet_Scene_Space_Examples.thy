section \<open> Example Alphabet Scene Spaces \<close>

theory Alphabet_Scene_Space_Examples
imports Alphabet_Scene_Spaces
begin

alphabet test = 
  x :: bool
  y :: nat 
  z :: "int list"

alphabet_scene_space test

lemma "UNIV\<^sub>F(test) = \<lbrace>x, y, z\<rbrace>\<^sub>F"
  by (simp add: frame)

term "\<lbrace>x, y, z\<rbrace>\<^sub>F"

lemma "z \<in>\<^sub>F \<lbrace>x, y, z\<rbrace>\<^sub>F"
  by simp

lemma "\<lbrace>x\<rbrace>\<^sub>F \<union>\<^sub>F \<lbrace>y, z\<rbrace>\<^sub>F = \<lbrace>x, y, z\<rbrace>\<^sub>F"
  by simp

lemma "\<lbrace>x\<rbrace>\<^sub>F \<union>\<^sub>F \<lbrace>x, y, z\<rbrace>\<^sub>F = \<lbrace>x, y, z\<rbrace>\<^sub>F"
  by simp

alphabet test2 = test +
  u :: string
  v :: int

alphabet_scene_space test2

lemma "UNIV\<^sub>F(test2) = \<lbrace>x, y, z, u, v\<rbrace>\<^sub>F"
  by (simp add: frame)

alphabet test3 = test2 +
  w :: string

alphabet_scene_space test3

lemma "UNIV\<^sub>F(test3) = \<lbrace>x, y, z, u, v, w\<rbrace>\<^sub>F"
  by (simp add: frame)

alphabet test4 = test3 +
  j :: string

alphabet_scene_space test4

lemma "UNIV\<^sub>F(test4) = \<lbrace>x, y, z, u, v, w, j\<rbrace>\<^sub>F"
  by (simp add: frame)

find_theorems concat set

alphabet person = 
  name :: string
  age  :: nat

alphabet_scene_space person

alphabet company =
  boss :: person
  worker :: person

instantiation company_ext :: (scene_space) scene_space
begin

definition Vars_company_ext :: "'a company_scheme scene list" where
[scene_space_defs]: "Vars_company_ext = alpha_scene_space' (concat [map_lcomp Vars boss, map_lcomp Vars worker]) more\<^sub>L 1\<^sub>L"

instance 
  apply (rule scene_space_class.intro
  ,(intro_classes)[1])
  apply (unfold Vars_company_ext_def)
  apply (rule alpha_scene_space_class_intro'')
  apply (simp_all add: ball_Un Vars_ext_lens_indep scene_space_lemmas scene_comp_pres_indep scene_indep_sym one_lens_scene scene_top_greatest scene_indeps_def pairwise_def)
  done

end

lemma "composite_lens boss"
  by composite_lens

lemma "composite_lens worker"
  by composite_lens

end