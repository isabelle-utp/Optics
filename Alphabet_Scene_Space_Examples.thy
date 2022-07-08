section \<open> Example Alphabet Scene Spaces \<close>

theory Alphabet_Scene_Space_Examples
imports Alphabet_Scene_Spaces
begin

lemma frame_Union_image: "set xs \<subseteq> scene_space \<Longrightarrow> \<Union>\<^sub>F (frame_scene `  set xs) = frame_scene (\<Squnion>\<^sub>S xs)"
  by (simp add: frame_scene_foldr)

term map_lcomp

lemma composite_lens_frame_lens: "composite_lens y \<Longrightarrow> \<Union>\<^sub>F (frame_scene ` set (map_lcomp Vars y)) = lens_frame y"
  apply (subst frame_Union_image)
  using composite_lens.comp_in_Vars apply auto[1]
  apply (metis composite_implies_var_lens composite_lens.axioms(1) frame_scene_basis_lens map_lcomp_Vars_is_lens)
  done

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
  income :: nat
  boss :: person
  worker :: person  

alphabet_scene_space company

lemma "composite_lens more\<^sub>L"
  by composite_lens

lemma "\<top>\<^sub>F = \<lbrace>income, boss, worker\<rbrace> \<union>\<^sub>F more_frame more\<^sub>L"
  apply (simp add: frame_scene_top frame_scene_foldr)?
  apply (simp add: Vars_company_ext_def frame_scene_top frame_scene_foldr alpha_scene_space'_def alpha_scene_space_def scene_space_lemmas more_frame_def  image_Un Sup_union_distrib)
  apply more_frame
  oops

(*
instantiation company_ext :: (scene_space) scene_space
begin

definition Vars_company_ext :: "'a company_scheme scene list" where
[scene_space_defs]: "Vars_company_ext = alpha_scene_space' (concat [[\<lbrakk>income\<rbrakk>\<^sub>\<sim>], map_lcomp Vars boss, map_lcomp Vars worker]) more\<^sub>L 1\<^sub>L"

instance by (alpha_scene_space' defs: Vars_company_ext_def)

end
*)
lemma "basis_lens income"
  by basis_lens

lemma "composite_lens boss"
  by composite_lens

lemma "composite_lens worker"
  by composite_lens


end