section \<open> Example Alphabet Scene Spaces \<close>

theory Alphabet_Scene_Space_Examples
imports Alphabet_Scene_Spaces
begin

alphabet test = 
  x :: bool
  y :: nat 
  z :: "int list"

alphabet_scene_space test

term "\<lbrace>x, y, z\<rbrace>"

lemma "z \<in>\<^sub>F \<lbrace>x, y, z\<rbrace>"
  by simp

lemma "UNIV\<^sub>F(test) = \<lbrace>x, y, z\<rbrace>"
  by (simp add: frame)

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

end