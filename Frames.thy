theory Frames
  imports Scene_Spaces
begin

definition nmods :: "'s::scene_space rel \<Rightarrow> 's frame \<Rightarrow> bool" where
"nmods R a = (\<forall> (s, s') \<in> R. s \<approx>\<^sub>F s' on a)"

abbreviation "mods R a \<equiv> nmods R (- a)"

lemma nmods_Id: "nmods Id a"
  by (auto simp add: nmods_def)

lemma nmods_seq: "\<lbrakk> nmods P a; nmods Q b \<rbrakk> \<Longrightarrow> nmods (P O Q) (a \<inter>\<^sub>F b)"
  apply (simp only: nmods_def relcomp_unfold)
  apply safe
  apply (metis case_prodD frame_equiv_trans_gen)
  done

lemma mods_seq: "\<lbrakk> mods P a; mods Q b \<rbrakk> \<Longrightarrow> mods (P O Q) (a \<union>\<^sub>F b)"
  by (simp add: nmods_seq)

definition antiframe_of :: "'s::scene_space rel \<Rightarrow> 's frame" where
"antiframe_of R = Least (nmods R)"

definition frame_of :: "'s::scene_space rel \<Rightarrow> 's frame" where
"frame_of R = Greatest (mods R)"

lemma nmods_antiframe: "nmods P (antiframe_of P)"
  by (simp add: antiframe_of_def)
     (metis Least_equality bot.extremum case_prodI2 frame_equiv_empty nmods_def)

lemma mods_frame: "mods P (frame_of P)"
  by (simp add: frame_of_def)
     (metis (mono_tags, lifting) GreatestI2_order boolean_algebra_class.boolean_algebra.double_compl bot.extremum compl_le_compl_iff frame_equiv_empty nmods_def prod.case_eq_if)

lemma antiframe_frame: "antiframe_of P = - (frame_of P)"
  apply (auto simp add: frame_of_def antiframe_of_def)
  apply (rule Least_equality)
   apply (metis frame_of_def mods_frame)
  apply (metis (no_types, lifting) Greatest_equality boolean_algebra_class.boolean_algebra.double_compl bot.extremum compl_le_swap1 frame_equiv_empty nmods_def prod.case_eq_if)
  done

lemma antiframe_of_Id: "antiframe_of Id = \<lbrace>\<rbrace>"
  apply (simp add: antiframe_of_def nmods_def)
  apply (rule Least_equality)
  apply (auto simp add: nmods_Id)
  done

lemma antiframe_of_seq: "antiframe_of (P O Q) = antiframe_of P \<inter>\<^sub>F antiframe_of Q"
  apply (simp add: antiframe_of_def)
  apply (metis (no_types, lifting) Least_equality bot.extremum frame_equiv_empty inf_bot_right nmods_def prod.case_eq_if)
  done

lemma frame_of_seq: "frame_of (P O Q) = frame_of P \<union>\<^sub>F frame_of Q"
  by (metis antiframe_frame antiframe_of_seq boolean_algebra.de_Morgan_disj boolean_algebra_class.boolean_algebra.compl_eq_compl_iff)

end