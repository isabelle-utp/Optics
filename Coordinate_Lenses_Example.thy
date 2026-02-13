section \<open> Example: Lenses as Coordinate Systems \<close>

theory Coordinate_Lenses_Example
  imports "HOL.Transcendental" Optics
begin

text \<open> We describe a lens for converting between polar and Cartesian coordinates. For simplicity,
  we only consider coordinates in the first quadrant with both components strictly greater than 0. 
  This means we only need angles in (0..\pi/2). \<close>

subsection \<open> Types for Angles and Strictly Positive Reals \<close>

typedef angle = "{0<..<pi/2}" apply (rule_tac x="0.9" in exI, auto)
  using pi_ge_two by force

setup_lifting type_definition_angle

typedef preal = "{0::real<..}" using pi_gt_zero by blast

type_synonym pcoord = "preal \<times> preal"

setup_lifting type_definition_preal

subsection \<open> Relating Cartesian and Polar Coordinates \<close>

lift_definition angle_of :: "pcoord \<Rightarrow> angle" is "\<lambda> (x, y). arctan (y / x)"
  using arctan_bounded order_less_imp_le by auto

lift_definition radius_of :: "pcoord \<Rightarrow> preal" is "\<lambda> (x, y). sqrt (x\<^sup>2 + y\<^sup>2)"
  by (auto simp add: pos_add_strict)

lift_definition xc_of :: "preal \<times> angle \<Rightarrow> preal" is "\<lambda> (r, \<theta>). r * cos \<theta>"
  by (auto simp add: cos_gt_zero_pi pi_def)

lift_definition yc_of :: "preal \<times> angle \<Rightarrow> preal" is "\<lambda> (r, \<theta>). r * sin \<theta>"
  by (auto simp add: sin_gt_zero2)

lemma cartesian_recovery_x:
  fixes x y :: real
  assumes "0 < x" "0 < y"
  shows "sqrt (x^2 + y^2) * cos (arctan (y / x)) = x"
proof -
  have cos_arctan: "cos (arctan (y/x)) = 1 / sqrt (1 + (y/x)^2)"
    by (rule cos_arctan) (* This is a standard library lemma *)

  have "sqrt (x^2 + y^2) * cos (arctan (y / x)) = 
        sqrt (x^2 + y^2) * (1 / sqrt (1 + (y/x)^2))"
    using cos_arctan by simp

  also have "... = sqrt (x^2 + y^2) * (1 / sqrt ((x^2 + y^2) / x^2))"
    using `0 < x` by (simp add: field_simps)

  also have "... = sqrt (x^2 + y^2) * (1 / (sqrt (x^2 + y^2) / x))"
    using `0 < x` by (simp add: real_sqrt_divide)
    
  also have "... = x"
    using `0 < x` `0 < y` by (simp add: field_simps)
    
  finally show ?thesis .
qed

lemma xc_of [simp]: "xc_of (radius_of (x, y), angle_of (x, y)) = x"
  by (transfer, simp add: cartesian_recovery_x)

lemma cartesian_recovery_y:
  fixes x y :: real
  assumes "0 < x" "0 < y"
  shows "sqrt (x^2 + y^2) * sin (arctan (y / x)) = y"
proof -
  have sin_arctan: "sin (arctan (y/x)) = (y/x) / sqrt (1 + (y/x)^2)"
    by (rule sin_arctan) 

  have "sqrt (x^2 + y^2) * sin (arctan (y / x)) = 
        sqrt (x^2 + y^2) * ((y/x) / sqrt (1 + (y/x)^2))"
    using sin_arctan by simp

  also have "... = sqrt (x^2 + y^2) * ((y/x) / (sqrt (x^2 + y^2) / x))"
    using `0 < x` by (simp add: real_sqrt_divide field_simps)
    
  also have "... = y"
    using `0 < x` `0 < y` by (simp add: field_simps)
    
  finally show ?thesis .
qed

lemma yc_of [simp]: "yc_of (radius_of (x, y), angle_of (x, y)) = y"
  by (transfer, simp add: cartesian_recovery_y)

lemma angle_of [simp]: "angle_of (xc_of (r, \<theta>), yc_of (r, \<theta>)) = \<theta>"
  by (transfer, auto simp add: arctan_unique pi_def pi_half tan_def)

lemma polar_radius_identity:
  assumes "0 < r" 
  shows "sqrt ((r * cos \<theta>)^2 + (r * sin \<theta>)^2) = r"
proof -
  have "sqrt ((r * cos \<theta>)^2 + (r * sin \<theta>)^2) = sqrt (r^2 * (cos \<theta>)^2 + r^2 * (sin \<theta>)^2)"
    by (simp add: power_mult_distrib)
  also have "... = sqrt (r^2 * ((cos \<theta>)^2 + (sin \<theta>)^2))"
    by argo
  also have "... = sqrt (r^2 * 1)"
    by simp
  also have "... = abs r"
    by simp
  also have "... = r"
    using assms(1) by simp
  finally show ?thesis .
qed

lemma radius_of [simp]: "radius_of (xc_of (r, \<theta>), yc_of (r, \<theta>)) = r"
  using polar_radius_identity by (transfer, auto)

subsection \<open> Polar Coordinate Lenses \<close>

definition radius :: "preal \<Longrightarrow> pcoord" where
[lens_defs]:
"radius = \<lparr> lens_get = radius_of
          , lens_put = (\<lambda> (x, y) r. (xc_of (r, angle_of (x, y)), yc_of (r, angle_of (x, y)))) \<rparr>"

definition angle :: "angle \<Longrightarrow> pcoord" where
[lens_defs]:
"angle = \<lparr> lens_get = angle_of
          , lens_put = (\<lambda> (x, y) \<theta>. (xc_of (radius_of (x, y), \<theta>), yc_of (radius_of (x, y), \<theta>))) \<rparr>"

lemma radius_vwb [simp]: "vwb_lens radius"
  unfolding radius_def
  by (unfold_locales, auto simp add: prod.case_eq_if)

lemma angle_vwb [simp]: "vwb_lens angle"
  unfolding angle_def
  by (unfold_locales, auto simp add: prod.case_eq_if)

lemma radius_angle_indep: "radius \<bowtie> angle"
  by (simp add: lens_indep_vwb_iff, simp add: angle_def radius_def)

lemma radius_angle_bij: "bij_lens (radius +\<^sub>L angle)"
  by (unfold_locales, auto simp add: lens_defs)

text \<open> The two coordinate systems are incompatible -- we cannot use both the Cartesian and polar
  coordinate lenses simultaneously. \<close>

lemma radius_incompat_fst: "\<not> (radius ##\<^sub>L fst\<^sub>L)"
  apply (auto simp add: lens_defs)
  apply (transfer)
  apply auto
  apply (metis add.commute divide_numeral_1 less_irrefl numeral_One real_sqrt_one sqrt2_less_2 zero_less_divide_iff zero_less_numeral)
  done

lemma radius_incompat_snd: "\<not> (radius ##\<^sub>L snd\<^sub>L)"
  apply (auto simp add: lens_defs)
  apply (transfer)
  apply auto
  apply (metis add.commute divide_numeral_1 lemma_real_divide_sqrt_less less_irrefl real_sqrt_gt_0_iff zero_less_divide_iff zero_less_numeral)
  done

lemma angle_incompat_fst: "\<not> (angle ##\<^sub>L fst\<^sub>L)"
  apply (auto simp add: lens_defs)
  apply (transfer)
  apply auto
  apply (metis cos_arctan cos_arctan_not_zero div_by_1 less_irrefl real_sqrt_one sin_arctan sqrt2_less_2 zero_less_numeral zero_less_one)
  done

lemma angle_incompat_snd: "\<not> (angle ##\<^sub>L snd\<^sub>L)"
  apply (auto simp add: lens_defs)
  apply (transfer)
  apply auto
  apply (metis less_irrefl real_sqrt_one sqrt2_less_2 zero_less_numeral zero_less_one)
  done

end