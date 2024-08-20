section \<open> Channel Types \<close>

theory Channel_Type
  imports Prisms
  keywords "chantype" :: "thy_defn"
begin

text \<open> A channel type is a simplified algebraic datatype where each constructor has exactly 
  one parameter, and it is wrapped up as a prism. It is a dual of an alphabet type. \<close>

subsection \<open> Datatype Constructor Prisms \<close>

definition ctor_prism :: "('a \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'd)" where
[lens_defs]: 
"ctor_prism ctor disc sel = \<lparr> prism_match = (\<lambda> d. if (disc d) then Some (sel d) else None)
                            , prism_build = ctor \<rparr>"

lemma wb_ctor_prism_intro:
  assumes 
    "\<And> v. disc (ctor v)" 
    "\<And> v. sel (ctor v) = v"
    "\<And> s. disc s \<Longrightarrow> ctor (sel s) = s"
  shows "wb_prism (ctor_prism ctor disc sel)"
  by (unfold_locales, simp_all add: lens_defs assms)
     (metis assms(3) option.distinct(1) option.sel)

lemma ctor_codep_intro:
  assumes "\<And> x y. ctor1 x \<noteq> ctor2 y"
  shows "ctor_prism ctor1 disc1 sel1 \<nabla> ctor_prism ctor2 disc2 sel2"
  by (rule prism_diff_intro, simp add: lens_defs assms)

lemma dom_match_ctor_prism [simp]: 
  "dom match\<^bsub>ctor_prism ctor disc sel\<^esub> = Collect disc"
  by (simp add: ctor_prism_def dom_def)

named_theorems chan_defs

subsection \<open> Channel Type Representation \<close>

text \<open> A channel is represented by a name, a type, and a predicate that determines whether the event is on this channel. \<close>

datatype 'a chanrep = Chanrep (chan_name: String.literal) (chan_type: typerep) (is_chan: "'a \<Rightarrow> bool") 

definition evs_of :: "'a chanrep \<Rightarrow> 'a set" where
"evs_of c = {e. is_chan c e}"

lemma evs_of_Chanrep [simp]: "evs_of (Chanrep n t P) = Collect P"
  by (simp add: evs_of_def)

text \<open> A channel type is represented by a list of channels \<close>

type_synonym 'a raw_chantyperep = "'a chanrep list"

text \<open> Well-formed channel type representations \<close>

definition wf_chantyperep :: "'a raw_chantyperep \<Rightarrow> bool" where 
"wf_chantyperep ct = 
  (distinct (map chan_name ct) \<comment> \<open> Each channel name is unique \<close> 
  \<and> (\<forall> x. foldr (\<or>) (map (\<lambda> c. is_chan c x) ct) False) \<comment> \<open> Every event has at least one channel \<close>
  \<and> (\<forall> c1\<in>set ct. \<forall> c2\<in>set ct. \<forall> e. is_chan c1 e \<and> is_chan c2 e \<longrightarrow> c1 = c2) \<comment> \<open> Every event has no more than one channel \<close>
  \<and> (\<forall> c\<in>set ct. \<exists> e. is_chan c e))" \<comment> \<open> Every channel has at least one event \<close>

lemma wf_chantyperepI:
  assumes "distinct (map chan_name ct)" "\<forall> x. foldr (\<or>) (map (\<lambda> c. is_chan c x) ct) False"
    "\<forall> c1\<in>set ct. \<forall> c2\<in>set ct. \<forall> e. is_chan c1 e \<and> is_chan c2 e \<longrightarrow> c1 = c2"
    "\<forall> c\<in>set ct. \<exists> e. is_chan c e"
  shows "wf_chantyperep ct"
  by (simp add: assms wf_chantyperep_def)

typedef 'a chantyperep = "{ctr::'a raw_chantyperep. wf_chantyperep ctr}"
  apply (rule_tac x="[Chanrep STR ''x'' TYPEREP(bool) (\<lambda> x. True)]" in exI)
  apply (auto simp add: wf_chantyperep_def)
  done

setup_lifting type_definition_chantyperep

lift_definition pred_of_chan :: "'a chantyperep \<Rightarrow> String.literal \<Rightarrow> 'a \<Rightarrow> bool" 
is "\<lambda> ct c e. find (\<lambda> c. is_chan c e) ct \<noteq> None" .

definition set_chan :: "'a chantyperep \<Rightarrow> String.literal \<Rightarrow> 'a set" where
"set_chan n ct = Collect (pred_of_chan n ct)"

definition set_chans :: "'a chantyperep \<Rightarrow> String.literal set \<Rightarrow> 'a set" where
"set_chans ct ns = \<Union> (set_chan ct ` ns)" 

named_theorems datatype_disc_thms 
named_theorems disc_thms
named_theorems exhaust_disc_thms

named_theorems chantyperep_defs

method wf_chantyperep = (simp add: comp_def wf_chantyperep_def chantyperep_defs, (meson datatype_disc_thms)?)

method wf_chantyperep' = 
  (rule wf_chantyperepI
  , simp add: comp_def chantyperep_defs
  , (simp add: comp_def chantyperep_defs; (insert exhaust_disc_thms, blast))
  , (simp add: comp_def chantyperep_defs; blast) (* This step could do with optimising -- the simplification is very slow *)
  , (simp add: comp_def chantyperep_defs; (insert disc_thms, blast intro: disc_thms)))

lemma foldr_disj_one_True: "foldr (\<or>) Ps False \<Longrightarrow> (\<exists> P\<in>set Ps. P)"
  by (induct Ps, auto)

text \<open> Every event has a channel \<close>

lemma chantyperep_ev_has_chan: "wf_chantyperep ct \<Longrightarrow> \<exists> c\<in>set ct. is_chan c e"
  using foldr_disj_one_True by (fastforce simp add: wf_chantyperep_def)

definition find_chanrep :: "'a raw_chantyperep \<Rightarrow> 'a \<Rightarrow> 'a chanrep option" where 
"find_chanrep ct e = find (\<lambda> c. is_chan c e) ct"

lemma find_chanrep_Some: "wf_chantyperep ct \<Longrightarrow> \<exists> c\<in>set ct. find_chanrep ct e = Some c"
  by (metis chantyperep_ev_has_chan find_None_iff2 find_Some_iff find_chanrep_def not_Some_eq nth_mem)

text \<open> Every channel has at least one event \<close>

lemma chantyperep_chan_has_ev:"\<lbrakk> wf_chantyperep ct; c \<in> set ct \<rbrakk> \<Longrightarrow> \<exists>e. is_chan c e"
  using wf_chantyperep_def by fastforce

lemma evs_of_inj: "\<lbrakk> wf_chantyperep ct; c \<in> set ct; d \<in> set ct; evs_of c = evs_of d \<rbrakk> \<Longrightarrow> c = d"
  by (metis evs_of_def mem_Collect_eq wf_chantyperep_def)

class chantyperep = 
  fixes chantyperep :: "'a itself \<Rightarrow> 'a raw_chantyperep"
  assumes wf_chantyperep: "wf_chantyperep (chantyperep TYPE('a))"

method chantyperep_inst = (rule chantyperep_class.intro, (intro_classes)[1], rule_tac class.chantyperep.intro, wf_chantyperep')

syntax "_chantyperep" :: "type \<Rightarrow> logic" ("CHANTYPEREP'(_')")
translations "CHANTYPEREP('a)" == "CONST chantyperep TYPE('a)"

context chantyperep
begin

definition chan_names :: "'a itself \<Rightarrow> String.literal list" where 
"chan_names t = map chan_name (chantyperep t)"

lemma distinct_chan_names [simp]: "distinct (chan_names TYPE('a))"
  using chan_names_def local.wf_chantyperep wf_chantyperep_def by auto
  
definition ev_chanrep :: "'a \<Rightarrow> 'a chanrep" where
"ev_chanrep e = the (find_chanrep CHANTYPEREP('a) e)"

lemma range_ev_chanrep: "range ev_chanrep = set CHANTYPEREP('a)"
  apply (auto simp add: ev_chanrep_def image_def)
  apply (metis find_chanrep_Some local.wf_chantyperep option.sel)
  apply (metis find_Some_iff find_chanrep_Some find_chanrep_def local.wf_chantyperep option.sel wf_chantyperep_def)
  done

lemma finite_chanreps: "finite (range ev_chanrep)"
  using range_ev_chanrep by auto

definition ev_set_of :: "'a \<Rightarrow> 'a set" where
"ev_set_of e = Collect (is_chan (ev_chanrep e))"

text \<open> An independent family of events, each corresponding to one set of channels. \<close>

definition ChanBasis :: "'a set set" where
"ChanBasis = evs_of ` range ev_chanrep"

lemma family_chan_basis: "\<Union> ChanBasis = UNIV"
  apply (auto simp add: ChanBasis_def evs_of_def)
  apply (metis chantyperep_ev_has_chan image_iff local.wf_chantyperep range_ev_chanrep)
  done

lemma indep_chan_basis: "\<lbrakk> A \<in> ChanBasis; B \<in> ChanBasis; A \<noteq> B \<rbrakk> \<Longrightarrow> A \<inter> B = {}"
  apply (auto simp add: ChanBasis_def evs_of_def)
  apply (metis local.wf_chantyperep rangeI range_ev_chanrep wf_chantyperep_def)+
  done

end

subsection \<open> Prisms with a Channel Representation \<close>

definition has_chanrep :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e::chantyperep) \<Rightarrow> bool" where 
"has_chanrep c = (\<exists> d. d \<in> set CHANTYPEREP('e) \<and> evs_of d = dom (match\<^bsub>c\<^esub>))"

definition chanrep_of :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e::chantyperep) \<Rightarrow> 'e chanrep" where
"chanrep_of c = (SOME d. d \<in> set CHANTYPEREP('e) \<and> evs_of d = dom (match\<^bsub>c\<^esub>))"  

lemma chanrep_of_eqI:
  fixes c :: "'a \<Longrightarrow>\<^sub>\<triangle> 'e::chantyperep" and d :: "'e chanrep"
  assumes "wb_prism c" "d \<in> set CHANTYPEREP('e)" "dom match\<^bsub>c\<^esub> = evs_of d"
  shows "chanrep_of c = d"
  using assms
  apply (simp add: chanrep_of_def)
  apply (rule some_equality)
   apply simp
  using evs_of_inj wf_chantyperep apply blast
  done

lemma ev_chanrep_build [simp]: 
  fixes c :: "'a \<Longrightarrow>\<^sub>\<triangle> 'e::chantyperep"
  assumes "wb_prism c" "has_chanrep c"
  shows "ev_chanrep (build\<^bsub>c\<^esub> v) = chanrep_of c"
proof -
  obtain d where d: "d \<in> set CHANTYPEREP('e)" "evs_of d = dom (match\<^bsub>c\<^esub>)"
    by (meson assms has_chanrep_def)
  hence chanrep_c: "chanrep_of c = d"
    by (metis (mono_tags, lifting) chanrep_of_def evs_of_inj someI_ex wf_chantyperep)
  have "is_chan d (build\<^bsub>c\<^esub> v)"
    using assms(1) d(2) evs_of_def by fastforce
  hence "find (\<lambda>Q. is_chan Q (build\<^bsub>c\<^esub> v)) CHANTYPEREP('e) = Some d"
    by (metis d(1) find_Some_iff find_chanrep_Some find_chanrep_def wf_chantyperep wf_chantyperep_def)
  thus ?thesis
    by (simp add: chanrep_c ev_chanrep_def find_chanrep_def)
qed

lemma ev_set_of_build [simp]:
  fixes c :: "'a \<Longrightarrow>\<^sub>\<triangle> 'e::chantyperep"
  assumes "wb_prism c" "has_chanrep c"
  shows "ev_set_of (build\<^bsub>c\<^esub> v) = Collect (is_chan (chanrep_of c))"
  by (simp add: assms(1) assms(2) ev_set_of_def)

method prism_has_chanrep for ct :: "'e chanrep" = (simp add: has_chanrep_def, rule exI[where x="ct"], rule conjI, simp add: chantyperep_defs, simp add: chan_defs)

method prism_chanrep = (rule chanrep_of_eqI, simp, simp add: chantyperep_defs, simp add: chan_defs)

subsection \<open> Channel Type Command \<close>

ML_file "Channel_Type.ML"

end