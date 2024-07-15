section \<open> Channel Types \<close>

theory Channel_Type
  imports Prisms
  keywords "chantype" :: "thy_defn"
begin

text \<open> A channel type is a simplified algebraic datatype where each constructor has exactly 
  one parameter, and it is wrapped up as a prism. It a dual of an alphabet type. \<close>

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

subsection \<open> Channel Type Representation \<close>

text \<open> A channel is represented by a name, a type, and a predicate that determines whether the event is on this channel. \<close>

datatype 'a chanrep = Chanrep (chan_name: String.literal) (chan_type: String.literal) (is_chan: "'a \<Rightarrow> bool") 

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
  \<and> (\<forall> x. foldr (\<or>) (map (\<lambda> c. is_chan c x) ct) False) \<comment> \<open> Every event has a channel \<close>
  \<and> (\<forall> c1\<in>set ct. \<forall> c2\<in>set ct. \<forall> e. is_chan c1 e \<and> is_chan c2 e \<longrightarrow> c1 = c2) \<comment> \<open> Every event has exactly one channel \<close>
  \<and> (\<forall> c\<in>set ct. \<exists> e. is_chan c e))" \<comment> \<open> Every channel has at least one event \<close>

typedef 'a chantyperep = "{ctr::'a raw_chantyperep. wf_chantyperep ctr}"
  apply (rule_tac x="[Chanrep STR ''x'' STR ''t'' (\<lambda> x. True)]" in exI)
  apply (auto simp add: wf_chantyperep_def)
  done

setup_lifting type_definition_chantyperep

lift_definition pred_of_chan :: "'a chantyperep \<Rightarrow> String.literal \<Rightarrow> 'a \<Rightarrow> bool" 
is "\<lambda> ct c e. find (\<lambda> c. is_chan c e) ct \<noteq> None" .

definition set_chan :: "'a chantyperep \<Rightarrow> String.literal \<Rightarrow> 'a set" where
"set_chan n ct = Collect (pred_of_chan n ct)"

definition set_chans :: "'a chantyperep \<Rightarrow> String.literal set \<Rightarrow> 'a set" where
"set_chans ct ns = \<Union> (set_chan ct ` ns)" 

method wf_chantyperep uses disc def = (force intro: disc simp add: wf_chantyperep_def def)

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

syntax "_chantyperep" :: "type \<Rightarrow> logic" ("CHANTYPEREP'(_')")
translations "CHANTYPEREP('a)" == "CONST chantyperep TYPE('a)"

context chantyperep
begin

definition chan_names :: "'a itself \<Rightarrow> String.literal list" where 
"chan_names t = map chan_name (chantyperep t)"

lemma distinct_chan_names [simp]: "distinct (chan_names TYPE('a))"
  using chan_names_def local.wf_chantyperep wf_chantyperep_def by auto
  
definition chanrep_of :: "'a \<Rightarrow> 'a chanrep" where
"chanrep_of e = the (find_chanrep CHANTYPEREP('a) e)"

lemma range_chanrep_of: "range chanrep_of = set CHANTYPEREP('a)"
  apply (auto simp add: chanrep_of_def image_def)
  apply (metis find_chanrep_Some local.wf_chantyperep option.sel)
  apply (metis find_Some_iff find_chanrep_Some find_chanrep_def local.wf_chantyperep option.sel wf_chantyperep_def)
  done

lemma finite_chanreps: "finite (range chanrep_of)"
  using range_chanrep_of by auto

text \<open> An independent family of events, each corresponding to one set of channels. \<close>

definition ChanBasis :: "'a set set" where
"ChanBasis = evs_of ` range chanrep_of"

lemma family_chan_basis: "\<Union> ChanBasis = UNIV"
  apply (auto simp add: ChanBasis_def evs_of_def)
  apply (metis chantyperep_ev_has_chan image_iff local.wf_chantyperep range_chanrep_of)
  done

lemma indep_chan_basis: "\<lbrakk> A \<in> ChanBasis; B \<in> ChanBasis; A \<noteq> B \<rbrakk> \<Longrightarrow> A \<inter> B = {}"
  apply (auto simp add: ChanBasis_def evs_of_def)
  apply (metis local.wf_chantyperep rangeI range_chanrep_of wf_chantyperep_def)+
  done

end

subsection \<open> Prisms with a Channel Representation \<close>

definition prism_chanrep :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e::chantyperep) \<Rightarrow> 'e chanrep" where
"prism_chanrep c = (SOME d. d \<in> set CHANTYPEREP('e) \<and> evs_of d = dom (match\<^bsub>c\<^esub>))"  

lemma prism_chanrep_eqI:
  fixes c :: "'a \<Longrightarrow>\<^sub>\<triangle> 'e::chantyperep" and d :: "'e chanrep"
  assumes "wb_prism c" "d \<in> set CHANTYPEREP('e)" "dom match\<^bsub>c\<^esub> = evs_of d"
  shows "prism_chanrep c = d"
  using assms
  apply (simp add: prism_chanrep_def)
  apply (rule some_equality)
   apply simp
  using evs_of_inj wf_chantyperep apply blast
  done

subsection \<open> Channel Type Command \<close>

ML_file "Channel_Type.ML"

end