theory QKD
  imports Prob
begin
datatype event = AsOne bool | AchX bool | BchX bool | EchX bool | BmOne bool | EmOne bool

datatype protocol = Protocol "event list set"

primrec the_prot :: "protocol \<Rightarrow> event list set"
  where
"the_prot (Protocol evs) = evs"

definition prot_mem :: "event list \<Rightarrow> protocol \<Rightarrow> bool"  ("_ \<in> _" 50)
  where 
"prot_mem l evs \<equiv> (l \<in> (the_prot evs))"

definition insertp :: "event list \<Rightarrow> protocol \<Rightarrow> protocol"
  where
"insertp l evs \<equiv> Protocol(insert l (the_prot evs))" 

inductive state_transition_qkd :: "[protocol, protocol] \<Rightarrow> bool" ("(_  \<rightarrow>\<^sub>Q _)" 50)
where 
  AsendsBitb: "[] \<in> evs \<Longrightarrow> evs \<rightarrow>\<^sub>Q insertp [AsOne b] evs"
| AchosesPolX: "l \<in> evs \<Longrightarrow> hd l = AsOne b \<Longrightarrow>
                evs \<rightarrow>\<^sub>Q insertp (AchX b' # l) evs"
| BchosesPolX: "l \<in> evs \<Longrightarrow> hd l = AchX b \<Longrightarrow>
                evs \<rightarrow>\<^sub>Q insertp (BchX b' # l) evs"
| BmeasuresOK: "l \<in> evs \<Longrightarrow>  hd l = BchX b \<Longrightarrow> hd(tl l) = AchX b \<Longrightarrow>
                 evs \<rightarrow>\<^sub>Q insertp (BmOne b # l) evs"
| BmeasuresNOK: "l \<in> evs \<Longrightarrow>  hd l = BchX b \<Longrightarrow> hd(tl l) = AchX b' \<Longrightarrow>
                 b \<noteq> b' \<Longrightarrow> evs \<rightarrow>\<^sub>Q insertp (BmOne b'' # l) evs"
| EchosesPolX: "l \<in> evs \<Longrightarrow> hd l = AchX b \<Longrightarrow>
                evs \<rightarrow>\<^sub>Q insertp (EchX b' # l) evs"
| EintercptOK: "l \<in> evs \<Longrightarrow> hd l = EchX b \<Longrightarrow> hd(tl l) = AchX b \<Longrightarrow>
                evs \<rightarrow>\<^sub>Q insertp (EmOne b # l) evs"
| EintrcptNOK: "l \<in> evs \<Longrightarrow>  hd l = EchX b \<Longrightarrow> hd(tl l) = AchX b' \<Longrightarrow>
                b \<noteq> b' \<Longrightarrow> evs \<rightarrow>\<^sub>Q insertp (EmOne b'' # l) evs"
| B_E_iterate: "l \<in> evs \<Longrightarrow> hd l = BmOne b \<or> hd l = EmOne b \<Longrightarrow>
                evs \<rightarrow>\<^sub>Q insertp [AsOne b] evs"

instantiation "protocol" :: state
begin

definition 
   state_transition_qkd_inst_def: "(i \<rightarrow>\<^sub>i i') =  (i \<rightarrow>\<^sub>Q (i' :: protocol))"


instance
  by (rule MC.class.MC.state.of_class.intro)
end

definition state_transition_qkd_refl ("(_ \<rightarrow>\<^sub>Q* _)" 50)
where "s \<rightarrow>\<^sub>Q* s' \<equiv> ((s,s') \<in> {(x,y). state_transition_qkd x y}\<^sup>*)"
  
definition global_policy :: "protocol \<Rightarrow> bool"
  where 
"global_policy e \<equiv> (\<forall> l. l \<in> e \<longrightarrow> (\<forall> b. \<not>(AsOne b \<in> set l \<and> EmOne b \<in> set l)))"

definition negated_policy :: "protocol set"
  where 
"negated_policy \<equiv> {e :: protocol. \<not>(global_policy e)}"

definition qkd_scenario :: "protocol"
  where
"qkd_scenario \<equiv> Protocol {([] :: event list)}"

definition Iqkd :: "protocol set"
  where 
"Iqkd \<equiv> {qkd_scenario}"

definition qkd_Kripke
  where
"qkd_Kripke \<equiv> Kripke {I. qkd_scenario  \<rightarrow>\<^sub>Q* I} Iqkd"

definition QKD1
  where
"QKD1 \<equiv> insertp [AsOne True] qkd_scenario"

definition QKD2
  where
"QKD2 \<equiv> insertp [AchX True, AsOne True] QKD1"

definition QKD3
  where
"QKD3 \<equiv> insertp [EchX True, AchX True, AsOne True] QKD2"

definition QKD4
  where
"QKD4 \<equiv> insertp [EmOne True, EchX True, AchX True, AsOne True] QKD3"


lemma step0: "qkd_scenario \<rightarrow>\<^sub>Q QKD1"
proof (unfold qkd_scenario_def QKD1_def)
  show "Protocol {[]}  \<rightarrow>\<^sub>Q insertp [AsOne True] (Protocol {[]})"
    apply (insert AsendsBitb)
    apply (drule_tac x = "Protocol {[]}" in meta_spec)
    apply (drule_tac x = True in meta_spec)
    apply (simp add: insertp_def)
    apply (erule meta_mp)
by (simp add: prot_mem_def)
qed

lemma step1: "QKD1 \<rightarrow>\<^sub>Q QKD2"
proof (unfold QKD1_def QKD2_def, rule_tac l = "[AsOne True]" and b = True in AchosesPolX) 
  show "[AsOne True] \<in>  insertp [AsOne True] qkd_scenario" by (simp add: insertp_def prot_mem_def)
next show "hd [AsOne True] = AsOne True" by simp
qed

lemma step1R: "QKD1 \<rightarrow>\<^sub>Q* QKD2"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD1, QKD2) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step1, auto)
qed

lemma step2: "QKD2 \<rightarrow>\<^sub>Q QKD3"
proof (unfold QKD2_def QKD3_def, rule_tac l = "[AchX True, AsOne True]" and 
          b = True and b' = True in EchosesPolX)
  show "[AchX True, AsOne True] \<in> insertp [AchX True, AsOne True] QKD1"
    by (simp add: insertp_def prot_mem_def)+
next show "hd [AchX True, AsOne True] = AchX True" by simp
qed

lemma step2R: "QKD2 \<rightarrow>\<^sub>Q* QKD3"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD2, QKD3) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step2, auto)
qed

lemma step3: "QKD3 \<rightarrow>\<^sub>Q QKD4"
proof (unfold QKD3_def QKD4_def, rule_tac l = "[EchX True, AchX True, AsOne True]" and 
          b = True in EintercptOK)
  show "[EchX True, AchX True, AsOne True] \<in> insertp [EchX True, AchX True, AsOne True] QKD2"
    by (simp add: insertp_def prot_mem_def)
next show "hd [EchX True, AchX True, AsOne True] = EchX True" by simp
next show "hd (tl [EchX True, AchX True, AsOne True]) = AchX True" by simp
qed

(* QKD4 violates global policy *)
lemma QKD4_bad: "\<not> global_policy QKD4"
proof (simp add: QKD4_def global_policy_def)
  show "\<exists>l::event list.
       l \<in> insertp [EmOne True, EchX True, AchX True, AsOne True] QKD3 \<and>
       (\<exists>b::bool. AsOne b \<in> set l \<and> EmOne b \<in> set l)"
    apply (rule_tac x = "[EmOne True, EchX True, AchX True, AsOne True]" in exI)
    apply (rule conjI)
     apply (simp add: insertp_def prot_mem_def)
    apply (rule_tac x = True in exI)
    by simp
qed

lemma qkd_ref: "[\<N>\<^bsub>(Iqkd,negated_policy)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Iqkd,negated_policy)\<^esup> \<sqsubseteq>
  [\<N>\<^bsub>(Iqkd,{QKD1})\<^esub>, \<N>\<^bsub>({QKD1},{QKD2})\<^esub>, \<N>\<^bsub>({QKD2},{QKD3})\<^esub>, \<N>\<^bsub>({QKD3},negated_policy)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Iqkd,negated_policy)\<^esup>"  
proof (rule_tac l = "[]" and
                l' = "[\<N>\<^bsub>(Iqkd,{QKD1})\<^esub>, \<N>\<^bsub>({QKD1},{QKD2})\<^esub>, \<N>\<^bsub>({QKD2},{QKD3})\<^esub>, \<N>\<^bsub>({QKD3},negated_policy)\<^esub>]" and
                l'' = "[]" and si = Iqkd and si' = "Iqkd" and si'' = negated_policy and
                si''' = negated_policy in refI, simp, rule refl)
  show "([\<N>\<^bsub>(Iqkd, {QKD1})\<^esub>, \<N>\<^bsub>({QKD1}, {QKD2})\<^esub>, \<N>\<^bsub>({QKD2}, {QKD3})\<^esub>,
      \<N>\<^bsub>({QKD3}, negated_policy)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Iqkd, negated_policy)\<^esup>) =
    ([] @
     [\<N>\<^bsub>(Iqkd, {QKD1})\<^esub>, \<N>\<^bsub>({QKD1}, {QKD2})\<^esub>, \<N>\<^bsub>({QKD2}, {QKD3})\<^esub>, \<N>\<^bsub>({QKD3}, negated_policy)\<^esub>] @
     [] \<oplus>\<^sub>\<and>\<^bsup>(Iqkd, negated_policy)\<^esup>)"
    by simp
qed


lemma att_qkd: 
"\<turnstile>[\<N>\<^bsub>(Iqkd,{QKD1})\<^esub>,\<N>\<^bsub>({QKD1},{QKD2})\<^esub>,\<N>\<^bsub>({QKD2},{QKD3})\<^esub>,\<N>\<^bsub>({QKD3},negated_policy)\<^esub>]\<oplus>\<^sub>\<and>\<^bsup>(Iqkd,negated_policy)\<^esup>" 
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(Iqkd, {QKD1})\<^esub>"
    apply (simp add: Iqkd_def att_base)
    apply (subst state_transition_qkd_inst_def)
    by (rule step0)
next show " \<turnstile>[\<N>\<^bsub>({QKD1}, {QKD2})\<^esub>, \<N>\<^bsub>({QKD2}, {QKD3})\<^esub>, \<N>\<^bsub>({QKD3}, negated_policy)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({QKD1}, negated_policy)\<^esup> "
  proof (subst att_and, simp, rule conjI)
    show "\<turnstile>\<N>\<^bsub>({QKD1}, {QKD2})\<^esub>"
      apply (simp add: att_base)
apply (subst state_transition_qkd_inst_def)
      by (rule step1)
  next show " \<turnstile>[\<N>\<^bsub>({QKD2}, {QKD3})\<^esub>, \<N>\<^bsub>({QKD3}, negated_policy)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({QKD2}, negated_policy)\<^esup>"
    proof (subst att_and, simp, rule conjI)
      show "\<turnstile>\<N>\<^bsub>({QKD2}, {QKD3})\<^esub>"
apply (simp add: att_base)
apply (subst state_transition_qkd_inst_def)
        by (rule step2)
    next show  "\<turnstile>[\<N>\<^bsub>({QKD3}, negated_policy)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({QKD3}, negated_policy)\<^esup>"
   apply (subst att_and, simp)
apply (simp add: negated_policy_def att_base)
        apply (subst state_transition_qkd_inst_def)
        apply (rule_tac x = QKD4 in exI)
        apply (rule conjI)
        apply (rule QKD4_bad)
        by (rule step3)
    qed
  qed
qed

lemma qkp_abs_att: "\<turnstile>\<^sub>V [\<N>\<^bsub>(Iqkd,negated_policy)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Iqkd,negated_policy)\<^esup>"
proof (rule ref_valI, rule qkd_ref, rule att_qkd)
qed

(* show now EF attack using the meta-theory Correctness rule AT_EF*)
theorem qkd_EF: "qkd_Kripke \<turnstile> EF negated_policy"
proof -
  have a: "\<turnstile> [\<N>\<^bsub>(Iqkd,{QKD1})\<^esub>,\<N>\<^bsub>({QKD1},{QKD2})\<^esub>,\<N>\<^bsub>({QKD2},{QKD3})\<^esub>,\<N>\<^bsub>({QKD3},negated_policy)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Iqkd,negated_policy)\<^esup>"
    by (rule att_qkd)
  hence "(Iqkd, negated_policy) = 
     attack ([\<N>\<^bsub>(Iqkd,{QKD1})\<^esub>,\<N>\<^bsub>({QKD1},{QKD2})\<^esub>,\<N>\<^bsub>({QKD2},{QKD3})\<^esub>,\<N>\<^bsub>({QKD3},negated_policy)\<^esub>]\<oplus>\<^sub>\<and>\<^bsup>(Iqkd,negated_policy)\<^esup>)"
    by simp
  hence "Kripke {s:: protocol. \<exists> e:: protocol\<in> Iqkd. e \<rightarrow>\<^sub>Q* s} Iqkd \<turnstile> EF negated_policy"
    apply (insert a)
    apply (drule AT_EF)
    apply simp
    by (simp add: state_transition_qkd_refl_def state_transition_refl_def state_transition_qkd_inst_def)
  thus
  "qkd_Kripke \<turnstile> EF negated_policy"
    by (simp add: qkd_Kripke_def qkd_scenario_def Iqkd_def)
qed

(* Probabilistic Analysis *)
typedef outcome = "{l :: event list. length l = 4}"
proof (rule_tac x = "[EmOne True, EchX True, AchX True, AsOne True]" in exI, simp)
qed


instance outcome :: finite
proof (rule Finite_Set.finite_class.intro)
  show "OFCLASS(outcome, type_class)"
    sorry
next show "class.finite TYPE(outcome) "
    sorry
qed

locale QKD = 
  fixes qkd_ops :: "outcome \<Rightarrow> real"
  defines qkd_ops_def: 
    "qkd_ops \<equiv>
    (\<lambda> x. case Rep_outcome x of
          [EmOne False, EchX False, AchX False, AsOne False] \<Rightarrow> 1/8
       |  [EmOne True, EchX False, AchX False, AsOne False] \<Rightarrow> 0
       |  [EmOne False, EchX True, AchX False, AsOne False] \<Rightarrow> 1/16
       |  [EmOne True, EchX True, AchX False, AsOne False] \<Rightarrow> 1/16
       |  [EmOne False, EchX False, AchX True, AsOne False] \<Rightarrow> 1/16
       |  [EmOne True, EchX False, AchX True, AsOne False] \<Rightarrow> 1/16
       |  [EmOne False, EchX True, AchX True, AsOne False] \<Rightarrow> 1/8
       |  [EmOne True, EchX True, AchX True, AsOne False] \<Rightarrow> 0
       |  [EmOne False, EchX False, AchX False, AsOne True] \<Rightarrow> 0
       |  [EmOne True, EchX False, AchX False, AsOne True] \<Rightarrow> 1/8
       |  [EmOne False, EchX True, AchX False, AsOne True] \<Rightarrow> 1/16
       |  [EmOne True, EchX True, AchX False, AsOne True] \<Rightarrow> 1/16
       |  [EmOne False, EchX False, AchX True, AsOne True] \<Rightarrow> 1/16
       |  [EmOne True, EchX False, AchX True, AsOne True] \<Rightarrow> 1/16
       |  [EmOne False, EchX True, AchX True, AsOne True] \<Rightarrow> 0
      |  [EmOne True, EchX True, AchX True, AsOne True] \<Rightarrow> 1/8
       | _ \<Rightarrow> 0)"

  fixes qkd_ops' :: "event list \<Rightarrow> real"
  defines qkd_ops'_def: 
    "qkd_ops' \<equiv>
    (\<lambda> x. case x of
          [EmOne False, EchX False, AchX False, AsOne False] \<Rightarrow> 1/8
       |  [EmOne True, EchX False, AchX False, AsOne False] \<Rightarrow> 0
       |  [EmOne False, EchX True, AchX False, AsOne False] \<Rightarrow> 1/16
       |  [EmOne True, EchX True, AchX False, AsOne False] \<Rightarrow> 1/16
       |  [EmOne False, EchX False, AchX True, AsOne False] \<Rightarrow> 1/16
       |  [EmOne True, EchX False, AchX True, AsOne False] \<Rightarrow> 1/16
       |  [EmOne False, EchX True, AchX True, AsOne False] \<Rightarrow> 1/8
       |  [EmOne True, EchX True, AchX True, AsOne False] \<Rightarrow> 0
       |  [EmOne False, EchX False, AchX False, AsOne True] \<Rightarrow> 0
       |  [EmOne True, EchX False, AchX False, AsOne True] \<Rightarrow> 1/8
       |  [EmOne False, EchX True, AchX False, AsOne True] \<Rightarrow> 1/16
       |  [EmOne True, EchX True, AchX False, AsOne True] \<Rightarrow> 1/16
       |  [EmOne False, EchX False, AchX True, AsOne True] \<Rightarrow> 1/16
       |  [EmOne True, EchX False, AchX True, AsOne True] \<Rightarrow> 1/16
       |  [EmOne False, EchX True, AchX True, AsOne True] \<Rightarrow> 0
      |  [EmOne True, EchX True, AchX True, AsOne True] \<Rightarrow> 1/8
       | _ \<Rightarrow> 0)"

fixes \<A> :: "outcome set set"
defines A_def:
   "\<A> \<equiv> {{s :: outcome. (\<exists> e. Rep_outcome s = [e, EchX True, AchX True, AsOne True])},
          {s :: outcome. (\<exists> e. Rep_outcome s = [e, EchX False, AchX True, AsOne True])},
          {s :: outcome. (\<exists> e. Rep_outcome s = [e, EchX True, AchX False, AsOne True])},
          {s :: outcome. (\<exists> e. Rep_outcome s = [e, EchX False, AchX False, AsOne True])},
          {s :: outcome. (\<exists> e. Rep_outcome s = [e, EchX True, AchX True, AsOne False])},
          {s :: outcome. (\<exists> e. Rep_outcome s = [e, EchX False, AchX True, AsOne False])},
          {s :: outcome. (\<exists> e. Rep_outcome s = [e, EchX True, AchX False, AsOne False])},
          {s :: outcome. (\<exists> e. Rep_outcome s = [e, EchX False, AchX False, AsOne False])}
}"

fixes J :: "real \<Rightarrow> bool"
defines J_def: "J \<equiv> (\<lambda> x. x = 3/4)"

begin
lemma qkd_prob_dist_lem: "pmap qkd_ops \<in> prob_dist_def"
  apply (rule pmap_ops)
   apply (unfold qkd_ops_def)
   apply (rule allI)
   apply (case_tac x)
   apply auto
   apply (case_tac y)
    apply simp+
   apply (case_tac list)
    apply simp+
apply (case_tac lista)
    apply simp+
apply (case_tac listb)
    apply simp+
  apply auto
  sorry

lemma all_eigth: "(Rep_prob_dist(P:: (outcome)prob_dist)
          ({s :: outcome. (\<exists> e. Rep_outcome s = [e, EchX True, AchX True, AsOne True])})) = 1/8"
  sorry

definition EmOne' :: "outcome set"
  where 
"(EmOne' :: outcome set) \<equiv> {l :: outcome. hd (Rep_outcome l) = (EmOne True :: event)}"

lemma PEmOne': "(Rep_prob_dist(P:: (outcome)prob_dist)) EmOne' = 1/2"
  sorry

definition AsOne' :: "outcome set"
  where 
"(AsOne' :: outcome set) \<equiv> {l :: outcome. (Rep_outcome l) ! 3 = (AsOne True :: event)}"


lemma cond_prob_AsOne_EmOne: "(P :: (outcome)prob_dist)[AsOne'|EmOne'] = 3/4"
  sorry



lemma qkd_Eve_attack: "qkd_Kripke (pmap qkd_ops') \<turnstile>PF\<^sub>J negated_policy"
  oops



end