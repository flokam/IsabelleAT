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
(* Iteration only makes sense if we insert numberings to the bits. Otherwise
   there would be repititions of the same bit which defies the purpose.
   Numbers can easily be introduced by having an additinal parameter  "i: nat"
   to index the bits.
| B_E_iterate: "l \<in> evs \<Longrightarrow> hd l = BmOne b \<or> hd l = EmOne b \<Longrightarrow>
                evs \<rightarrow>\<^sub>Q insertp [AsOne b] evs"
*)
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

(* Eve has success because she chooses the same scheme as Alice 
  "": [EmOne True, EchX True, AchX True, AsOne True]
   e: [EmOne False, EchX True, AchX True, AsOne False]
   f: [EmOne True, EchX False, AchX False, AsOne True]
   g: [EmOne False, EchX False, AchX False, AsOne False]*)

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

(* e *)
definition QKD1e
  where
"QKD1e \<equiv> insertp [AsOne False] qkd_scenario"

definition QKD2e
  where
"QKD2e \<equiv> insertp [AchX True, AsOne False] QKD1e"

definition QKD3e
  where
"QKD3e \<equiv> insertp [EchX True, AchX True, AsOne False] QKD2e"

definition QKD4e
  where
"QKD4e \<equiv> insertp [EmOne False, EchX True, AchX True, AsOne False] QKD3e"

(* f *)
definition QKD1f
  where
"QKD1f \<equiv> insertp [AsOne True] qkd_scenario"

definition QKD2f
  where
"QKD2f \<equiv> insertp [AchX False, AsOne True] QKD1f"

definition QKD3f
  where
"QKD3f \<equiv> insertp [EchX False, AchX False, AsOne True] QKD2f"

definition QKD4f
  where
"QKD4f \<equiv> insertp [EmOne True, EchX False, AchX False, AsOne True] QKD3f"

(* g *)
definition QKD1g
  where
"QKD1g \<equiv> insertp [AsOne False] qkd_scenario"

definition QKD2g
  where
"QKD2g \<equiv> insertp [AchX False, AsOne False] QKD1g"

definition QKD3g
  where
"QKD3g \<equiv> insertp [EchX False, AchX False, AsOne False] QKD2g"

definition QKD4g
  where
"QKD4g \<equiv> insertp [EmOne False, EchX False, AchX False, AsOne False] QKD3g"


(* E succeeds despite wrong scheme: 
   a: [EmOne True, EchX True, AchX False, AsOne True] and
   b: [EmOne False, EchX True, AchX False, AsOne False]    
   c: [EmOne True, EchX False, AchX True, AsOne True] and
   d: [EmOne False, EchX False, AchX True, AsOne False]   *)

definition QKD1a
  where
"QKD1a \<equiv> insertp [AsOne True] qkd_scenario"

definition QKD2a
  where
"QKD2a \<equiv> insertp [AchX False, AsOne True] QKD1a"

definition QKD3a
  where
"QKD3a \<equiv> insertp [EchX True, AchX False, AsOne True] QKD2a"

definition QKD4a
  where
"QKD4a \<equiv> insertp [EmOne True, EchX True, AchX False, AsOne True] QKD3a"

(* b *)
definition QKD1b
  where
"QKD1b \<equiv> insertp [AsOne False] qkd_scenario"

definition QKD2b
  where
"QKD2b \<equiv> insertp [AchX False, AsOne False] QKD1b"

definition QKD3b
  where
"QKD3b \<equiv> insertp [EchX True, AchX False, AsOne False] QKD2b"

definition QKD4b
  where
"QKD4b \<equiv> insertp [EmOne False, EchX True, AchX False, AsOne False] QKD3b"


(* c *)
definition QKD1c
  where
"QKD1c \<equiv> insertp [AsOne True] qkd_scenario"

definition QKD2c
  where
"QKD2c \<equiv> insertp [AchX True, AsOne True] QKD1c"

definition QKD3c
  where
"QKD3c \<equiv> insertp [EchX False, AchX True, AsOne True] QKD2c"

definition QKD4c
  where
"QKD4c \<equiv> insertp [EmOne True, EchX False, AchX True, AsOne True] QKD3c"

(* d *)
definition QKD1d
  where
"QKD1d \<equiv> insertp [AsOne False] qkd_scenario"

definition QKD2d
  where
"QKD2d \<equiv> insertp [AchX True, AsOne False] QKD1d"

definition QKD3d
  where
"QKD3d \<equiv> insertp [EchX False, AchX True, AsOne False] QKD2d"

definition QKD4d
  where
"QKD4d \<equiv> insertp [EmOne False, EchX False, AchX True, AsOne False] QKD3d"


(* step relation for QKD *)
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

(* Now lift this basic outcome distribution to protocol and then to protocol lists*)
  fixes qkd_ops'' :: "protocol \<Rightarrow> real"
  defines qkd_ops''_def: 
    "qkd_ops'' P \<equiv> fsum(fmap qkd_ops' (the_prot P))"


  fixes qkd_ops''' :: "protocol list \<Rightarrow> real"
  defines qkd_ops'''_def: 
    "qkd_ops''' pl \<equiv> fold (\<lambda> x y. (qkd_ops'' x) + y) pl 0"



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

(* define protocol lists representing Eve's successful attacks *)
fixes QKD_L QKD_La QKD_Lb QKD_Lc QKD_Ld QKD_Le QKD_Lf QKD_Lg :: "protocol list"
defines QKD_L_def: "QKD_L \<equiv> [qkd_scenario, QKD1, QKD2, QKD3, QKD4]"
defines QKD_La_def: "QKD_La \<equiv> [qkd_scenario, QKD1a, QKD2a, QKD3a, QKD4a]"
defines QKD_Lb_def: "QKD_Lb \<equiv> [qkd_scenario, QKD1b, QKD2b, QKD3b, QKD4b]"
defines QKD_Lc_def: "QKD_Lc \<equiv> [qkd_scenario, QKD1c, QKD2c, QKD3c, QKD4c]"
defines QKD_Ld_def: "QKD_Ld \<equiv> [qkd_scenario, QKD1d, QKD2d, QKD3d, QKD4d]"
defines QKD_Le_def: "QKD_Le \<equiv> [qkd_scenario, QKD1e, QKD2e, QKD3e, QKD4e]"
defines QKD_Lf_def: "QKD_Lf \<equiv> [qkd_scenario, QKD1f, QKD2f, QKD3f, QKD4f]"
defines QKD_Lg_def: "QKD_Lg \<equiv> [qkd_scenario, QKD1g, QKD2g, QKD3g, QKD4g]"


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
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
(*
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
   apply (case_tac "Rep_outcome (Abs_outcome [a, aa, ab, ac])", simp)
*)
   apply auto
   apply (case_tac ad, simp+)
    apply (case_tac x6, simp+)
    apply (case_tac list, simp+)
    apply auto
   apply (case_tac ae, simp+)
      apply auto
    apply (case_tac x4, simp+)
     apply auto
        apply (case_tac lista, simp+)
     apply auto
   apply (case_tac ad, simp+)
         apply auto
   apply (case_tac x2, simp+)
      apply auto
    apply (case_tac list, simp+)
    apply auto
   apply (case_tac ad, simp+)
         apply auto
      apply (case_tac x1)
       apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac list)
        apply auto
       apply (case_tac ad)
        apply auto
       apply (case_tac x1)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac ad)
        apply auto
       apply (case_tac x2)
        apply auto
       apply (case_tac list)
        apply auto
       apply (case_tac ad)
        apply auto
       apply (case_tac x1)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac list)
        apply auto
       apply (case_tac ad)
        apply auto
       apply (case_tac x1)
     apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac list)
        apply auto
       apply (case_tac ad)
        apply auto
       apply (case_tac x4)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac ad)
        apply auto
       apply (case_tac x2)
        apply auto
       apply (case_tac list)
        apply auto
       apply (case_tac ad)
        apply auto
       apply (case_tac x1)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac list)
        apply auto
       apply (case_tac ad)
        apply auto
       apply (case_tac x1)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac list)
        apply auto
       apply (case_tac ad)
        apply auto
       apply (case_tac x2)
        apply auto
       apply (case_tac ad)
        apply auto
       apply (case_tac x2)
        apply auto
       apply (case_tac ae)
        apply auto
       apply (case_tac x1)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac ae)
        apply auto
       apply (case_tac x1)
        apply auto
       apply (case_tac lista)
        apply auto
       apply (case_tac lista)
        apply auto
(* now = 1 *)
  apply (simp add: sum_def)
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

lemma qkd_eval_step1: "qkd_Kripke \<turnstile>F negated_policy = {QKD_L, QKD_La, QKD_Lb, QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg}"
  sorry


(* Proof for unequality are unfortunately better done as separate lemmas
   to not clutter the presentation of the actual PCTL calculation below. *)
(* L not equal to ... *)
lemma insert_neq: "a \<noteq> b \<Longrightarrow> a \<notin> A \<Longrightarrow> b \<notin> A \<Longrightarrow> insert a A \<noteq> insert b A"
by blast

lemma L_neq_La: "QKD_L \<noteq> QKD_La"
apply (simp add: QKD_L_def QKD_La_def QKD4_def QKD4a_def QKD3_def QKD3a_def QKD2_def QKD2a_def
                    QKD1_def QKD1a_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+

lemma L_neq_Lb: "QKD_L \<noteq> QKD_Lb"
apply (simp add: QKD_L_def QKD_Lb_def QKD4_def QKD4b_def QKD3_def QKD3b_def QKD2_def QKD2b_def
                    QKD1_def QKD1b_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+

lemma L_neq_Lc: "QKD_L \<noteq> QKD_Lc"
apply (simp add: QKD_L_def QKD_Lc_def QKD4_def QKD4c_def QKD3_def QKD3c_def QKD2_def QKD2c_def
                    QKD1_def QKD1c_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma L_neq_Ld: "QKD_L \<noteq> QKD_Ld"
apply (simp add: QKD_L_def QKD_Ld_def QKD4_def QKD4d_def QKD3_def QKD3d_def QKD2_def QKD2d_def
                    QKD1_def QKD1d_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma L_neq_Le: "QKD_L \<noteq> QKD_Le"
apply (simp add: QKD_L_def QKD_Le_def QKD4_def QKD4e_def QKD3_def QKD3e_def QKD2_def QKD2e_def
                    QKD1_def QKD1e_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma L_neq_Lf: "QKD_L \<noteq> QKD_Lf"
apply (simp add: QKD_L_def QKD_Lf_def QKD4_def QKD4f_def QKD3_def QKD3f_def QKD2_def QKD2f_def
                    QKD1_def QKD1f_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+

lemma L_neq_Lg: "QKD_L \<noteq> QKD_Lg"
apply (simp add: QKD_L_def QKD_Lg_def QKD4_def QKD4g_def QKD3_def QKD3g_def QKD2_def QKD2g_def
                    QKD1_def QKD1g_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+

(* La *)
lemma La_neq_Lb: "QKD_La \<noteq> QKD_Lb"
apply (simp add: QKD_La_def QKD_Lb_def QKD4a_def QKD4b_def QKD3a_def QKD3b_def QKD2a_def QKD2b_def
                     QKD1a_def QKD1b_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+

lemma La_neq_Lc: "QKD_La \<noteq> QKD_Lc"
apply (simp add: QKD_La_def QKD_Lc_def QKD4a_def QKD4c_def QKD3a_def QKD3c_def QKD2a_def QKD2c_def
                    QKD1a_def QKD1c_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma La_neq_Ld: "QKD_La \<noteq> QKD_Ld"
apply (simp add: QKD_La_def QKD_Ld_def QKD4a_def QKD4d_def QKD3a_def QKD3d_def QKD2a_def QKD2d_def
                    QKD1a_def QKD1d_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma La_neq_Le: "QKD_La \<noteq> QKD_Le"
apply (simp add: QKD_La_def QKD_Le_def QKD4a_def QKD4e_def QKD3a_def QKD3e_def QKD2a_def QKD2e_def
                    QKD1a_def QKD1e_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma La_neq_Lf: "QKD_La \<noteq> QKD_Lf"
apply (simp add: QKD_La_def QKD_Lf_def QKD4a_def QKD4f_def QKD3a_def QKD3f_def QKD2a_def QKD2f_def
                    QKD1a_def QKD1f_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+

lemma La_neq_Lg: "QKD_La \<noteq> QKD_Lg"
apply (simp add: QKD_La_def QKD_Lg_def QKD4a_def QKD4g_def QKD3a_def QKD3g_def QKD2a_def QKD2g_def
                    QKD1a_def QKD1g_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


(* Lb *)

lemma Lb_neq_Lc: "QKD_Lb \<noteq> QKD_Lc"
apply (simp add: QKD_Lb_def QKD_Lc_def QKD4b_def QKD4c_def QKD3b_def QKD3c_def QKD2b_def QKD2c_def
                    QKD1b_def QKD1c_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma Lb_neq_Ld: "QKD_Lb \<noteq> QKD_Ld"
apply (simp add: QKD_Lb_def QKD_Ld_def QKD4b_def QKD4d_def QKD3b_def QKD3d_def QKD2_def QKD2d_def
                    QKD1b_def QKD1d_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma Lb_neq_Le: "QKD_Lb \<noteq> QKD_Le"
apply (simp add: QKD_Lb_def QKD_Le_def QKD4b_def QKD4e_def QKD3b_def QKD3e_def QKD2b_def QKD2e_def
                    QKD1b_def QKD1e_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma Lb_neq_Lf: "QKD_Lb \<noteq> QKD_Lf"
apply (simp add: QKD_Lb_def QKD_Lf_def QKD4b_def QKD4f_def QKD3b_def QKD3f_def QKD2b_def QKD2f_def
                    QKD1b_def QKD1f_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+

lemma Lb_neq_Lg: "QKD_Lb \<noteq> QKD_Lg"
apply (simp add: QKD_Lb_def QKD_Lg_def QKD4b_def QKD4g_def QKD3b_def QKD3g_def QKD2b_def QKD2g_def
                    QKD1b_def QKD1g_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


(* Lc *)

lemma Lc_neq_Ld: "QKD_Lc \<noteq> QKD_Ld"
apply (simp add: QKD_Lc_def QKD_Ld_def QKD4c_def QKD4d_def QKD3c_def QKD3d_def QKD2c_def QKD2d_def
                    QKD1c_def QKD1d_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma Lc_neq_Le: "QKD_Lc \<noteq> QKD_Le"
apply (simp add: QKD_Lc_def QKD_Le_def QKD4c_def QKD4e_def QKD3c_def QKD3e_def QKD2c_def QKD2e_def
                    QKD1c_def QKD1e_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma Lc_neq_Lf: "QKD_Lc \<noteq> QKD_Lf"
apply (simp add: QKD_Lc_def QKD_Lf_def QKD4c_def QKD4f_def QKD3c_def QKD3f_def QKD2c_def QKD2f_def
                    QKD1c_def QKD1f_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+

lemma Lc_neq_Lg: "QKD_Lc \<noteq> QKD_Lg"
apply (simp add: QKD_Lc_def QKD_Lg_def QKD4c_def QKD4g_def QKD3c_def QKD3g_def QKD2c_def QKD2g_def
                    QKD1c_def QKD1g_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


(* Ld *)
lemma Ld_neq_Le: "QKD_Ld \<noteq> QKD_Le"
apply (simp add: QKD_Ld_def QKD_Le_def QKD4d_def QKD4e_def QKD3d_def QKD3e_def QKD2d_def QKD2e_def
                    QKD1d_def QKD1e_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma Ld_neq_Lf: "QKD_Ld \<noteq> QKD_Lf"
apply (simp add: QKD_Ld_def QKD_Lf_def QKD4d_def QKD4f_def QKD3d_def QKD3f_def QKD2d_def QKD2f_def
                    QKD1d_def QKD1f_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+

lemma Ld_neq_Lg: "QKD_Ld \<noteq> QKD_Lg"
apply (simp add: QKD_Ld_def QKD_Lg_def QKD4d_def QKD4g_def QKD3d_def QKD3g_def QKD2d_def QKD2g_def
                    QKD1d_def QKD1g_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+

(* Le *)

lemma Le_neq_Lf: "QKD_Le \<noteq> QKD_Lf"
apply (simp add: QKD_Le_def QKD_Lf_def QKD4e_def QKD4f_def QKD3e_def QKD3f_def QKD2e_def QKD2f_def
                    QKD1e_def QKD1f_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+

lemma Le_neq_Lg: "QKD_Le \<noteq> QKD_Lg"
apply (simp add: QKD_Le_def QKD_Lg_def QKD4e_def QKD4g_def QKD3e_def QKD3g_def QKD2e_def QKD2g_def
                    QKD1e_def QKD1g_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+

(* Lf *)
lemma Lf_neq_Lg: "QKD_Lf \<noteq> QKD_Lg"
apply (simp add: QKD_Lf_def QKD_Lg_def QKD4f_def QKD4g_def QKD3f_def QKD3g_def QKD2f_def QKD2g_def
                    QKD1f_def QKD1g_def qkd_scenario_def insertp_def the_prot_def)
  apply (rule impI)+
  apply (rule insert_neq)
by simp+


lemma Lf_nin_Lg: "QKD_Lf \<notin> {QKD_Lg}"
by (simp add: Lf_neq_Lg)

(* main QKD result: PCTL formula that shows that changes for Eve to get the tight key are 3/4 *)
lemma qkd_eval_step2a: "(fsumap qkd_ops''') {QKD_L, QKD_La, QKD_Lb, QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg} = 3/4"
proof -
  show "fsumap qkd_ops''' {QKD_L, QKD_La, QKD_Lb, QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg} =
    (3::real) / (4::real)"
  proof -
    have a: "fsumap qkd_ops''' {QKD_L, QKD_La, QKD_Lb, QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg} =
             qkd_ops''' QKD_L + qkd_ops''' QKD_La + qkd_ops''' QKD_Lb + qkd_ops''' QKD_Lc + 
              qkd_ops''' QKD_Ld + qkd_ops''' QKD_Le + qkd_ops''' QKD_Lf + qkd_ops''' QKD_Lg"
      apply (subgoal_tac "QKD_L \<notin> {QKD_La, QKD_Lb, QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg}") 
       apply (simp add: fsumap_fold_one fsumap_lem)
      apply (subgoal_tac "QKD_La \<notin> {QKD_Lb, QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg}") 
        apply (simp add: fsumap_fold_one fsumap_lem)
        apply (subgoal_tac "QKD_Lb \<notin> {QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg}") 
         apply (simp add: fsumap_fold_one fsumap_lem)
        apply (subgoal_tac "QKD_Lc \<notin> {QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg}") 
          apply (simp add: fsumap_fold_one fsumap_lem)
          apply (subgoal_tac "QKD_Lc \<notin> {QKD_Le, QKD_Lf, QKD_Lg}") 
           apply (simp add: fsumap_fold_one fsumap_lem)
            apply (subgoal_tac "QKD_Ld \<notin> {QKD_Le, QKD_Lf, QKD_Lg}") 
            apply (simp add: fsumap_fold_one fsumap_lem)
            apply (subgoal_tac "QKD_Le \<notin> {QKD_Lf, QKD_Lg}") 
             apply (simp add: fsumap_fold_one fsumap_lem)
             apply (subgoal_tac "QKD_Lf \<notin> {QKD_Lg}") 
             apply (simp add: fsumap_fold_one fsumap_lem)
              apply (simp add: fsumap_def)
             apply (rule Lf_nin_Lg)
            apply (simp add: Ld_neq_Le Le_neq_Lf Le_neq_Lg)
           apply (simp add: Ld_neq_Le Ld_neq_Lf Ld_neq_Lg Le_neq_Lf Le_neq_Lg)
          apply (simp add: Lc_neq_Le)
         apply (simp add: Lc_neq_Ld  Lc_neq_Le  Lc_neq_Lf  Lc_neq_Lg)
        apply (simp add: Lb_neq_Lc Lb_neq_Ld Lb_neq_Le Lb_neq_Lf Lb_neq_Lg)
       apply (simp add: La_neq_Lb La_neq_Lc La_neq_Ld La_neq_Le La_neq_Lf La_neq_Lg)
      by (simp add: L_neq_La L_neq_Lb L_neq_Lc L_neq_Ld L_neq_Le L_neq_Lf L_neq_Lg)
        moreover have b1: "qkd_ops''' QKD_L = 1/8" 
      apply (simp add: qkd_ops'''_def qkd_ops''_def qkd_ops'_def QKD_L_def fsum_def the_prot_def
             QKD1_def QKD2_def QKD3_def QKD4_def insertp_def qkd_scenario_def fmap_lem fmap_lem_one)
      by (simp add: fold_one_plus fold_two_plus)
    moreover have b2: "qkd_ops''' QKD_La = 1/16" 
      apply (simp add: qkd_ops'''_def qkd_ops''_def qkd_ops'_def QKD_La_def fsum_def the_prot_def
             QKD1a_def QKD2a_def QKD3a_def QKD4a_def insertp_def qkd_scenario_def fmap_lem fmap_lem_one)
      by (simp add: fold_one_plus fold_two_plus)
    moreover have b3: "qkd_ops''' QKD_Lb = 1/16" 
       apply (simp add: qkd_ops'''_def qkd_ops''_def qkd_ops'_def QKD_Lb_def fsum_def the_prot_def
             QKD1b_def QKD2b_def QKD3b_def QKD4b_def insertp_def qkd_scenario_def fmap_lem fmap_lem_one)
      by (simp add: fold_one_plus fold_two_plus)
    moreover have b4: "qkd_ops''' QKD_Lc = 1/16" 
      apply (simp add: qkd_ops'''_def qkd_ops''_def qkd_ops'_def QKD_Lc_def fsum_def the_prot_def
             QKD1c_def QKD2c_def QKD3c_def QKD4c_def insertp_def qkd_scenario_def fmap_lem fmap_lem_one)
      by (simp add: fold_one_plus fold_two_plus)
    moreover have b5: "qkd_ops''' QKD_Ld = 1/16" 
        apply (simp add: qkd_ops'''_def qkd_ops''_def qkd_ops'_def QKD_Ld_def fsum_def the_prot_def
             QKD1d_def QKD2d_def QKD3d_def QKD4d_def insertp_def qkd_scenario_def fmap_lem fmap_lem_one)
      by (simp add: fold_one_plus fold_two_plus)
    moreover have b6: "qkd_ops''' QKD_Le = 1/8"  
        apply (simp add: qkd_ops'''_def qkd_ops''_def qkd_ops'_def QKD_Le_def fsum_def the_prot_def
             QKD1e_def QKD2e_def QKD3e_def QKD4e_def insertp_def qkd_scenario_def fmap_lem fmap_lem_one)
      by (simp add: fold_one_plus fold_two_plus)
    moreover have b7: "qkd_ops''' QKD_Lf = 1/8" 
          apply (simp add: qkd_ops'''_def qkd_ops''_def qkd_ops'_def QKD_Lf_def fsum_def the_prot_def
             QKD1f_def QKD2f_def QKD3f_def QKD4f_def insertp_def qkd_scenario_def fmap_lem fmap_lem_one)
      by (simp add: fold_one_plus fold_two_plus)
    moreover have b8: "qkd_ops''' QKD_Lg = 1/8" 
            apply (simp add: qkd_ops'''_def qkd_ops''_def qkd_ops'_def QKD_Lg_def fsum_def the_prot_def
             QKD1g_def QKD2g_def QKD3g_def QKD4g_def insertp_def qkd_scenario_def fmap_lem fmap_lem_one)
      by (simp add: fold_one_plus fold_two_plus)
    moreover have c: "qkd_ops''' QKD_L + qkd_ops''' QKD_La + qkd_ops''' QKD_Lb + qkd_ops''' QKD_Lc +
              qkd_ops''' QKD_Ld + qkd_ops''' QKD_Le + qkd_ops''' QKD_Lf + qkd_ops''' QKD_Lg =
                      1/8 + 1/16 + 1/16 + 1/16 + 1/16 + 1/8 + 1/8 + 1/8"
      by (simp add: lsum_def b1 b2 b3 b4 b5 b6 b7 b8) 
    ultimately show "fsumap qkd_ops''' {QKD_L, QKD_La, QKD_Lb, QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg} =
    (3::real) / (4::real)"
      apply (subst a)
      apply (subst c)
      by arith
  qed
qed


lemma qkd_eval_step2: "J (fsumap qkd_ops''' {QKD_L, QKD_La, QKD_Lb, QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg})"
proof (subst qkd_eval_step2a)
  show "J ((3::real) / (4::real))" by (simp add: J_def)
qed

lemma qkd_Eve_attack: "qkd_Kripke ((fsumap qkd_ops''')::(protocol list set \<Rightarrow> real)) \<turnstile>PF\<^sub>J negated_policy"
proof (unfold probF_def)
  show "J ((fsumap qkd_ops''') (qkd_Kripke \<turnstile>F negated_policy))"
  proof -
    have a: "qkd_Kripke \<turnstile>F negated_policy = {QKD_L, QKD_La, QKD_Lb, QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg}"
      by (rule qkd_eval_step1)
    moreover have b:
    "J ((fsumap qkd_ops''') {QKD_L, QKD_La, QKD_Lb, QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg})"
      by (rule qkd_eval_step2)
    ultimately show "J ((fsumap qkd_ops''') (qkd_Kripke \<turnstile>F negated_policy))" 
      by (subst a)
  qed
qed


end