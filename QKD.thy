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
                 hd(tl (tl l)) = AsOne b' \<Longrightarrow> evs \<rightarrow>\<^sub>Q insertp (BmOne b' # l) evs"
| BmeasuresNOK: "l \<in> evs \<Longrightarrow>  hd l = BchX b \<Longrightarrow> hd(tl l) = AchX b' \<Longrightarrow>
                 b \<noteq> b' \<Longrightarrow> evs \<rightarrow>\<^sub>Q insertp (BmOne b'' # l) evs"
| EchosesPolX: "l \<in> evs \<Longrightarrow> hd l = AchX b \<Longrightarrow>
                evs \<rightarrow>\<^sub>Q insertp (EchX b' # l) evs"
| EintercptOK: "l \<in> evs \<Longrightarrow> hd l = EchX b \<Longrightarrow> hd(tl l) = AchX b \<Longrightarrow>
                hd(tl (tl l)) = AsOne b' \<Longrightarrow> evs \<rightarrow>\<^sub>Q insertp (EmOne b' # l) evs"
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

lemma step0R: "qkd_scenario \<rightarrow>\<^sub>Q* QKD1"
proof (simp add: state_transition_qkd_refl_def)
  show "(qkd_scenario, QKD1) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step0, auto)
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
next show "hd (tl (tl [EchX True, AchX True, AsOne True])) = AsOne True" by simp
qed

lemma step3R: "QKD3 \<rightarrow>\<^sub>Q* QKD4"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD3, QKD4) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step3, auto)
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

(* same for QKDxa, QKDxb, ...*)
(* step relation for QKDxa *)
lemma step0a: "qkd_scenario \<rightarrow>\<^sub>Q QKD1a"
proof (unfold qkd_scenario_def QKD1a_def)
  show "Protocol {[]}  \<rightarrow>\<^sub>Q insertp [AsOne True] (Protocol {[]})"
    apply (insert AsendsBitb)
    apply (drule_tac x = "Protocol {[]}" in meta_spec)
    apply (drule_tac x = True in meta_spec)
    apply (simp add: insertp_def)
    apply (erule meta_mp)
by (simp add: prot_mem_def)
qed

lemma step0aR: "qkd_scenario \<rightarrow>\<^sub>Q* QKD1a"
proof (simp add: state_transition_qkd_refl_def)
  show "(qkd_scenario, QKD1a) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step0a, auto)
qed

lemma step1a: "QKD1a \<rightarrow>\<^sub>Q QKD2a"
proof (unfold QKD1a_def QKD2a_def, rule_tac l = "[AsOne True]" and b = True in AchosesPolX) 
  show "[AsOne True] \<in>  insertp [AsOne True] qkd_scenario" by (simp add: insertp_def prot_mem_def)
next show "hd [AsOne True] = AsOne True" by simp
qed

lemma step1aR: "QKD1a \<rightarrow>\<^sub>Q* QKD2a"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD1a, QKD2a) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step1a, auto)
qed

lemma step2a: "QKD2a \<rightarrow>\<^sub>Q QKD3a"
proof (unfold QKD2a_def QKD3a_def, rule_tac l = "[AchX False, AsOne True]" and 
          b = False and b' = True in EchosesPolX)
  show "[AchX False, AsOne True] \<in> insertp [AchX False, AsOne True] QKD1a"
    by (simp add: insertp_def prot_mem_def)+
next show "hd [AchX False, AsOne True] = AchX False" by simp
qed

lemma step2aR: "QKD2a \<rightarrow>\<^sub>Q* QKD3a"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD2a, QKD3a) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step2a, auto)
qed

lemma step3a: "QKD3a \<rightarrow>\<^sub>Q QKD4a"
proof (unfold QKD3a_def QKD4a_def, rule_tac l = "[EchX True, AchX False, AsOne True]" and 
          b = True and b' = False in EintrcptNOK)
  show "[EchX True, AchX False, AsOne True] \<in> insertp [EchX True, AchX False, AsOne True] QKD2a"
    by (simp add: insertp_def prot_mem_def)
next show "hd [EchX True, AchX False, AsOne True] = EchX True" by simp
next show "hd (tl [EchX True, AchX False, AsOne True]) = AchX False" by simp
next show "True \<noteq> False" by simp
qed

lemma step3aR: "QKD3a \<rightarrow>\<^sub>Q* QKD4a"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD3a, QKD4a) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step3a, auto)
qed

(* QKD4a violates global policy *)
lemma QKD4a_bad: "\<not> global_policy QKD4a"
proof (simp add: QKD4a_def global_policy_def)
  show "\<exists>l::event list.
       l \<in> insertp [EmOne True, EchX True, AchX False, AsOne True] QKD3a \<and>
       (\<exists>b::bool. AsOne b \<in> set l \<and> EmOne b \<in> set l)"
    apply (rule_tac x = "[EmOne True, EchX True, AchX False, AsOne True]" in exI)
    apply (rule conjI)
     apply (simp add: insertp_def prot_mem_def)
    apply (rule_tac x = True in exI)
    by simp
qed

(* step relation for QKDxb *)
lemma step0b: "qkd_scenario \<rightarrow>\<^sub>Q QKD1b"
proof (unfold qkd_scenario_def QKD1b_def)
  show "Protocol {[]}  \<rightarrow>\<^sub>Q insertp [AsOne False] (Protocol {[]})"
    apply (insert AsendsBitb)
    apply (drule_tac x = "Protocol {[]}" in meta_spec)
    apply (drule_tac x = False in meta_spec)
    apply (simp add: insertp_def)
    apply (erule meta_mp)
by (simp add: prot_mem_def)
qed

lemma step0bR: "qkd_scenario \<rightarrow>\<^sub>Q* QKD1b"
proof (simp add: state_transition_qkd_refl_def)
  show "(qkd_scenario, QKD1b) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step0b, auto)
qed

lemma step1b: "QKD1b \<rightarrow>\<^sub>Q QKD2b"
proof (unfold QKD1b_def QKD2b_def, rule_tac l = "[AsOne False]" and b = False in AchosesPolX) 
  show "[AsOne False] \<in>  insertp [AsOne False] qkd_scenario" by (simp add: insertp_def prot_mem_def)
next show "hd [AsOne False] = AsOne False" by simp
qed

lemma step1bR: "QKD1b \<rightarrow>\<^sub>Q* QKD2b"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD1b, QKD2b) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step1b, auto)
qed

lemma step2b: "QKD2b \<rightarrow>\<^sub>Q QKD3b"
proof (unfold QKD2b_def QKD3b_def, rule_tac l = "[AchX False, AsOne False]" and 
          b = False and b' = True in EchosesPolX)
  show "[AchX False, AsOne False] \<in> insertp [AchX False, AsOne False] QKD1b"
    by (simp add: insertp_def prot_mem_def)+
next show "hd [AchX False, AsOne False] = AchX False" by simp
qed

lemma step2bR: "QKD2b \<rightarrow>\<^sub>Q* QKD3b"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD2b, QKD3b) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step2b, auto)
qed

lemma step3b: "QKD3b \<rightarrow>\<^sub>Q QKD4b"
proof (unfold QKD3b_def QKD4b_def, rule_tac l = "[EchX True, AchX False, AsOne False]" and 
          b = True and b' = False in EintrcptNOK)
  show "[EchX True, AchX False, AsOne False] \<in> insertp [EchX True, AchX False, AsOne False] QKD2b"
    by (simp add: insertp_def prot_mem_def)
next show "hd [EchX True, AchX False, AsOne False] = EchX True" by simp
next show "hd (tl [EchX True, AchX False, AsOne False]) = AchX False" by simp
next show "True \<noteq> False" by simp
qed

lemma step3bR: "QKD3b \<rightarrow>\<^sub>Q* QKD4b"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD3b, QKD4b) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step3b, auto)
qed

(* QKD4b violates global policy *)
lemma QKD4b_bad: "\<not> global_policy QKD4b"
proof (simp add: QKD4b_def global_policy_def)
  show "\<exists>l::event list.
       l \<in> insertp [EmOne False, EchX True, AchX False, AsOne False] QKD3b \<and>
       (\<exists>b::bool. AsOne b \<in> set l \<and> EmOne b \<in> set l)"
    apply (rule_tac x = "[EmOne False, EchX True, AchX False, AsOne False]" in exI)
    apply (rule conjI)
     apply (simp add: insertp_def prot_mem_def)
    apply (rule_tac x = False in exI)
    by simp
qed

(* step relation for QKDxc *)
lemma step0c: "qkd_scenario \<rightarrow>\<^sub>Q QKD1c"
proof (unfold qkd_scenario_def QKD1c_def)
  show "Protocol {[]}  \<rightarrow>\<^sub>Q insertp [AsOne True] (Protocol {[]})"
    apply (insert AsendsBitb)
    apply (drule_tac x = "Protocol {[]}" in meta_spec)
    apply (drule_tac x = True in meta_spec)
    apply (simp add: insertp_def)
    apply (erule meta_mp)
by (simp add: prot_mem_def)
qed

lemma step0cR: "qkd_scenario \<rightarrow>\<^sub>Q* QKD1c"
proof (simp add: state_transition_qkd_refl_def)
  show "(qkd_scenario, QKD1c) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step0c, auto)
qed

lemma step1c: "QKD1c \<rightarrow>\<^sub>Q QKD2c"
proof (unfold QKD1c_def QKD2c_def, rule_tac l = "[AsOne True]" and b = True in AchosesPolX) 
  show "[AsOne True] \<in>  insertp [AsOne True] qkd_scenario" by (simp add: insertp_def prot_mem_def)
next show "hd [AsOne True] = AsOne True" by simp
qed

lemma step1cR: "QKD1c \<rightarrow>\<^sub>Q* QKD2c"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD1c, QKD2c) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step1c, auto)
qed

lemma step2c: "QKD2c \<rightarrow>\<^sub>Q QKD3c"
proof (unfold QKD2c_def QKD3c_def, rule_tac l = "[AchX True, AsOne True]" and 
          b = True and b' = False in EchosesPolX)
  show "[AchX True, AsOne True] \<in> insertp [AchX True, AsOne True] QKD1c"
    by (simp add: insertp_def prot_mem_def)+
next show "hd [AchX True, AsOne True] = AchX True" by simp
qed

lemma step2cR: "QKD2c \<rightarrow>\<^sub>Q* QKD3c"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD2c, QKD3c) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step2c, auto)
qed

lemma step3c: "QKD3c \<rightarrow>\<^sub>Q QKD4c"
proof (unfold QKD3c_def QKD4c_def, rule_tac l = "[EchX False, AchX True, AsOne True]" and 
          b = False and b' = True in EintrcptNOK)
  show "[EchX False, AchX True, AsOne True] \<in> insertp [EchX False, AchX True, AsOne True] QKD2c"
    by (simp add: insertp_def prot_mem_def)
next show "hd [EchX False, AchX True, AsOne True] = EchX False" by simp
next show "hd (tl [EchX False, AchX True, AsOne True]) = AchX True" by simp
next show "False \<noteq> True" by simp
qed

lemma step3cR: "QKD3c \<rightarrow>\<^sub>Q* QKD4c"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD3c, QKD4c) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step3c, auto)
qed

(* QKD4c violates global policy *)
lemma QKD4c_bad: "\<not> global_policy QKD4c"
proof (simp add: QKD4c_def global_policy_def)
  show "\<exists>l::event list.
       l \<in> insertp [EmOne True, EchX False, AchX True, AsOne True] QKD3c \<and>
       (\<exists>b::bool. AsOne b \<in> set l \<and> EmOne b \<in> set l)"
    apply (rule_tac x = "[EmOne True, EchX False, AchX True, AsOne True]" in exI)
    apply (rule conjI)
     apply (simp add: insertp_def prot_mem_def)
    apply (rule_tac x = True in exI)
    by simp
qed

(* step relation for QKDxd *)
lemma step0d: "qkd_scenario \<rightarrow>\<^sub>Q QKD1d"
proof (unfold qkd_scenario_def QKD1d_def)
  show "Protocol {[]}  \<rightarrow>\<^sub>Q insertp [AsOne False] (Protocol {[]})"
    apply (insert AsendsBitb)
    apply (drule_tac x = "Protocol {[]}" in meta_spec)
    apply (drule_tac x = False in meta_spec)
    apply (simp add: insertp_def)
    apply (erule meta_mp)
by (simp add: prot_mem_def)
qed

lemma step0dR: "qkd_scenario \<rightarrow>\<^sub>Q* QKD1d"
proof (simp add: state_transition_qkd_refl_def)
  show "(qkd_scenario, QKD1d) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step0d, auto)
qed

lemma step1d: "QKD1d \<rightarrow>\<^sub>Q QKD2d"
proof (unfold QKD1d_def QKD2d_def, rule_tac l = "[AsOne False]" and b = False in AchosesPolX) 
  show "[AsOne False] \<in>  insertp [AsOne False] qkd_scenario" by (simp add: insertp_def prot_mem_def)
next show "hd [AsOne False] = AsOne False" by simp
qed

lemma step1dR: "QKD1d \<rightarrow>\<^sub>Q* QKD2d"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD1d, QKD2d) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step1d, auto)
qed

lemma step2d: "QKD2d \<rightarrow>\<^sub>Q QKD3d"
proof (unfold QKD2d_def QKD3d_def, rule_tac l = "[AchX True, AsOne False]" and 
          b = True and b' = False in EchosesPolX)
  show "[AchX True, AsOne False] \<in> insertp [AchX True, AsOne False] QKD1d"
    by (simp add: insertp_def prot_mem_def)+
next show "hd [AchX True, AsOne False] = AchX True" by simp
qed

lemma step2dR: "QKD2d \<rightarrow>\<^sub>Q* QKD3d"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD2d, QKD3d) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step2d, auto)
qed

lemma step3d: "QKD3d \<rightarrow>\<^sub>Q QKD4d"
proof (unfold QKD3d_def QKD4d_def, rule_tac l = "[EchX False, AchX True, AsOne False]" and 
          b = False and b' = True in EintrcptNOK)
  show "[EchX False, AchX True, AsOne False] \<in> insertp [EchX False, AchX True, AsOne False] QKD2d"
    by (simp add: insertp_def prot_mem_def)
next show "hd [EchX False, AchX True, AsOne False] = EchX False" by simp
next show "hd (tl [EchX False, AchX True, AsOne False]) = AchX True" by simp
next show "False \<noteq> True" by simp
qed

lemma step3dR: "QKD3d \<rightarrow>\<^sub>Q* QKD4d"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD3d, QKD4d) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step3d, auto)
qed

(* QKD4d violates global policy *)
lemma QKD4d_bad: "\<not> global_policy QKD4d"
proof (simp add: QKD4d_def global_policy_def)
  show "\<exists>l::event list.
       l \<in> insertp [EmOne False, EchX False, AchX True, AsOne False] QKD3d \<and>
       (\<exists>b::bool. AsOne b \<in> set l \<and> EmOne b \<in> set l)"
    apply (rule_tac x = "[EmOne False, EchX False, AchX True, AsOne False]" in exI)
    apply (rule conjI)
     apply (simp add: insertp_def prot_mem_def)
    apply (rule_tac x = False in exI)
    by simp
qed

(* step relation for QKDxd *)
lemma step0e: "qkd_scenario \<rightarrow>\<^sub>Q QKD1e"
proof (unfold qkd_scenario_def QKD1e_def)
  show "Protocol {[]}  \<rightarrow>\<^sub>Q insertp [AsOne False] (Protocol {[]})"
    apply (insert AsendsBitb)
    apply (drule_tac x = "Protocol {[]}" in meta_spec)
    apply (drule_tac x = False in meta_spec)
    apply (simp add: insertp_def)
    apply (erule meta_mp)
by (simp add: prot_mem_def)
qed

lemma step0eR: "qkd_scenario \<rightarrow>\<^sub>Q* QKD1e"
proof (simp add: state_transition_qkd_refl_def)
  show "(qkd_scenario, QKD1e) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step0e, auto)
qed

lemma step1e: "QKD1e \<rightarrow>\<^sub>Q QKD2e"
proof (unfold QKD1e_def QKD2e_def, rule_tac l = "[AsOne False]" and b = False in AchosesPolX) 
  show "[AsOne False] \<in>  insertp [AsOne False] qkd_scenario" by (simp add: insertp_def prot_mem_def)
next show "hd [AsOne False] = AsOne False" by simp
qed

lemma step1eR: "QKD1e \<rightarrow>\<^sub>Q* QKD2e"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD1e, QKD2e) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step1e, auto)
qed

lemma step2e: "QKD2e \<rightarrow>\<^sub>Q QKD3e"
proof (unfold QKD2e_def QKD3e_def, rule_tac l = "[AchX True, AsOne False]" and 
          b = True and b' = True in EchosesPolX)
  show "[AchX True, AsOne False] \<in> insertp [AchX True, AsOne False] QKD1e"
    by (simp add: insertp_def prot_mem_def)+
next show "hd [AchX True, AsOne False] = AchX True" by simp
qed

lemma step2eR: "QKD2e \<rightarrow>\<^sub>Q* QKD3e"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD2e, QKD3e) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step2e, auto)
qed

lemma step3e: "QKD3e \<rightarrow>\<^sub>Q QKD4e"
proof (unfold QKD3e_def QKD4e_def, rule_tac l = "[EchX True, AchX True, AsOne False]" and 
          b = True in EintercptOK)
  show "[EchX True, AchX True, AsOne False] \<in> insertp [EchX True, AchX True, AsOne False] QKD2e"
    by (simp add: insertp_def prot_mem_def)
next show "hd [EchX True, AchX True, AsOne False] = EchX True" by simp
next show "hd (tl [EchX True, AchX True, AsOne False]) = AchX True" by simp
next show "hd (tl (tl [EchX True, AchX True, AsOne False])) = AsOne False" by simp
qed

lemma step3eR: "QKD3e \<rightarrow>\<^sub>Q* QKD4e"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD3e, QKD4e) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step3e, auto)
qed

(* QKD4d violates global policy *)
lemma QKD4e_bad: "\<not> global_policy QKD4e"
proof (simp add: QKD4e_def global_policy_def)
  show "\<exists>l::event list.
       l \<in> insertp [EmOne False, EchX True, AchX True, AsOne False] QKD3e \<and>
       (\<exists>b::bool. AsOne b \<in> set l \<and> EmOne b \<in> set l)"
    apply (rule_tac x = "[EmOne False, EchX True, AchX True, AsOne False]" in exI)
    apply (rule conjI)
     apply (simp add: insertp_def prot_mem_def)
    apply (rule_tac x = False in exI)
    by simp
qed


(* step relation for QKDxf *)
lemma step0f: "qkd_scenario \<rightarrow>\<^sub>Q QKD1f"
proof (unfold qkd_scenario_def QKD1f_def)
  show "Protocol {[]}  \<rightarrow>\<^sub>Q insertp [AsOne True] (Protocol {[]})"
    apply (insert AsendsBitb)
    apply (drule_tac x = "Protocol {[]}" in meta_spec)
    apply (drule_tac x = True in meta_spec)
    apply (simp add: insertp_def)
    apply (erule meta_mp)
by (simp add: prot_mem_def)
qed

lemma step0fR: "qkd_scenario \<rightarrow>\<^sub>Q* QKD1f"
proof (simp add: state_transition_qkd_refl_def)
  show "(qkd_scenario, QKD1f) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step0f, auto)
qed

lemma step1f: "QKD1f \<rightarrow>\<^sub>Q QKD2f"
proof (unfold QKD1f_def QKD2f_def, rule_tac l = "[AsOne True]" and b = True in AchosesPolX) 
  show "[AsOne True] \<in>  insertp [AsOne True] qkd_scenario" by (simp add: insertp_def prot_mem_def)
next show "hd [AsOne True] = AsOne True" by simp
qed

lemma step1fR: "QKD1f \<rightarrow>\<^sub>Q* QKD2f"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD1f, QKD2f) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step1f, auto)
qed

lemma step2f: "QKD2f \<rightarrow>\<^sub>Q QKD3f"
proof (unfold QKD2f_def QKD3f_def, rule_tac l = "[AchX False, AsOne True]" and 
          b = False and b' = False in EchosesPolX)
  show "[AchX False, AsOne True] \<in> insertp [AchX False, AsOne True] QKD1f"
    by (simp add: insertp_def prot_mem_def)+
next show "hd [AchX False, AsOne True] = AchX False" by simp
qed

lemma step2fR: "QKD2f \<rightarrow>\<^sub>Q* QKD3f"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD2f, QKD3f) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step2f, auto)
qed

lemma step3f: "QKD3f \<rightarrow>\<^sub>Q QKD4f"
proof (unfold QKD3f_def QKD4f_def, rule_tac l = "[EchX False, AchX False, AsOne True]" and 
          b = False in EintercptOK)
  show "[EchX False, AchX False, AsOne True] \<in> insertp [EchX False, AchX False, AsOne True] QKD2f"
    by (simp add: insertp_def prot_mem_def)
next show "hd [EchX False, AchX False, AsOne True] = EchX False" by simp
next show "hd (tl [EchX False, AchX False, AsOne True]) = AchX False" by simp
next show "hd (tl (tl [EchX False, AchX False, AsOne True])) = AsOne True" by simp
qed

lemma step3fR: "QKD3f \<rightarrow>\<^sub>Q* QKD4f"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD3f, QKD4f) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step3f, auto)
qed

(* QKD4f violates global policy *)
lemma QKD4f_bad: "\<not> global_policy QKD4f"
proof (simp add: QKD4f_def global_policy_def)
  show "\<exists>l::event list.
       l \<in> insertp [EmOne True, EchX False, AchX False, AsOne True] QKD3f \<and>
       (\<exists>b::bool. AsOne b \<in> set l \<and> EmOne b \<in> set l)"
    apply (rule_tac x = "[EmOne True, EchX False, AchX False, AsOne True]" in exI)
    apply (rule conjI)
     apply (simp add: insertp_def prot_mem_def)
    apply (rule_tac x = True in exI)
    by simp
qed

(* step relation for QKDxg *)
lemma step0g: "qkd_scenario \<rightarrow>\<^sub>Q QKD1g"
proof (unfold qkd_scenario_def QKD1g_def)
  show "Protocol {[]}  \<rightarrow>\<^sub>Q insertp [AsOne False] (Protocol {[]})"
    apply (insert AsendsBitb)
    apply (drule_tac x = "Protocol {[]}" in meta_spec)
    apply (drule_tac x = False in meta_spec)
    apply (simp add: insertp_def)
    apply (erule meta_mp)
by (simp add: prot_mem_def)
qed

lemma step0gR: "qkd_scenario \<rightarrow>\<^sub>Q* QKD1g"
proof (simp add: state_transition_qkd_refl_def)
  show "(qkd_scenario, QKD1g) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step0g, auto)
qed

lemma step1g: "QKD1g \<rightarrow>\<^sub>Q QKD2g"
proof (unfold QKD1g_def QKD2g_def, rule_tac l = "[AsOne False]" and b = False in AchosesPolX) 
  show "[AsOne False] \<in>  insertp [AsOne False] qkd_scenario" by (simp add: insertp_def prot_mem_def)
next show "hd [AsOne False] = AsOne False" by simp
qed

lemma step1gR: "QKD1g \<rightarrow>\<^sub>Q* QKD2g"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD1g, QKD2g) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step1g, auto)
qed

lemma step2g: "QKD2g \<rightarrow>\<^sub>Q QKD3g"
proof (unfold QKD2g_def QKD3g_def, rule_tac l = "[AchX False, AsOne False]" and 
          b = False and b' = False in EchosesPolX)
  show "[AchX False, AsOne False] \<in> insertp [AchX False, AsOne False] QKD1g"
    by (simp add: insertp_def prot_mem_def)+
next show "hd [AchX False, AsOne False] = AchX False" by simp
qed

lemma step2gR: "QKD2g \<rightarrow>\<^sub>Q* QKD3g"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD2g, QKD3g) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step2g, auto)
qed

lemma step3g: "QKD3g \<rightarrow>\<^sub>Q QKD4g"
proof (unfold QKD3g_def QKD4g_def, rule_tac l = "[EchX False, AchX False, AsOne False]" and 
          b = False in EintercptOK)
  show "[EchX False, AchX False, AsOne False] \<in> insertp [EchX False, AchX False, AsOne False] QKD2g"
    by (simp add: insertp_def prot_mem_def)
next show "hd [EchX False, AchX False, AsOne False] = EchX False" by simp
next show "hd (tl [EchX False, AchX False, AsOne False]) = AchX False" by simp
next show "hd (tl (tl [EchX False, AchX False, AsOne False])) = AsOne False" by simp
qed

lemma step3gR: "QKD3g \<rightarrow>\<^sub>Q* QKD4g"
proof (simp add: state_transition_qkd_refl_def)
  show "(QKD3g, QKD4g) \<in> {(x::protocol, y::protocol). x  \<rightarrow>\<^sub>Q y}\<^sup>* "
    by (insert step3g, auto)
qed

(* QKD4g violates global policy *)
lemma QKD4g_bad: "\<not> global_policy QKD4g"
proof (simp add: QKD4g_def global_policy_def)
  show "\<exists>l::event list.
       l \<in> insertp [EmOne False, EchX False, AchX False, AsOne False] QKD3g \<and>
       (\<exists>b::bool. AsOne b \<in> set l \<and> EmOne b \<in> set l)"
    apply (rule_tac x = "[EmOne False, EchX False, AchX False, AsOne False]" in exI)
    apply (rule conjI)
     apply (simp add: insertp_def prot_mem_def)
    apply (rule_tac x = False in exI)
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
proof (unfold eventually_def F_def, rule equalityI) 
  show "{l::protocol list. set l \<subseteq> states qkd_Kripke \<and> hd l \<in> init qkd_Kripke} \<inter>
    {l::protocol list. \<forall>i<length l - 1. l ! i \<rightarrow>\<^sub>i l ! Suc i \<and> last l \<in> negated_policy}
    \<subseteq> {QKD_L, QKD_La, QKD_Lb, QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg}"
 sorry
next show "{QKD_L, QKD_La, QKD_Lb, QKD_Lc, QKD_Ld, QKD_Le, QKD_Lf, QKD_Lg}
    \<subseteq> {l::protocol list. set l \<subseteq> states qkd_Kripke \<and> hd l \<in> init qkd_Kripke} \<inter>
       {l::protocol list. \<forall>i<length l - 1. l ! i \<rightarrow>\<^sub>i l ! Suc i \<and> last l \<in> negated_policy}"
    apply (rule subsetI)
    apply simp
  proof -
    have L: "set QKD_L \<subseteq> states qkd_Kripke \<and>
       hd QKD_L \<in> init qkd_Kripke \<and>
       (\<forall>i<length QKD_L - Suc (0::nat). QKD_L ! i \<rightarrow>\<^sub>i QKD_L ! Suc i \<and> last QKD_L \<in> negated_policy)"
      apply (rule conjI)
      (* set QKD_L \<subseteq> states qkd_Kripke  *)
       apply (simp add: QKD_L_def qkd_Kripke_def qkd_scenario_def)
       apply (rule conjI)
        apply (simp add:  state_transition_qkd_refl_def)
      apply (rule conjI)
        apply (fold qkd_scenario_def, rule step0R)
       apply (rule conjI)
      apply (insert step0R step1R, simp add: state_transition_qkd_refl_def)
       apply (rule conjI)
      apply (insert step2R, simp add: state_transition_qkd_refl_def)
      apply (insert step3R, simp add: state_transition_qkd_refl_def)
     (* hd QKD_L \<in> init qkd_Kripke *)
      apply (rule conjI)
       apply (simp add: QKD_L_def qkd_Kripke_def Iqkd_def)
     (* \<forall>i<length QKD_L. QKD_L ! i \<rightarrow>\<^sub>i QKD_L ! Suc i \<and> last QKD_L \<in> negated_policy *)
      apply (rule allI)
      apply (rule impI)
      apply (simp add: QKD_L_def negated_policy_def)
      apply (rule conjI)
      prefer 2
       apply (rule QKD4_bad)
      apply (subst state_transition_qkd_inst_def)
      apply (case_tac i)
       apply (simp add: step0)
      apply (case_tac nat)
       apply (simp add: step1)
      apply (case_tac nata)
       apply (simp add: step2)
      apply (case_tac natb)
      by (simp add: step3)+
    moreover have La: "set QKD_La \<subseteq> states qkd_Kripke \<and>
       hd QKD_La \<in> init qkd_Kripke \<and> 
       (\<forall>i<length QKD_La - Suc (0::nat). QKD_La ! i \<rightarrow>\<^sub>i QKD_La ! Suc i \<and> last QKD_La \<in> negated_policy)"
       apply (rule conjI)
      (* set QKD_La \<subseteq> states qkd_Kripke  *)
       apply (simp add: QKD_La_def qkd_Kripke_def qkd_scenario_def)
       apply (rule conjI)
        apply (simp add:  state_transition_qkd_refl_def)
      apply (rule conjI)
        apply (fold qkd_scenario_def, rule step0aR)
       apply (rule conjI)
      apply (insert step0aR step1aR, simp add: state_transition_qkd_refl_def)
       apply (rule conjI)
      apply (insert step2aR, simp add: state_transition_qkd_refl_def)
      apply (insert step3aR, simp add: state_transition_qkd_refl_def)
     (* hd QKD_L \<in> init qkd_Kripke *)
      apply (rule conjI)
       apply (simp add: QKD_La_def qkd_Kripke_def Iqkd_def)
     (* \<forall>i<length QKD_La. QKD_La ! i \<rightarrow>\<^sub>i QKD_La ! Suc i \<and> last QKD_La \<in> negated_policy *)
      apply (rule allI)
      apply (rule impI)
      apply (simp add: QKD_La_def negated_policy_def)
      apply (rule conjI)
      prefer 2
       apply (rule QKD4a_bad)
      apply (subst state_transition_qkd_inst_def)
      apply (case_tac i)
       apply (simp add: step0a)
      apply (case_tac nat)
       apply (simp add: step1a)
      apply (case_tac nata)
       apply (simp add: step2a)
      apply (case_tac natb)
      by (simp add: step3a)+      
    moreover have Lb: "set QKD_Lb \<subseteq> states qkd_Kripke \<and>
       hd QKD_Lb \<in> init qkd_Kripke \<and> 
       (\<forall>i<length QKD_Lb - Suc (0::nat). QKD_Lb ! i \<rightarrow>\<^sub>i QKD_Lb ! Suc i \<and> last QKD_Lb \<in> negated_policy)"
       apply (rule conjI)
      (* set QKD_Lb \<subseteq> states qkd_Kripke  *)
       apply (simp add: QKD_Lb_def qkd_Kripke_def qkd_scenario_def)
       apply (rule conjI)
        apply (simp add:  state_transition_qkd_refl_def)
      apply (rule conjI)
        apply (fold qkd_scenario_def, rule step0bR)
       apply (rule conjI)
      apply (insert step0bR step1bR, simp add: state_transition_qkd_refl_def)
       apply (rule conjI)
      apply (insert step2bR, simp add: state_transition_qkd_refl_def)
      apply (insert step3bR, simp add: state_transition_qkd_refl_def)
     (* hd QKD_La \<in> init qkd_Kripke *)
      apply (rule conjI)
       apply (simp add: QKD_Lb_def qkd_Kripke_def Iqkd_def)
     (* \<forall>i<length QKD_Lb. QKD_Lb ! i \<rightarrow>\<^sub>i QKD_Lb ! Suc i \<and> last QKD_Lb \<in> negated_policy *)
      apply (rule allI)
      apply (rule impI)
      apply (simp add: QKD_Lb_def negated_policy_def)
      apply (rule conjI)
      prefer 2
       apply (rule QKD4b_bad)
      apply (subst state_transition_qkd_inst_def)
      apply (case_tac i)
       apply (simp add: step0b)
      apply (case_tac nat)
       apply (simp add: step1b)
      apply (case_tac nata)
       apply (simp add: step2b)
      apply (case_tac natb)
      by (simp add: step3b)+      
    moreover have Lc: "set QKD_Lc \<subseteq> states qkd_Kripke \<and>
       hd QKD_Lc \<in> init qkd_Kripke \<and> 
       (\<forall>i<length QKD_Lc - Suc (0::nat). QKD_Lc ! i \<rightarrow>\<^sub>i QKD_Lc ! Suc i \<and> last QKD_Lc \<in> negated_policy)"
       apply (rule conjI)
      (* set QKD_Lc \<subseteq> states qkd_Kripke  *)
       apply (simp add: QKD_Lc_def qkd_Kripke_def qkd_scenario_def)
       apply (rule conjI)
        apply (simp add:  state_transition_qkd_refl_def)
      apply (rule conjI)
        apply (fold qkd_scenario_def, rule step0cR)
       apply (rule conjI)
      apply (insert step0cR step1cR, simp add: state_transition_qkd_refl_def)
       apply (rule conjI)
      apply (insert step2cR, simp add: state_transition_qkd_refl_def)
      apply (insert step3cR, simp add: state_transition_qkd_refl_def)
     (* hd QKD_Lc \<in> init qkd_Kripke *)
      apply (rule conjI)
       apply (simp add: QKD_Lc_def qkd_Kripke_def Iqkd_def)
     (* \<forall>i<length QKD_Lc. QKD_Lc ! i \<rightarrow>\<^sub>i QKD_Lc ! Suc i \<and> last QKD_Lc \<in> negated_policy *)
      apply (rule allI)
      apply (rule impI)
      apply (simp add: QKD_Lc_def negated_policy_def)
      apply (rule conjI)
      prefer 2
       apply (rule QKD4c_bad)
      apply (subst state_transition_qkd_inst_def)
      apply (case_tac i)
       apply (simp add: step0c)
      apply (case_tac nat)
       apply (simp add: step1c)
      apply (case_tac nata)
       apply (simp add: step2c)
      apply (case_tac natb)
      by (simp add: step3c)+      
    moreover have Ld: "set QKD_Ld \<subseteq> states qkd_Kripke \<and>
       hd QKD_Ld \<in> init qkd_Kripke \<and> 
       (\<forall>i<length QKD_Ld - Suc (0::nat). QKD_Ld ! i \<rightarrow>\<^sub>i QKD_Ld ! Suc i \<and> last QKD_Ld \<in> negated_policy)"
       apply (rule conjI)
      (* set QKD_Ld \<subseteq> states qkd_Kripke  *)
       apply (simp add: QKD_Ld_def qkd_Kripke_def qkd_scenario_def)
       apply (rule conjI)
        apply (simp add:  state_transition_qkd_refl_def)
      apply (rule conjI)
        apply (fold qkd_scenario_def, rule step0dR)
       apply (rule conjI)
      apply (insert step0dR step1dR, simp add: state_transition_qkd_refl_def)
       apply (rule conjI)
      apply (insert step2dR, simp add: state_transition_qkd_refl_def)
      apply (insert step3dR, simp add: state_transition_qkd_refl_def)
     (* hd QKD_Ld \<in> init qkd_Kripke *)
      apply (rule conjI)
       apply (simp add: QKD_Ld_def qkd_Kripke_def Iqkd_def)
     (* \<forall>i<length QKD_Ld. QKD_Ld ! i \<rightarrow>\<^sub>i QKD_Ld ! Suc i \<and> last QKD_Ld \<in> negated_policy *)
      apply (rule allI)
      apply (rule impI)
      apply (simp add: QKD_Ld_def negated_policy_def)
      apply (rule conjI)
      prefer 2
       apply (rule QKD4d_bad)
      apply (subst state_transition_qkd_inst_def)
      apply (case_tac i)
       apply (simp add: step0d)
      apply (case_tac nat)
       apply (simp add: step1d)
      apply (case_tac nata)
       apply (simp add: step2d)
      apply (case_tac natb)
      by (simp add: step3d)+      
    moreover have Le: "set QKD_Le \<subseteq> states qkd_Kripke \<and>
       hd QKD_Le \<in> init qkd_Kripke \<and> 
       (\<forall>i<length QKD_Le - Suc (0::nat). QKD_Le ! i \<rightarrow>\<^sub>i QKD_Le ! Suc i \<and> last QKD_Le \<in> negated_policy)"
       apply (rule conjI)
      (* set QKD_Le \<subseteq> states qkd_Kripke  *)
       apply (simp add: QKD_Le_def qkd_Kripke_def qkd_scenario_def)
       apply (rule conjI)
        apply (simp add:  state_transition_qkd_refl_def)
      apply (rule conjI)
        apply (fold qkd_scenario_def, rule step0eR)
       apply (rule conjI)
      apply (insert step0eR step1eR, simp add: state_transition_qkd_refl_def)
       apply (rule conjI)
      apply (insert step2eR, simp add: state_transition_qkd_refl_def)
      apply (insert step3eR, simp add: state_transition_qkd_refl_def)
     (* hd QKD_Le \<in> init qkd_Kripke *)
      apply (rule conjI)
       apply (simp add: QKD_Le_def qkd_Kripke_def Iqkd_def)
     (* \<forall>i<length QKD_Le. QKD_Le ! i \<rightarrow>\<^sub>i QKD_Le ! Suc i \<and> last QKD_Le \<in> negated_policy *)
      apply (rule allI)
      apply (rule impI)
      apply (simp add: QKD_Le_def negated_policy_def)
      apply (rule conjI)
      prefer 2
       apply (rule QKD4e_bad)
      apply (subst state_transition_qkd_inst_def)
      apply (case_tac i)
       apply (simp add: step0e)
      apply (case_tac nat)
       apply (simp add: step1e)
      apply (case_tac nata)
       apply (simp add: step2e)
      apply (case_tac natb)
      by (simp add: step3e)+      
    moreover have Lf: "set QKD_Lf \<subseteq> states qkd_Kripke \<and>
       hd QKD_Lf \<in> init qkd_Kripke \<and> 
       (\<forall>i<length QKD_Lf - Suc (0::nat). QKD_Lf ! i \<rightarrow>\<^sub>i QKD_Lf ! Suc i \<and> last QKD_Lf \<in> negated_policy)"
       apply (rule conjI)
      (* set QKD_Lf \<subseteq> states qkd_Kripke  *)
       apply (simp add: QKD_Lf_def qkd_Kripke_def qkd_scenario_def)
       apply (rule conjI)
        apply (simp add:  state_transition_qkd_refl_def)
      apply (rule conjI)
        apply (fold qkd_scenario_def, rule step0fR)
       apply (rule conjI)
      apply (insert step0fR step1fR, simp add: state_transition_qkd_refl_def)
       apply (rule conjI)
      apply (insert step2fR, simp add: state_transition_qkd_refl_def)
      apply (insert step3fR, simp add: state_transition_qkd_refl_def)
     (* hd QKD_Lf \<in> init qkd_Kripke *)
      apply (rule conjI)
       apply (simp add: QKD_Lf_def qkd_Kripke_def Iqkd_def)
     (* \<forall>i<length QKD_Lf. QKD_Lf ! i \<rightarrow>\<^sub>i QKD_Lf ! Suc i \<and> last QKD_Lf \<in> negated_policy *)
      apply (rule allI)
      apply (rule impI)
      apply (simp add: QKD_Lf_def negated_policy_def)
      apply (rule conjI)
      prefer 2
       apply (rule QKD4f_bad)
      apply (subst state_transition_qkd_inst_def)
      apply (case_tac i)
       apply (simp add: step0f)
      apply (case_tac nat)
       apply (simp add: step1f)
      apply (case_tac nata)
       apply (simp add: step2f)
      apply (case_tac natb)
      by (simp add: step3f)+      
    moreover have Lg: "set QKD_Lg \<subseteq> states qkd_Kripke \<and>
       hd QKD_Lg \<in> init qkd_Kripke \<and> 
       (\<forall>i<length QKD_Lg - Suc (0::nat). QKD_Lg ! i \<rightarrow>\<^sub>i QKD_Lg ! Suc i \<and> last QKD_Lg \<in> negated_policy)"
       apply (rule conjI)
      (* set QKD_Lg \<subseteq> states qkd_Kripke  *)
       apply (simp add: QKD_Lg_def qkd_Kripke_def qkd_scenario_def)
       apply (rule conjI)
        apply (simp add:  state_transition_qkd_refl_def)
      apply (rule conjI)
        apply (fold qkd_scenario_def, rule step0gR)
       apply (rule conjI)
      apply (insert step0gR step1gR, simp add: state_transition_qkd_refl_def)
       apply (rule conjI)
      apply (insert step2gR, simp add: state_transition_qkd_refl_def)
      apply (insert step3gR, simp add: state_transition_qkd_refl_def)
     (* hd QKD_Lg \<in> init qkd_Kripke *)
      apply (rule conjI)
       apply (simp add: QKD_Lg_def qkd_Kripke_def Iqkd_def)
     (* \<forall>i<length QKD_Lg. QKD_Le ! i \<rightarrow>\<^sub>i QKD_Lg ! Suc i \<and> last QKD_Lg \<in> negated_policy *)
      apply (rule allI)
      apply (rule impI)
      apply (simp add: QKD_Lg_def negated_policy_def)
      apply (rule conjI)
      prefer 2
       apply (rule QKD4g_bad)
      apply (subst state_transition_qkd_inst_def)
      apply (case_tac i)
       apply (simp add: step0g)
      apply (case_tac nat)
       apply (simp add: step1g)
      apply (case_tac nata)
       apply (simp add: step2g)
      apply (case_tac natb)
      by (simp add: step3g)+      
    fix x
    show "x = QKD_L \<or>
       x = QKD_La \<or> x = QKD_Lb \<or> x = QKD_Lc \<or> x = QKD_Ld \<or> x = QKD_Le \<or> x = QKD_Lf \<or> x = QKD_Lg \<Longrightarrow>
       set x \<subseteq> states qkd_Kripke \<and>
       hd x \<in> init qkd_Kripke \<and> (\<forall>i<length x - Suc (0::nat). x ! i \<rightarrow>\<^sub>i x ! Suc i \<and> last x \<in> negated_policy)"
      apply (erule disjE, erule ssubst, rule L)
        apply (erule disjE, erule ssubst, rule La)
      apply (erule disjE, erule ssubst, rule Lb)
      apply (erule disjE, erule ssubst, rule Lc)
      apply (erule disjE, erule ssubst, rule Ld)
      apply (erule disjE, erule ssubst, rule Le)
      apply (erule disjE, erule ssubst, rule Lf)
      by (erule ssubst, rule Lg)
  qed
qed

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