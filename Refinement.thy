theory Refinement
imports AT
begin

(* Improvement possibility:
The first two conditions in mod_trans could be part of Kripke type_def and thus become implicit *)
definition refinement :: "[('a::state) kripke,('a'::state) \<Rightarrow> 'a, 'a' kripke] \<Rightarrow> bool" ("(_ \<sqsubseteq>\<^sub>_ _)" 50)  
  where "K \<sqsubseteq>\<^sub>E K' = (init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and>
    (\<forall> s' \<in> (states K'). (\<forall> s \<in> (init K'). (s \<rightarrow>\<^sub>i* s') \<longrightarrow> (E s) \<in> (init K) \<and> (E s) \<rightarrow>\<^sub>i* (E s'))))"

lemma init_ref: "K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> E ` (init K') \<subseteq> (init K)"
  apply (simp add: refinement_def)
  apply (rule subsetI)
  apply (erule imageE)
  apply (rotate_tac -2)
  apply (erule ssubst)
  apply (erule conjE)+
  apply (drule_tac x = xa in bspec)
  apply (erule subsetD, assumption)
  apply (drule_tac x = xa in bspec)
  apply assumption
  apply (erule impE)
  apply (simp add: state_transition_refl_def)
by (erule conjE, assumption)

(* This version allows that the init in the refinement "deletes" some initial states *)
theorem prop_pres:  "K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> (\<forall> s' \<in> (Pow (states K')). 
                      (K' \<turnstile> EF s') \<longrightarrow> (Kripke (states K)(E ` (init K')) \<turnstile> EF (E ` s')))" 
  apply clarify
  apply (frule init_ref)
  apply (unfold refinement_def)
  apply (erule conjE)+
  apply (simp add: check_def)
  apply (rule subsetI)
  apply (rule CollectI)
  apply (rule conjI)
  apply (rule_tac A = "init K" in subsetD, assumption)
   apply (rule_tac A = "E ` init K'" in subsetD, assumption+)
  apply (subgoal_tac "? y. y \<in> init K' \<and> E y = x")
   prefer 2
  apply force
  apply (erule exE)
  apply (erule conjE)
   apply (rotate_tac 1)
   apply (drule subsetD, assumption)
   apply (erule CollectE)
  apply (erule conjE)
   apply (drule EF_step_star_rev)
  apply (erule bexE)
  apply (drule_tac x = ya in bspec)
  apply (erule subsetD, assumption)
  apply (drule_tac x = y in bspec, assumption)
  apply (drule mp, assumption)
  apply (erule conjE)
  apply (rule_tac y = "E ya" in EF_step_star)
   apply (erule subst, assumption)
by simp

(* In this version of the property preservation theorem, the init_ref condition is
   stronger so it will be disallowed to "delete" initial states during refinement. 
   Then the second more complex Kripke structure in prop_pres becomes simply K *)
lemma Kripke_self: "K = Kripke (states K) (init K)"
  apply (case_tac K)
by simp

theorem prop_pres':  "K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> init K \<subseteq> E ` (init K') \<Longrightarrow> (\<forall> s' \<in> (Pow (states K')). 
                      (K' \<turnstile> EF s') \<longrightarrow> (K \<turnstile> EF (E ` s')))" 
  apply (subgoal_tac "init K = E ` (init K')")
   apply (subgoal_tac "K = Kripke (states K)(init K)")
  apply (rotate_tac -1)
  apply (erule ssubst)
    apply (erule ssubst)
  apply (rule prop_pres, assumption)
   apply (rule Kripke_self)
  apply (rule subset_antisym, assumption)
by (erule init_ref)


theorem strong_mt[rule_format]: 
"init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and> E ` (init K') \<subseteq> (init K) \<and> (\<forall> s s'. s \<rightarrow>\<^sub>i s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i (E s')) \<Longrightarrow>
                                K \<sqsubseteq>\<^sub>E K'"
  apply (unfold refinement_def)
  apply simp
  apply (erule conjE)+
  apply (rule ballI)+
  apply (rule impI)
  apply (rule conjI)
   apply (erule subsetD)
   apply (erule imageI)
  apply (subgoal_tac "(\<forall>s::'a. s \<rightarrow>\<^sub>i s' \<longrightarrow> E s \<rightarrow>\<^sub>i E s') \<longrightarrow> s \<rightarrow>\<^sub>i* s' \<longrightarrow> E s \<rightarrow>\<^sub>i* E s'")
   apply simp
  apply (simp add: state_transition_refl_def)
  apply (erule_tac rtrancl_induct)
   apply simp
  apply (drule_tac x = y in spec)
  apply (drule_tac x = z in spec)
  apply (drule mp, simp)
  apply (erule rtrancl_into_rtrancl)
  apply (rule CollectI)
  by simp

theorem strong_mt'[rule_format]: 
"init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and> E ` (init K') \<subseteq> (init K) \<and> 
     (\<forall> s s'. (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s) \<longrightarrow> s \<rightarrow>\<^sub>i s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i (E s')) \<Longrightarrow>
                                K \<sqsubseteq>\<^sub>E K'"
  apply (unfold refinement_def)
  apply simp
  apply (erule conjE)+
  apply (rule ballI)+
  apply (rule impI)
  apply (rule conjI)
   apply (erule subsetD)
   apply (erule imageI)
  apply (subgoal_tac "(\<forall>s::'a. (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s) \<longrightarrow> s \<rightarrow>\<^sub>i s' \<longrightarrow> E s \<rightarrow>\<^sub>i E s') \<longrightarrow> 
                                  (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s) \<longrightarrow> s \<rightarrow>\<^sub>i* s' \<longrightarrow> E s \<rightarrow>\<^sub>i* E s'")
   apply simp
   apply (erule mp)
   apply (rule_tac x = s in bexI)
    apply (simp add: state_transition_refl_def, assumption)
     apply (simp add: state_transition_refl_def)
  apply (erule_tac rtrancl_induct)
   apply simp
  apply (rule impI)
  apply (drule mp)
  apply assumption
   apply (drule_tac x = y in spec)
(* *)
  apply (rotate_tac -1)
   apply (drule mp)
    apply (rule_tac x = s in bexI)
  apply assumption+
  apply (erule rtrancl_into_rtrancl)
   apply (rule CollectI)
by simp

theorem strong_mt''[rule_format]: 
"init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and> E ` (init K') \<subseteq> (init K) \<and> 
     (\<forall> s s'. (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s) \<longrightarrow> s \<rightarrow>\<^sub>i s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i* (E s')) \<Longrightarrow>
                                K \<sqsubseteq>\<^sub>E K'"
  apply (unfold refinement_def)
  apply simp
  apply (erule conjE)+
  apply (rule ballI)+
  apply (rule impI)
  apply (rule conjI)
   apply (erule subsetD)
   apply (erule imageI)
  apply (subgoal_tac "(\<forall>s::'a. (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s) \<longrightarrow> s \<rightarrow>\<^sub>i s' \<longrightarrow> E s \<rightarrow>\<^sub>i* E s') \<longrightarrow> 
                                  (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s) \<longrightarrow> s \<rightarrow>\<^sub>i* s' \<longrightarrow> E s \<rightarrow>\<^sub>i* E s'")
   apply simp
   apply (erule mp)
   apply (rule_tac x = s in bexI)
    apply (simp add: state_transition_refl_def, assumption)
     apply (simp add: state_transition_refl_def)
  apply (erule_tac rtrancl_induct)
   apply simp
  apply (rule impI)
  apply (drule mp)
  apply assumption
  apply (drule_tac x = y in spec)
  apply (rotate_tac -1)
   apply (drule mp)
    apply (rule_tac x = s in bexI)
    apply assumption+
  thm rtrancl_trans
  apply (erule rtrancl_trans)
by simp

definition RR_cycle :: "[('a::state) kripke, ('a'::state)kripke, 'a' set] \<Rightarrow> bool"
  where "RR_cycle K K' s = (\<exists> (E:: ('a'::state) \<Rightarrow> 'a). (K \<turnstile> EF (E `s)) \<and> (K \<sqsubseteq>\<^sub>E K')  \<longrightarrow> \<not>(K' \<turnstile> EF s))"

end

