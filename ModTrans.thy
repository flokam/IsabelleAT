theory ModTrans 
imports AT
begin

(* FIXME:
The first two condition in mod_trans should be part of Kripke type_def and thus become implicit *)
definition mod_trans :: "[('a::state) kripke,('a'::state) \<Rightarrow> 'a, 'a' kripke] \<Rightarrow> bool" ("(_ \<sqsubseteq>\<^sub>_ _)" 50)  
  where "K \<sqsubseteq>\<^sub>E K' = (init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and>
    (\<forall> s' \<in> (states K'). (\<forall> s \<in> (init K'). (s \<rightarrow>\<^sub>i* s') \<longrightarrow> (E s) \<in> (init K) \<and> (E s) \<rightarrow>\<^sub>i* (E s'))))"

lemma init_ref: "K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> E ` (init K') \<subseteq> (init K)"
  apply (simp add: mod_trans_def)
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

(* Improvement(?): make the init_ref condition stronger so it will be disallowed to "delete" 
   initial states during refinement. Then the second more complex Kripke structure
   in prop_pres would become just K*)
theorem prop_pres:  "K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> (\<forall> s' \<in> (Pow (states K')). 
                      (K' \<turnstile> EF s') \<longrightarrow> (Kripke (states K)(E ` (init K')) \<turnstile> EF (E ` s')))" 
  apply clarify
  apply (frule init_ref)
  apply (unfold mod_trans_def)
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


(*
theorem prop_pres:  "K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> (\<forall> s' \<in> (Pow (states K')). (K' \<turnstile> EF s') \<longrightarrow> (K \<turnstile> EF (E ` s')))" 
  apply clarify
  apply (unfold mod_trans_def)
  apply (erule conjE)+
  apply (simp add: check_def)
  apply (rule subsetI)
  apply (rule CollectI)
  apply (rule conjI)
  apply (rotate_tac 2)
   apply (erule subsetD, assumption)
     apply (rule_tac y = x in EF_step_star)
   apply (simp add: state_transition_refl_def)
  apply (subgoal_tac "\<exists> y. y \<in> (init K')")
  prefer 2
   apply force
   apply (erule exE)
   apply (rotate_tac 1)
   apply (drule subsetD, assumption)
  apply (rotate_tac -1)
   apply (erule CollectE)
  apply (erule conjE)
   apply (drule EF_step_star_rev)
  apply (erule bexE)
  apply (drule_tac x = "ya" in bspec)
  thm subsetD
   apply (rule_tac A = s' in subsetD, assumption+)
  apply (drule_tac x = "y" in bspec)


   apply (subgoal_tac "states K' \<noteq> {}")
    apply (subgoal_tac "? x. x \<in> states K'")
     apply (erule exE)
     apply (drule_tac x = xa in bspec, assumption)
  apply (drule_tac x = x in bspec, assumption)


   apply (erule subsetD, assumption)
  

  apply (drule mp)

*)


theorem strong_mt[rule_format]: "E ` (init K') \<subseteq> (init K) \<and> (\<forall> s s'. s \<rightarrow>\<^sub>i s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i (E s')) \<Longrightarrow>
                                K \<sqsubseteq>\<^sub>E K'"
  sorry

end

