theory ModTrans 
imports AT
begin
definition mod_trans :: "[('a::state) kripke,('a'::state) \<Rightarrow> 'a, 'a' kripke] \<Rightarrow> bool" ("(_ \<sqsubseteq>\<^sub>_ _)" 50)  
  where "K \<sqsubseteq>\<^sub>E K' = 
    (\<forall> s' \<in> (states K'). (\<forall> s \<in> (init K'). (s \<rightarrow>\<^sub>i* s') \<longrightarrow> (E s) \<in> (init K) \<and> (E s) \<rightarrow>\<^sub>i* (E s')))"

lemma init_ref: "K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> E ` (init K') \<subseteq> (init K)"
  apply (simp add: mod_trans_def)
  apply (rule subsetI)
  apply (erule imageE)
  apply (rotate_tac -2)
  apply (erule ssubst)
  apply (drule_tac x = xa in bspec)
   apply (simp add: init_def states_def)
   defer
  apply (drule_tac x = xa in bspec)
    apply assumption
   apply (erule impE)
    apply (simp add: state_transition_refl_def)
  apply (erule conjE, assumption)
  sorry

theorem prop_pres:  "K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> (\<forall> s' \<in> (Pow (state K')). (K \<turnstile> EF s') \<longrightarrow> (K' \<turnstile> EF(E ` s')))" 
  sorry

theorem strong_mt[rule_format]: "E ` (init K') \<subseteq> (init K) \<and> (\<forall> s s'. s \<rightarrow>\<^sub>i s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i (E s')) \<Longrightarrow>
                                K \<sqsubseteq>\<^sub>E K'"
  sorry

end

