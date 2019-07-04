theory Prob 
  imports  FMap
begin

definition prob_space :: "(('O:: finite) set)set \<Rightarrow> bool"
  where
"prob_space S \<equiv> {} \<in> S \<and> (UNIV:: 'O set) \<in> S \<and>
                (\<forall> A \<in> S. \<forall> B \<in> S. A \<union> B \<in> S) \<and> (\<forall> A \<in> S. (UNIV :: 'O set) - A \<in> S)"

theorem Pow_prob_space: "prob_space (Pow ((UNIV :: (('O :: finite)) set)))"
  by (simp add: prob_space_def)

definition prob_dist_def
  where
"prob_dist_def \<equiv> {p :: (('O :: finite) set \<Rightarrow> real).
         (\<forall> A:: 'O set. p A \<ge> 0) \<and> p {} = 0 \<and> (p(UNIV :: 'O set) = 1) \<and>
         (\<forall> A:: 'O set. \<forall> B:: 'O set.  p(A \<union> B) = p A + p B - p(A \<inter> B))}"

typedef ('O :: finite)prob_dist = "{p :: ('O set \<Rightarrow> real).
         (\<forall> A:: 'O set. p A \<ge> 0) \<and> p {} = 0 \<and> (p(UNIV :: 'O set) = 1) \<and> 
         (\<forall> A:: 'O set. \<forall> B:: 'O set.  p(A \<union> B) = p A + p B - p(A \<inter> B))}"
proof (rule_tac x = "(\<lambda> x :: 'O set. ((card x)::real)/((card (UNIV :: 'O set))::real))" in exI, rule CollectI, rule conjI)
  show " \<forall>A::'O set. (0::real) \<le> real (card A) / real (card UNIV)" by simp
next show "real (card ({}  :: ('O :: finite) set)) / real (card (UNIV  :: ('O :: finite) set)) = (0::real) \<and> 
       real (card (UNIV :: ('O :: finite) set)) / real (card (UNIV :: ('O :: finite)set)) = (1::real) \<and>
    (\<forall>(A::('O ::finite) set) B::('O::finite) set.
        real (card (A \<union> B)) / real (card (UNIV :: ('O :: finite)set)) =
        real (card A) / real (card (UNIV :: ('O :: finite)set)) + 
        real (card B) / real (card (UNIV :: ('O :: finite)set))
        - (real (card (A \<inter> B)) / real (card (UNIV :: ('O :: finite)set))))"
  proof (rule conjI)
    show "real (card ({}  :: ('O :: finite) set)) / real (card (UNIV  :: ('O :: finite) set)) = (0::real)"
    by simp
  next show "real (card (UNIV :: ('O :: finite) set)) / real (card (UNIV :: ('O :: finite)set)) = (1::real) \<and>
    (\<forall>(A::('O ::finite) set) B::('O::finite) set.
        real (card (A \<union> B)) / real (card (UNIV :: ('O :: finite)set)) =
        real (card A) / real (card (UNIV :: ('O :: finite)set)) + 
        real (card B) / real (card (UNIV :: ('O :: finite)set))
        - (real (card (A \<inter> B)) / real (card (UNIV :: ('O :: finite)set))))"
    apply (rule conjI)
     apply simp
    apply clarify
    apply (subgoal_tac "real (card A) / real (card (UNIV :: ('O :: finite) set)) + 
                        real (card B) / real (card (UNIV :: ('O :: finite) set)) -
                        real (card (A \<inter> B)) / real (card (UNIV :: ('O :: finite) set)) = 
                        (real (card A) + real (card B) - real (card (A \<inter> B))) / 
                              real (card (UNIV :: ('O :: finite) set))")
    apply (rotate_tac -1)
     apply (erule ssubst)
     apply (subgoal_tac "real (card (A \<union> B)) = real (card A) + real (card B) - real (card (A \<inter> B))")
      apply (rotate_tac -1)
      apply (erule ssubst)
      apply (rule refl)
     apply (subgoal_tac "card (A \<union> B) = card A + card B - card (A \<inter> B)")
      apply (rotate_tac -1)
      apply (erule ssubst)
    apply (metis add_diff_cancel_right' card_Un_Int finite of_nat_add)
    apply (metis add_diff_cancel_right' card_Un_Int finite)
    by (simp add: add_divide_distrib diff_divide_distrib)
qed
qed

(* lemmas to use prop_space and prob_dist *)
lemma prob_dist_def_Abs_inv: "p \<in> prob_dist_def \<Longrightarrow> Rep_prob_dist (Abs_prob_dist p) = p"
  apply (unfold prob_dist_def_def)
  by (erule Abs_prob_dist_inverse)

lemma prob_dist_def_Rep_inv: "Rep_prob_dist (p :: ('O :: finite)prob_dist) \<in> prob_dist_def"
  apply (unfold prob_dist_def_def)
  by (rule Rep_prob_dist)

lemma prob_dist_defE1: "(p :: (('O :: finite) set \<Rightarrow> real)) \<in> prob_dist_def \<Longrightarrow> (\<forall> A:: 'O set. p A \<ge> 0)"
proof (simp add: prob_dist_def_def)
qed

lemma prob_dist_defE1a: "(p :: (('O :: finite) set \<Rightarrow> real)) \<in> prob_dist_def \<Longrightarrow> (p({} :: 'O set) = 0)"
proof (simp add: prob_dist_def_def)
qed

lemma prob_dist_defE2: "(p :: (('O :: finite) set \<Rightarrow> real)) \<in> prob_dist_def \<Longrightarrow> (p(UNIV :: 'O set) = 1)"
proof (simp add: prob_dist_def_def)
qed

lemma prob_dist_defE3[rule_format]: "(p :: (('O :: finite) set \<Rightarrow> real)) \<in> prob_dist_def \<Longrightarrow> 
                        (\<forall> A:: 'O set. \<forall> B:: 'O set.  p(A \<union> B) = p A + p B - p(A \<inter> B))"
proof (simp add: prob_dist_def_def)
qed

lemma prob_dist_defE3'[rule_format]: "(p :: (('O :: finite) set \<Rightarrow> real)) \<in> prob_dist_def \<Longrightarrow> 
                     (A :: 'O set) \<inter> (B:: 'O set) = {} \<Longrightarrow>   p(A \<union> B) = p A + p B"
proof (simp add: prob_dist_defE3 prob_dist_defE1a)
qed


lemma prob_dist_compl: assumes "p \<in> prob_dist_def"
  shows "p ((UNIV :: (('O :: finite)set)) - A :: (('O :: finite) set)) = 1 - p A"
proof -
  have a: "p (UNIV :: (('O :: finite)set)) = 1"  using assms
    by (rule prob_dist_defE2)
  moreover have b: "p (UNIV :: (('O :: finite)set)) - p A = 1 - p A" using a
    by simp
  moreover have c: "(UNIV :: (('O :: finite)set)) = (UNIV :: (('O :: finite)set)) - A  \<union> A" by simp
  moreover have d: "((UNIV :: (('O :: finite)set)) - A) \<inter> A = {}" by blast
  moreover have e: "p (((UNIV :: (('O :: finite)set)) - A) \<union> A) - p A = 1 - p A" 
    by (simp add: prob_dist_defE2 a)
  moreover have f: "p (((UNIV :: (('O :: finite)set)) - A) \<union> A)= p (((UNIV :: (('O :: finite)set)) - A)) + p A" 
    apply (rule prob_dist_defE3')
     apply (rule assms)
    by (rule d)
  ultimately show "p ((UNIV :: (('O :: finite)set)) - A :: (('O :: finite) set)) = 1 - p A"
    apply (rule_tac P =  "\<lambda> x. p ((UNIV :: (('O :: finite)set)) - A :: (('O :: finite) set)) = x" in subst)
     apply (rule e)
    apply (subst f)
    by simp
qed


lemma prob_dist_and: assumes "p \<in> prob_dist_def"
     shows "\<forall> (B :: (('O :: finite) set)). p ((A :: (('O :: finite) set)) \<inter> B) = p A * p B"
proof -
  show "\<forall> (B :: (('O :: finite) set)). p ((A :: (('O :: finite) set)) \<inter> B) = p A * p B"
    apply (rule finite_psubset_induct, rule finite)
    apply (rule allI)
    apply (case_tac "A = {}")
     apply (simp add: prob_dist_defE1a assms)
    apply (subgoal_tac "\<exists> x. x \<in> A")
     prefer 2
     apply blast
    apply (erule exE)
  proof -
     show "\<And>(A::'O set) (B::'O set) x::'O.
       finite A \<Longrightarrow>
       (\<And>B::'O set. B \<subset> A \<Longrightarrow> \<forall>Ba::'O set. p (B \<inter> Ba) = p B * p Ba) \<Longrightarrow>
       A \<noteq> {} \<Longrightarrow> x \<in> A \<Longrightarrow> p (A \<inter> B) = p A * p B"
     proof -
       fix A B x
      have a: "x \<in> A \<Longrightarrow> ((A :: (('O :: finite) set)) \<inter> B) = (({x} \<inter> B) \<union> ((A - {x}) \<inter> B))" 
        by blast
      have b: "x \<in> A \<Longrightarrow> p ((A :: (('O :: finite) set)) \<inter> B) = p (({x} \<inter> B) \<union> ((A - {x}) \<inter> B))"
        by (simp add: a)
      have c: "({x} \<inter> B) \<inter> ((A - {x}) \<inter> B) = {}" 
        by blast
      have d: "p (({x} \<inter> B) \<union> ((A - {x}) \<inter> B)) = p ({x} \<inter> B) + p ((A - {x}) \<inter> B)"
        apply (rule prob_dist_defE3')
         apply (rule assms)
        by (rule c)
      have e: "(\<And>B::'O set. B \<subset> A \<Longrightarrow> \<forall>Ba::'O set. p (B \<inter> Ba) = p B * p Ba) \<Longrightarrow>
       A \<noteq> {} \<Longrightarrow> x \<in> A \<Longrightarrow> p ((A - {x}) \<inter> B) = p (A - {x}) * p B"
        apply (drule_tac x = "A - {x}" in meta_spec)
        apply (drule meta_mp)
         apply blast
        by (erule spec)
      have f:  "(\<And>B::'O set. B \<subset> A \<Longrightarrow> \<forall>Ba::'O set. p (B \<inter> Ba) = p B * p Ba) \<Longrightarrow>
       A \<noteq> {} \<Longrightarrow> A \<noteq> {x} \<Longrightarrow> x \<in> A \<Longrightarrow> p ({x} \<inter> B) = p {x} * p B"
        apply (drule_tac x = "{x}" in meta_spec)
        apply (drule meta_mp)
         apply blast
        by (erule spec)
      show "(\<And>B::'O set. B \<subset> A \<Longrightarrow> \<forall>Ba::'O set. p (B \<inter> Ba) = p B * p Ba) \<Longrightarrow>
       A \<noteq> {} \<Longrightarrow> x \<in> A \<Longrightarrow> p (A \<inter> B) = p A * p B"
        apply (case_tac "A = {x}")
        apply simp
         apply (rule f)
            apply simp
        apply simp
         apply (rule_tac P = "\<lambda> x. x = p A * p B" in ssubst)
          apply (erule b)
         apply (subst d)
         apply (subst e)
            apply assumption+
         apply (subst f)
        apply assumption+
        sorry
    qed
  qed
qed

(* simply an gerneralisation of prob_dist_defE3'*)
lemma prob_dist_sum: "(\<forall> A \<in> \<A>. \<forall> B \<in> \<A>. A \<noteq> B \<longrightarrow> A \<inter> B = {}) \<Longrightarrow> p \<in> prob_dist_def \<Longrightarrow> 
      p(\<Union> A \<in> \<A>. A) = sum (\<lambda> A. p A) \<A>"
  sorry

lemma prob_dist_sum': assumes "(\<forall> A \<in> (\<A> :: ('O :: finite) set set). \<forall> B \<in> \<A>. A \<noteq> B \<longrightarrow> A \<inter> B = {})" 
                              "p \<in> prob_dist_def" 
                            shows "p(\<Union> A \<in> \<A>. C \<inter> A) = sum (\<lambda> A. p (C \<inter> A)) \<A>"
proof -
  have a: "(\<forall> A \<in> fmap (\<lambda> x. C \<inter> x) (\<A> :: ('O :: finite) set set). 
            \<forall> B \<in> fmap (\<lambda> x. C \<inter> x) \<A>. A \<noteq> B \<longrightarrow> A \<inter> B = {})" using assms
    apply (simp add: fmap_def)
    sorry
  moreover have b: "p(\<Union> A \<in> fmap (\<lambda> x. C \<inter> x) (\<A> :: ('O :: finite) set set). A) = 
          sum (\<lambda> A. p A) (fmap (\<lambda> x. C \<inter> x) (\<A> :: ('O :: finite) set set))"
    apply (rule prob_dist_sum)
     apply (rule a)
    by (rule assms)
  moreover have c: "(\<Union> A \<in> \<A>. C \<inter> A) = (\<Union> A \<in> fmap (\<lambda> x. C \<inter> x) (\<A> :: ('O :: finite) set set). A)"
    apply (simp add: fmap_lem_map finite fmap_lem_one fmap_lem)
    sorry
  moreover have d: "sum (\<lambda> A. p A) (fmap (\<lambda> x. C \<inter> x) (\<A> :: ('O :: finite) set set)) =
                   sum (\<lambda> A. p (C \<inter> A)) \<A>"
    sorry
  ultimately show "p(\<Union> A \<in> \<A>. C \<inter> A) = sum (\<lambda> A. p (C \<inter> A)) \<A>"
    apply (subst c)
    by simp
qed



(* Canonical construction *)
definition pmap :: "(('O :: finite) \<Rightarrow> real) \<Rightarrow> 'O set \<Rightarrow> real"
  where 
"pmap (ops :: ('O :: finite) \<Rightarrow> real) S \<equiv> Finite_Set.fold (\<lambda> x y. ops x + y) 0 S"


theorem pmap_ops: "\<forall> x :: ('O :: finite). ops x \<ge> 0 \<Longrightarrow>
                   sum ops (UNIV :: ('O :: finite) set) = 1 \<Longrightarrow> pmap ops \<in> prob_dist_def"
  apply (simp add: prob_dist_def_def)
  apply (rule conjI)
  apply (simp add: pmap_def)
  sorry

definition cond_prob :: "('O :: finite)prob_dist \<Rightarrow> 'O set \<Rightarrow> 'O set \<Rightarrow> real" ("_[_|_]" 50)
  where
"(P :: ('O :: finite)prob_dist)[A|B] \<equiv> (Rep_prob_dist P (A \<inter> B)) / (Rep_prob_dist P B)"

lemma cond_prob2: "(Rep_prob_dist P (A \<inter> B)) = ((P :: ('O :: finite)prob_dist)[A|B]) * (Rep_prob_dist P B)"
  apply (subst cond_prob_def)
  apply simp
  apply (insert prob_dist_and)
  apply (drule_tac x = "Rep_prob_dist P" in meta_spec)
  apply (subgoal_tac "Rep_prob_dist P \<in> prob_dist_def")
   apply simp
  apply (thin_tac "(\<And>A::'O set.
        Rep_prob_dist P \<in> prob_dist_def \<Longrightarrow>
        \<forall>B::'O set. Rep_prob_dist P (A \<inter> B) = Rep_prob_dist P A * Rep_prob_dist P B)")
  apply (insert Rep_prob_dist)
  apply (drule_tac x = P in meta_spec)
by (simp add: prob_dist_def_def)


theorem law_of_total_probability:
  assumes "\<Union> \<A> = (UNIV :: 'O set)"
          "\<forall> A \<in> \<A>. \<forall> B \<in> \<A>. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
  shows "(Rep_prob_dist(P:: ('O :: finite)prob_dist)(B::'O set)) = sum (\<lambda> A. (P[B|A])*(Rep_prob_dist P A)) \<A>"
proof -
  show "Rep_prob_dist P B = (\<Sum>A::'O set\<in>\<A>. (P[B|A]) * Rep_prob_dist P A)"
  proof -
  have a: "Rep_prob_dist P (B :: 'O set) = Rep_prob_dist P (B \<inter> (UNIV :: 'O set))" by simp
  moreover have b: "Rep_prob_dist P (B \<inter> (UNIV :: 'O set)) = Rep_prob_dist P (B \<inter> \<Union> \<A>)" using assms(1)
    by simp
  moreover have c: "Rep_prob_dist P (B \<inter> \<Union> \<A>) = Rep_prob_dist P (\<Union> A \<in> \<A>. B \<inter> A)" using assms(2)
    by simp
  moreover have d: "Rep_prob_dist P (\<Union> A \<in> \<A>. B \<inter> A) = sum (\<lambda> A. Rep_prob_dist P (B \<inter> A)) \<A>" using assms
    apply (rule_tac p = "Rep_prob_dist P" in prob_dist_sum')
     apply (rule assms(2))
  apply (insert Rep_prob_dist)
  apply (drule_tac x = P in meta_spec)
    by (simp add: prob_dist_def_def)
  moreover have e: "sum (\<lambda> A. Rep_prob_dist P (B \<inter> A)) \<A> = sum (\<lambda> A. (P[B|A])*(Rep_prob_dist P A)) \<A>"
    apply (subst cond_prob2)
    by (rule refl)
  ultimately show "Rep_prob_dist P B = (\<Sum>A::'O set\<in>\<A>. (P[B|A]) * Rep_prob_dist P A)"
    apply (subst a)
    apply (subst b)
    apply (subst c)
    apply (subst d)
    apply (subst e)
    by (rule refl) 
qed
qed


definition F:: "('a :: state)set \<Rightarrow> 'a list set"
  where
"F s \<equiv> {l. (\<forall> i < length l - 1. l ! i \<rightarrow>\<^sub>i l ! (Suc i)) \<and> last l \<in> s}"

definition eventually :: "[('a :: state)kripke, 'a set] \<Rightarrow> 'a list set" (infixr "\<turnstile>F" 50)
  where
"M \<turnstile>F s \<equiv> {l. set l \<subseteq> states M \<and> hd l \<in> init M} \<inter> F s"


definition probF :: "[('a :: state)kripke, 'a list set \<Rightarrow> real, real \<Rightarrow> bool, 'a set] \<Rightarrow> bool"
                                ("_ _ \<turnstile>PF\<^sub>_ _")
                                where
"M pdist \<turnstile>PF\<^sub>J s \<equiv> J(pdist (M \<turnstile>F s))" 


(* application to QKD in QKD.thy *)
end