theory Prob 
  imports AT Complex_Main
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
         (\<forall> A:: 'O set. p A \<ge> 0) \<and> (p(UNIV :: 'O set) = 1) \<and>
         (\<forall> A:: 'O set. \<forall> B:: 'O set. A \<inter> B = {} \<longrightarrow> p(A \<union> B) = p A + p B)}"

typedef ('O :: finite)prob_dist = "{p :: ('O set \<Rightarrow> real).
         (\<forall> A:: 'O set. p A \<ge> 0) \<and> (p(UNIV :: 'O set) = 1) \<and>
         (\<forall> A:: 'O set. \<forall> B:: 'O set. A \<inter> B = {} \<longrightarrow> p(A \<union> B) = p A + p B)}"
proof (rule_tac x = "(\<lambda> x :: 'O set. if x = UNIV then 1 else 0)" in exI, rule CollectI, rule conjI)
  show " \<forall>A::'O set. (0::real) \<le> (if A = UNIV then 1::real else (0::real))" by simp
next show "(if UNIV = UNIV then 1::real else (0::real)) = (1::real) \<and>
    (\<forall>(A::'O set) B::'O set.
        A \<inter> B = {} \<longrightarrow>
        (if A \<union> B = UNIV then 1::real else (0::real)) =
        (if A = UNIV then 1::real else (0::real)) + (if B = UNIV then 1::real else (0::real)))"
    apply (rule conjI)
    apply simp
    apply clarify
    apply (rule CollectD)
    sorry
qed

(* Canonical construction *)
definition pmap :: "(('O :: finite) \<Rightarrow> real) \<Rightarrow> 'O set \<Rightarrow> real"
  where 
"pmap (ops :: ('O :: finite) \<Rightarrow> real) S \<equiv> Finite_Set.fold (\<lambda> x y. ops x + y) 0 S"

(* necessary at all?
lemma pmap_ops0: "(\<forall> x :: ('O :: finite). pmap ops {x} = ops x)"
proof (simp add: pmap_def)
  show "\<forall>x::'O. Finite_Set.fold (\<lambda>x::'O. (+) (ops x)) (0::real) {x} = ops x"
  sorry
qed
*)

theorem pmap_ops: "\<forall> x :: ('O :: finite). ops x \<ge> 0 \<Longrightarrow>
                   sum ops (UNIV :: 'O set) = 1 \<Longrightarrow> pmap ops \<in> prob_dist_def"
  apply (simp add: prob_dist_def_def)
  apply (rule conjI)
  apply (simp add: pmap_def)
  sorry

definition cond_prob :: "('O :: finite)prob_dist \<Rightarrow> 'O set \<Rightarrow> 'O set \<Rightarrow> real" ("_[_|_]" 50)
  where
"(P :: ('O :: finite)prob_dist)[A|B] \<equiv> (Rep_prob_dist P (A \<inter> B)) / (Rep_prob_dist P A)"

theorem law_of_total_probability:
"\<forall> A \<in> \<A>. \<forall> B \<in> \<A>. A \<noteq> B \<longrightarrow> A \<inter> B = {} \<Longrightarrow>
(Rep_prob_dist(P:: ('O :: finite)prob_dist)(B::'O set)) = sum (\<lambda> A. (P[B|A])*(Rep_prob_dist P A)) \<A>"
  sorry


definition F:: "('a :: state)set \<Rightarrow> 'a list set"
  where
"F s \<equiv> {l. \<forall> i < length l. l ! i \<rightarrow>\<^sub>i l ! (Suc i) \<and> last l \<in> s}"

definition eventually :: "[('a :: state)kripke, 'a set] \<Rightarrow> 'a list set" (infixr "\<turnstile>F" 50)
  where
"M \<turnstile>F s \<equiv> {l. set l \<subseteq> states M \<and> hd l \<in> init M} \<inter> F s"


definition probF :: "[('a :: state)kripke, 'a list set \<Rightarrow> real, real \<Rightarrow> bool, 'a set] \<Rightarrow> bool"
                                ("_ _ \<turnstile>PF\<^sub>_ _")
                                where
"M pdist \<turnstile>PF\<^sub>J s \<equiv> J(pdist (M \<turnstile>F s))" 


(* application to QKD in QKD.thy *)
end