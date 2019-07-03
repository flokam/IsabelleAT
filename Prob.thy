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

lemma finiteA: "finite (A :: (('O :: finite) set))"
proof (rule Finite_Set.finite_class.finite)
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
      have b: "x \<in> A \<Longrightarrow> p (A \<inter> B) = p (({x} \<inter> B) \<union> ((A - {x}) \<inter> B))"
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

      show "\<And>(A::'O set) (B::'O set) x::'O.
       finite A \<Longrightarrow>
       (\<And>B::'O set. B \<subset> A \<Longrightarrow> \<forall>Ba::'O set. p (B \<inter> Ba) = p B * p Ba) \<Longrightarrow>
       A \<noteq> {} \<Longrightarrow> x \<in> A \<Longrightarrow> p (A \<inter> B) = p A * p B"
        apply (case_tac "A = {x}")

        sorry
    qed
  qed
qed

lemma prob_dist_sum: "(\<forall> A \<in> \<A>. \<forall> B \<in> \<A>. A \<noteq> B \<longrightarrow> A \<inter> B = {}) \<Longrightarrow> p \<in> prob_dist_def \<Longrightarrow> 
      p(\<Union> A \<in> \<A>. A) = sum (\<lambda> A. p A) \<A>"
  sorry

lemma prob_dist_sum': assumes "(\<forall> A \<in> \<A>. \<forall> B \<in> \<A>. A \<noteq> B \<longrightarrow> A \<inter> B = {})" 
                              "p \<in> prob_dist_def" 
                            shows "p(\<Union> A \<in> \<A>. B \<inter> A) = sum (\<lambda> A. p (B \<inter> A)) \<A>"
proof -
  show "p(\<Union> A \<in> \<A>. B \<inter> A) = sum (\<lambda> A. p (B \<inter> A)) \<A>"
  proof -
    have a: "p(\<Union> A \<in> \<A>. B \<inter> A) =  p(B \<inter>(\<Union> A \<in> \<A>. A))" by simp
    moreover have b: "p(B \<inter>(\<Union> A \<in> \<A>. A)) = p B * p(\<Union> A \<in> \<A>. A)"  using assms
      by (simp add: prob_dist_and)
    moreover have c: "p(\<Union> A \<in> \<A>. A) = (sum (\<lambda> A. p A) \<A>)" using assms
      by (rule prob_dist_sum)
    moreover have d: "p B * p(\<Union> A \<in> \<A>. A) = p B * (sum (\<lambda> A. p A) \<A>)" 
      by (subst c, rule refl)
    moreover have e: "p B * (sum (\<lambda> A. p A) \<A>) =  (sum (\<lambda> A. p B * p A) \<A>)" 
      using sum_distrib_left by blast
    moreover have f: "(sum (\<lambda> A. p B * p A) \<A>) = (sum (\<lambda> A. p (B \<inter> A)) \<A>)" using assms
      by (simp add: prob_dist_and)
    ultimately show "p(\<Union> A \<in> \<A>. B \<inter> A) = sum (\<lambda> A. p (B \<inter> A)) \<A>"
      apply (subst a)
      apply (subst b)
      apply (subst c)
      apply (subst e)
      by (rule f)
  qed
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

(* some general techniques for mapping function on finite sets *)
(* general scheme for map over finite sets.
   This would be a useful provision for the Finite_Set library: everyone needs
   a simple map on Finite Sets all the time! *)
definition fmap :: "['a \<Rightarrow> 'b, 'a set] \<Rightarrow> 'b set"
  where "fmap f S = Finite_Set.fold (\<lambda> x y. insert (f x) y) {} S"

(* doesn't work since not commutative -- consider 
   linear sorted domains and then use sorted_list_of_set
definition fmapL :: "['a \<Rightarrow> 'b, 'a set] \<Rightarrow> 'b list"
  where "fmapL f S = Finite_Set.fold (\<lambda> x y. (f x) # y) [] S"
*)

lemma fmap_lem_map[rule_format]: "finite S \<Longrightarrow> n \<in> S \<longrightarrow> (f n) \<in> (fmap f S)"
  apply (erule_tac F = S in finite_induct)
   apply simp
  apply clarify
  apply (simp add: fmap_def)
  apply (subgoal_tac "comp_fun_commute (\<lambda>x::'a. insert (f x))")
   apply (drule_tac A = "F" in Finite_Set.comp_fun_commute.fold_insert)
     apply assumption+
   apply (erule ssubst)
   apply (erule disjE)
  apply force+
apply (simp add: comp_fun_commute_def)
by force


lemma fmap_lem_map_rev[rule_format]: "finite S \<Longrightarrow> inj f \<Longrightarrow> (f n) \<in> (fmap f S) \<longrightarrow> n \<in> S"
  apply (erule_tac F = S in finite_induct)
   apply (simp add: fmap_def)
  apply clarify
  apply (simp add: fmap_def)
  apply (subgoal_tac "comp_fun_commute (\<lambda>x::'a. insert (f x))")
   apply (drule_tac A = "F" and z = "{}" in Finite_Set.comp_fun_commute.fold_insert)
     apply assumption+
   apply (subgoal_tac "f n \<in> insert (f x) (Finite_Set.fold (\<lambda>x::'a. insert (f x)) {} F)")
    prefer 2
    apply simp
   apply (subgoal_tac "f n = f x")
    prefer 2
    apply simp
   apply (erule injD, assumption) 
apply (simp add: comp_fun_commute_def)
by force

lemma fold_one: "Finite_Set.fold (\<lambda>x::'a. insert (f x)) {} {n} = {f n}"
  thm Finite_Set.comp_fun_commute.fold_insert
  apply (subgoal_tac "comp_fun_commute (\<lambda>x::'a. insert (f x))")
   apply (drule_tac A = "{}" in Finite_Set.comp_fun_commute.fold_insert)
     apply simp+
  apply (simp add: comp_fun_commute_def)
  by force

(*
lemma fold_oneL: "Finite_Set.fold (\<lambda> (x::'a). (#)(f x)) [] {n} = [f n]"
  apply (subgoal_tac "comp_fun_commute (\<lambda> (x::'a). (#)(f x))")
   apply (drule_tac A = "{}" and z = "[]" in Finite_Set.comp_fun_commute.fold_insert)
     apply simp+
  apply (simp add: comp_fun_commute_def)
fails here  
by force
*)


lemma fold_one_plus: "Finite_Set.fold (+) (b::real) {a::real} = a + b"
  apply (subgoal_tac "comp_fun_commute (+)")
   apply (drule_tac A = "{}" in Finite_Set.comp_fun_commute.fold_insert)
  apply simp+
  apply (simp add: comp_fun_commute_def)
  apply (simp add: comp_def)
by force

lemma fold_two_plus: "a \<noteq> c \<Longrightarrow> Finite_Set.fold (+) (b::real) {a::real, c} = a + b + c"
  apply (subgoal_tac "comp_fun_commute (+)")
   apply (drule_tac A = "{ c}" and x = a in Finite_Set.comp_fun_commute.fold_insert)
     apply simp+
   apply (simp add: fold_one_plus)
   apply (subgoal_tac "a + (c + b) = a + b + c")
    apply (erule ssubst)
    apply assumption
  apply simp
  apply (simp add: comp_fun_commute_def)
  apply (simp add: comp_def)
by force

lemma fold_three_plus: "a \<noteq> c \<Longrightarrow> a \<noteq> b \<Longrightarrow> b \<noteq> c \<Longrightarrow> Finite_Set.fold (+) (d::real) {a::real, b, c} = a + b + c + d"
  apply (subgoal_tac "comp_fun_commute (+)")
   apply (drule_tac A = "{b, c}" and x = a and z = d in Finite_Set.comp_fun_commute.fold_insert)
     apply simp+
   apply (simp add: fold_two_plus)
  apply (simp add: comp_fun_commute_def)
  apply (simp add: comp_def)
by force

lemma fmap_lem_one: "fmap f {a} = {f a}"
  by (simp add: fmap_def fold_one)

(*
lemma fmapL_lem_one: "fmapL f {a} = [f a]"
  by (simp add: fmapL_def fold_one)
*)

lemma fmap_lem[rule_format]: "finite S \<Longrightarrow> \<forall> n. (fmap f (insert n S)) = (insert (f n) (fmap f S))"
  thm finite.induct
  apply (erule_tac F = S in finite_induct)
   apply (rule allI)
   apply (simp add: fmap_def)
   apply (rule fold_one)
(* *)
  apply (subgoal_tac "comp_fun_commute (\<lambda>x::'a. insert (f x))")
   apply (rule allI)
   apply (drule_tac x = x in spec)
   apply (erule ssubst)
   apply (subgoal_tac "fmap f (insert n (insert x F)) = insert (f n) (fmap f (insert x F))")
  apply (erule ssubst)
    apply (subgoal_tac "fmap f (insert x F) = insert (f x) (fmap f F)")
     apply simp
    apply (drule_tac A = "F" in Finite_Set.comp_fun_commute.fold_insert)
      apply assumption
     apply assumption
    apply (unfold fmap_def, assumption)
   apply (case_tac "n \<in> insert x F")
    defer
    apply (drule_tac A = "insert x F" in Finite_Set.comp_fun_commute.fold_insert)
     apply simp
  apply assumption+
  apply (simp add: comp_fun_commute_def)
  apply force
(* n \<in> insert x F *)
  apply (simp add: Finite_Set.comp_fun_commute.fold_rec)
  apply (subgoal_tac "Finite_Set.fold (\<lambda>x::'a. insert (f x)) {} (insert n (insert x F)) =
                     Finite_Set.fold (\<lambda>x::'a. insert (f x)) {} (insert x F)")
   prefer 2
   apply (subgoal_tac "insert n (insert x F) = insert x F")
    apply simp
  apply blast
  apply (erule ssubst)
  apply (rule Finite_Set.comp_fun_commute.fold_rec)
apply (simp add: comp_fun_commute_def)
   apply force
  by simp


lemma insert_delete: "x \<notin> S \<Longrightarrow> (insert x S) - {x} = S"
by simp

lemma fmap_lem_del[rule_format]: "finite S \<Longrightarrow> inj f \<Longrightarrow> \<forall> n \<in> S. fmap f (S - {n}) = (fmap f S) - {f n}"
  apply (erule_tac F = S in finite_induct)
   apply (rule ballI)
   apply (simp add: fmap_def)
(* *)
  apply (subgoal_tac "comp_fun_commute (\<lambda>x::'a. insert (f x))")
   apply (rule ballI)
apply simp
   apply (erule disjE)
(* n = x *)
    apply simp
    apply (drule_tac A = "F" and z = "{}" in Finite_Set.comp_fun_commute.fold_insert)
      apply assumption+
    apply (unfold fmap_def)
    apply (rotate_tac -1)
  apply (erule ssubst)
  apply (rule sym)
    apply (rule insert_delete)
    apply (erule contrapos_nn)
  apply (rule fmap_lem_map_rev, assumption, assumption)
  apply (simp add: fmap_def)
(* n \<in> F *)
    apply (frule_tac A = "F" and z = "{}" in Finite_Set.comp_fun_commute.fold_insert, assumption, assumption)
   apply (rotate_tac -1)
   apply (erule ssubst)
  apply (subgoal_tac "insert (f x) (Finite_Set.fold (\<lambda>x::'a. insert (f x)) {} F) - {f n} =
                      insert (f x) ((Finite_Set.fold (\<lambda>x::'a. insert (f x)) {} F) - {f n})")
   apply (rotate_tac -1)
   apply (erule ssubst)
   apply (drule_tac x = n in bspec,assumption)
   apply (rotate_tac -1)
   apply (erule subst)
    apply (drule_tac A = "F - {n}" and z = "{}" and x = x in Finite_Set.comp_fun_commute.fold_insert)
      apply simp+
    apply (subgoal_tac "insert x (F - {n}) = insert x F - {n}")
     apply simp
    apply blast
   apply (subgoal_tac "f x \<noteq> f n")
    apply force
   apply (subgoal_tac "x \<noteq> n")
  apply (rotate_tac -1)
  apply (erule contrapos_nn)
    apply (erule injD, assumption)
  apply blast
apply (simp add: comp_fun_commute_def)
by force


lemma fmap_lem_map_rev0[rule_format]: "finite S \<Longrightarrow> (\<forall>y\<in>S. f y \<noteq> f n) \<longrightarrow> (f n) \<in> (fmap f S) \<longrightarrow> n \<in> S"
  apply (erule_tac F = S in finite_induct)
   apply (simp add: fmap_def)
  apply clarify
  apply (simp add: fmap_def)
  apply (subgoal_tac "comp_fun_commute (\<lambda>x::'a. insert (f x))")
   apply (drule_tac A = "F" and z = "{}" in Finite_Set.comp_fun_commute.fold_insert)
     apply assumption+
   apply (subgoal_tac "f n \<in> insert (f x) (Finite_Set.fold (\<lambda>x::'a. insert (f x)) {} F)")
    prefer 2
    apply simp
   apply (subgoal_tac "f n = f x")
  apply simp
    apply simp
apply (simp add: comp_fun_commute_def)
by force

lemma fmap_lem_map_rev1: "finite S \<Longrightarrow> (\<forall>y\<in>S. f y \<noteq> f n) \<Longrightarrow> (f n) \<in> (fmap f S) \<Longrightarrow> n \<in> S"
  apply (erule fmap_lem_map_rev0)
  apply (drule bspec, assumption, assumption)
  by assumption

lemma fmap_lem_del_set1[rule_format]: "finite S \<Longrightarrow> 
                        \<forall> n \<in> S. fmap f (S - {y. f y = f n}) = (fmap f S) - {f n}"
  apply (erule_tac F = S in finite_induct)
   apply (rule ballI)
   apply (simp add: fmap_def)
(* *)
  apply (subgoal_tac "comp_fun_commute (\<lambda>x::'a. insert (f x))")
   apply (rule ballI)
   prefer 2
apply (simp add: comp_fun_commute_def)
   apply force
(* *)
  apply (case_tac "n = x")
   apply (simp add: fmap_def)
   apply (frule_tac A = "F" and z = "{}" in Finite_Set.comp_fun_commute.fold_insert)
     apply assumption+
   apply (rotate_tac -1)
  apply (erule ssubst)
(* *)
    apply simp
    apply (case_tac "\<exists> y \<in> F. f y = f x")
     apply (erule bexE)
     apply (drule_tac x = y in bspec, assumption)
     apply simp+
   apply (subgoal_tac "F - {y::'a. f y = f x} = F - {x}")
    prefer 2
  apply blast
  apply (rotate_tac -1)
  apply (erule ssubst)
   apply simp
  apply (subgoal_tac "(f x) \<notin> Finite_Set.fold (\<lambda>x::'a. insert (f x)) {} F ")
    apply simp
   apply (erule contrapos_nn)
   apply (rule fmap_lem_map_rev1, assumption, assumption)
   apply (simp add: fmap_def)
(* *)
  apply (subgoal_tac "n \<in> F")
   apply (drule_tac x = n in bspec, assumption)
  apply (frule_tac f = f and n = x in fmap_lem)
   apply (rotate_tac -1)
   apply (erule ssubst)
(* *)
  apply (case_tac "f x = f n")
    apply simp
  apply simp
   apply (subgoal_tac "insert (f x) (fmap f F) - {f n} = insert (f x) ((fmap f F) - {f n})")
    prefer 2
    apply force
  apply (rotate_tac -1)
   apply (erule ssubst)
   apply (subgoal_tac "insert x F - {y::'a. f y = f n} = insert x (F - {y::'a. f y = f n})")
    prefer 2
    apply force
  apply (rotate_tac -1)
   apply (erule ssubst)
   apply (subgoal_tac "finite (F - {y::'a. f y = f n})")
    apply (rotate_tac -1)
  apply (drule_tac S = "(F - {y::'a. f y = f n})" and f = f and n = x in fmap_lem)
    apply simp
   apply simp
by (simp add: comp_fun_commute_def)

(* In a similar vain: some simple summation on finite sets
definition fmap :: "['a \<Rightarrow> 'b, 'a set] \<Rightarrow> 'b set"
  where "fmap f S = Finite_Set.fold (\<lambda> x y. insert (f x) y) {} S"
*)
definition fsum :: "real set \<Rightarrow>  real"
  where "fsum S = Finite_Set.fold (\<lambda> x y. x + y) 0 S"

definition fsumap :: "['a \<Rightarrow> real, 'a set] \<Rightarrow> real"
  where "fsumap f S = Finite_Set.fold (\<lambda> x y. (f x) + y) (0 :: real) S"

lemma fsumap_fold_one: "Finite_Set.fold (\<lambda>x y. (f x) + y) (0 :: real) {n} = f n"
  thm Finite_Set.comp_fun_commute.fold_insert
  apply (subgoal_tac "comp_fun_commute (\<lambda>x. (+)(f x))")
   apply (drule_tac A = "{}" and z = 0 and x = n in Finite_Set.comp_fun_commute.fold_insert)
     apply simp+
  apply (simp add: comp_fun_commute_def)
  by force

lemma fsumap_lem[rule_format]: "finite S \<Longrightarrow> \<forall> n. n \<notin> S \<longrightarrow> (fsumap f (insert n S)) = (f n) + (fsumap f S)"
  thm finite.induct
  apply (erule_tac F = S in finite_induct)
   apply (rule allI)
   apply (simp add: fsumap_def)
   apply (rule fsumap_fold_one)
(* *)
  apply (subgoal_tac "comp_fun_commute (\<lambda>x. (+)(f x))")
   apply (rule allI, rule impI)
   apply (drule_tac x = x in spec)
  apply (drule mp, assumption)
   apply (erule ssubst)
  apply (subgoal_tac "fsumap f (insert n (insert x F)) = f n + (fsumap f (insert x F))")
    apply (erule ssubst)
    apply (subgoal_tac "fsumap f (insert x F) = (f x + fsumap f F)")
         apply simp
    apply (drule_tac A = "F" in Finite_Set.comp_fun_commute.fold_insert)
      apply assumption
     apply assumption
    apply (unfold fsumap_def, assumption)
   apply (case_tac "n \<in> insert x F")
    defer
    apply (drule_tac A = "insert x F" in Finite_Set.comp_fun_commute.fold_insert)
     apply simp
  apply assumption+
  apply (simp add: comp_fun_commute_def)
by force+
(* n \<in> insert x F is not possible 
  apply (subgoal_tac "Finite_Set.fold (\<lambda>x::'a. (+) (f x)) (0::real) (insert n (insert x F)) =
                      Finite_Set.fold (\<lambda>x::'a. (+) (f x)) (0::real) (insert x F)")
     prefer 2
   apply (subgoal_tac "insert n (insert x F) = insert x F")
    apply simp
  apply blast
  apply (erule ssubst)
  apply (simp add: Finite_Set.comp_fun_commute.fold_rec)
apply (simp add: comp_fun_commute_def)
   apply force
*)

primrec map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"
  where
   map_empty: "map f [] = []"
|  map_step: "map f (a # l) = (f a) #(map f l)"

definition lsum :: "real list \<Rightarrow> real"
  where "lsum rl \<equiv>  fold (\<lambda> x y. x + y) rl 0"

thm fold.simps
end