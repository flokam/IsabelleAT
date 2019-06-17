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
proof (rule_tac x = "(\<lambda> x :: 'O set. ((card x)::real)/((card (UNIV :: 'O set))::real))" in exI, rule CollectI, rule conjI)
  show " \<forall>A::'O set. (0::real) \<le> real (card A) / real (card UNIV)" by simp
next show "real (card (UNIV :: ('O :: finite) set)) / real (card (UNIV :: ('O :: finite)set)) = (1::real) \<and>
    (\<forall>(A::('O ::finite) set) B::('O::finite) set.
        A \<inter> B = {} \<longrightarrow>
        real (card (A \<union> B)) / real (card (UNIV :: ('O :: finite)set)) =
        real (card A) / real (card (UNIV :: ('O :: finite)set)) + 
        real (card B) / real (card (UNIV :: ('O :: finite)set)))"
    apply (rule conjI)
     apply simp
    apply clarify
    apply (subgoal_tac "real (card A) / real (card (UNIV :: ('O :: finite) set)) + 
                        real (card B) / real (card (UNIV :: ('O :: finite) set)) = 
                        (real (card A) + real (card B)) / real (card (UNIV :: ('O :: finite) set))")
    apply (rotate_tac -1)
     apply (erule ssubst)
     apply (subgoal_tac "real (card (A \<union> B)) = real (card A) + real (card B) ")
      apply (rotate_tac -1)
      apply (erule ssubst)
      apply (rule refl)
     apply (subgoal_tac "card (A \<union> B) = card A + card B")
      apply (rotate_tac -1)
      apply (erule ssubst)
    apply simp
     apply (simp add: card_Un_disjoint)
    apply (subgoal_tac "\<forall> (a::real) b c. c > 0 \<longrightarrow> a / c + b / c = (a + b) / c")
     apply (subgoal_tac "0 < real(card (UNIV :: ('O :: finite) set))")
      apply (drule_tac x = "real (card A)" in spec)
      apply (drule_tac x = "real (card B)" in spec)
        apply (drule_tac x = "real (card (UNIV :: ('O :: finite)set))" in spec)
    apply (drule mp)    
       apply simp+
     apply force
    by (simp add: add_divide_distrib)
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

(* some general techniques for mapping function on finite sets *)
(* general scheme for map over finite sets.
   This would be a useful provision for the Finite_Set library: everyone needs
   a simple map on Finite Sets all the time! *)
definition fmap :: "['a \<Rightarrow> 'b, 'a set] \<Rightarrow> 'b set"
  where "fmap f S = Finite_Set.fold (\<lambda> x y. insert (f x) y) {} S"

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

lemma fmap_lem_one: "fmap f {a} = {f a}"
by (simp add: fmap_def fold_one)


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

end