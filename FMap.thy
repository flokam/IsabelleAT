theory FMap
  imports AT Complex_Main
begin

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


lemma fmap_empty1: "(fmap f {} = S) \<Longrightarrow> (S = {})"
  by (simp add: fmap_def)

lemma fmap_empty2: "S = {} \<Longrightarrow> fmap f {} = S"
  by (simp add: fmap_def)

lemma fmap_empty: "(fmap f {} = S) = (S = {})"
proof  
  show "fmap f {} = S \<Longrightarrow> S = {}"
    by (erule fmap_empty1)
next show  "S = {} \<Longrightarrow> fmap f {} = S"
    by (erule fmap_empty2)
qed

lemma fmap_empty3: "fmap f {} = {}"
  by (simp add: fmap_def)

lemma fmap_empty4[rule_format]: "finite S \<Longrightarrow> fmap f S = {} \<longrightarrow> S = {}"
  apply (erule_tac F = S in finite_induct)
  apply simp
  apply (simp add: fmap_def)
  apply (subgoal_tac "Finite_Set.fold (\<lambda>x::'a. insert (f x)) {} ({x}) \<noteq> {}")
  apply (subgoal_tac "Finite_Set.fold (\<lambda>x::'a. insert (f x)) {} ({x}) \<subseteq> 
                      Finite_Set.fold (\<lambda>x::'a. insert (f x)) {} (insert x F)")
    apply blast
  apply (subst fold_one)
   apply (subgoal_tac "comp_fun_commute (\<lambda>x::'a. insert (f x))")
  thm Finite_Set.comp_fun_commute.fold_insert
   apply (drule_tac A = "F" and z = "{}" in Finite_Set.comp_fun_commute.fold_insert)
     apply simp
     apply simp
  apply (erule ssubst)
    apply simp
     apply (simp add: comp_fun_commute_def)
     apply force
    apply (subst fold_one)
  by simp


lemma insert_delete0: "x \<in> A \<Longrightarrow> A = insert x (A - {x})"
  by auto

lemma fmap_inj[rule_format]: 
  assumes "finite S" and "inj f"
  shows "\<forall> S'. finite S' \<longrightarrow> fmap f S = fmap f S' \<longrightarrow> S = S'"
  using assms
proof (erule_tac F = S in finite_induct, clarify)
  show "\<And>S'::'a set. inj f \<Longrightarrow> finite S \<Longrightarrow> inj f \<Longrightarrow> finite S' \<Longrightarrow> 
        fmap f {} = fmap f S' \<Longrightarrow> {} = S'"
    apply (rule sym)
    apply (rule_tac f = f in fmap_empty4)
    apply assumption
by (erule fmap_empty1)
next show "\<And>(x::'a) F::'a set.
       inj f \<Longrightarrow>
       finite F \<Longrightarrow>
       x \<notin> F \<Longrightarrow>
       \<forall>S'::'a set. finite S' \<longrightarrow> fmap f F = fmap f S' \<longrightarrow> F = S' \<Longrightarrow>
       \<forall>S'::'a set. finite S' \<longrightarrow> fmap f (insert x F) = fmap f S' \<longrightarrow> insert x F = S'"
  proof (clarify)
    fix x F S'
    assume a0: "inj f"
       and a1: "finite F"
       and a1a: "x \<notin> F"
       and a2: "\<forall>S'::'a set. finite S' \<longrightarrow> fmap f F = fmap f S' \<longrightarrow> F = S'"
       and a3: "finite S'"
       and a4: "fmap f (insert x F) = fmap f S'"
    show "insert x F = S'"
    proof -
      have a5: "insert (f x) (fmap f F) = fmap f S'" 
        by (insert fmap_lem[of F f x], drule meta_mp, rule a1, erule subst, rule a4) 
      have a6: "f x \<in> fmap f S'" by (insert a5, erule subst, simp)
      have a6a: "x \<in> S'" by (rule fmap_lem_map_rev, rule a3, rule a0, rule a6)
      have a7: "fmap f S' = insert (f x) ((fmap f S') - {f x})" 
        by (insert insert_delete0[of "f x" "(fmap f S')"],drule meta_mp, rule a6)
      have a8: "insert (f x) (fmap f F) = insert (f x) ((fmap f S') - {f x})" 
        by (subst a5, subst a7, rule refl)
      have a9: "f x \<notin> (fmap f F)" using a0 a1 a1a
        apply (rule_tac P = "f x \<in> fmap f F" in notI, subgoal_tac "x \<in> F")
          apply (rule notE, rule a1a, assumption)
        by (rule fmap_lem_map_rev)
      have a10: "f x \<notin> ((fmap f S') - {f x})" by simp
      have a11: "fmap f F = ((fmap f S') - {f x})" by (insert a8 a9 a10, force) 
      have a12: "x \<in> S' \<Longrightarrow> fmap f F = fmap f (S' - {x})" 
        apply (insert fmap_lem_del[of S' f x])
        apply (drule meta_mp)
         apply (rule a3)
        apply (drule meta_mp)
         apply (rule a0)
        apply (drule meta_mp, assumption)
        apply (erule ssubst)
        by (rule a11)
(*      have a13: "x \<notin> S' \<Longrightarrow> f x \<notin> fmap f S'" 
        by (erule contrapos_nn, rule fmap_lem_map_rev, rule a3, rule a0)
      have a14: "x \<notin> S' \<Longrightarrow> fmap f F = (fmap f S')" 
        by (insert a13, drule meta_mp, assumption, subst a11, simp) *)
      show "insert x F = S'"
        apply (insert a6a)
         apply (insert a2)
         apply (drule_tac x = "S' - {x}" in spec)
         apply (drule mp)
          apply (simp add: a3)
         apply (drule mp)
          apply (erule a12)
         apply (erule ssubst)
        apply (rule sym)
        by (erule insert_delete0)
    qed
  qed
qed

lemma fmap_inj0: "inj f \<Longrightarrow> inj_on (fmap f){S. finite S}"
  apply (rule inj_onI)
  apply (rule fmap_inj)
  by simp+




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

lemma fmap_set_rep_lem[rule_format]: "finite S \<Longrightarrow> 
        S \<noteq> {} \<longrightarrow> x \<in> Finite_Set.fold (\<lambda>x::'a. insert (f x)) {} S \<longrightarrow> (\<exists>y::'a\<in>S. x = f y)"
  apply (erule_tac F = S in finite_induct)
   apply simp
  apply (case_tac "F = {}")
   apply (simp add: fold_one)
  apply simp
  by (metis (full_types) empty_iff fold_infinite image_fold_insert image_insert insert_iff)



lemma fmap_set_rep[rule_format]: "finite S \<Longrightarrow>  fmap f S = {x. \<exists> y \<in> S. x = f y}"
proof (rule equalityI, rule subsetI, rule CollectI)
  show "\<And>x::'b. finite S \<Longrightarrow> x \<in> fmap f S \<Longrightarrow> \<exists>y::'a\<in>S. x = f y"
    apply (simp add: fmap_def)
    apply (case_tac "S = {}")
     apply simp
    by (simp add: fmap_set_rep_lem)
next show "finite S \<Longrightarrow> {x::'b. \<exists>y::'a\<in>S. x = f y} \<subseteq> fmap f S"
    apply (rule subsetI)
    apply (drule CollectD)
    apply (erule bexE)
    apply (erule ssubst)
  by (erule fmap_lem_map, assumption)
qed

lemma fmap_set_rep'[rule_format]: "finite S \<Longrightarrow>  fmap f S = f `S"
proof (subst fmap_set_rep, assumption, simp add: image_def)
qed

lemma fmap_set_del_set0[rule_format]: "finite S \<Longrightarrow>
   \<forall> S'.  inj_on f S \<longrightarrow> S' \<subseteq> S \<longrightarrow> f ` S - f ` S' = f ` (S - S')"
  apply (erule_tac F = S in finite_induct)
   apply simp
  by (metis Diff_subset inj_on_image_set_diff)

thm inj_on_image_set_diff
thm fmap_def

lemma fmap_set_del_set1[rule_format]: "inj_on f S \<Longrightarrow> S' \<subseteq> S 
        \<Longrightarrow> f ` S - f ` S' = f ` (S - S')"
  by (metis Diff_subset inj_on_image_set_diff)

lemma fmap_set_del_set: "finite S \<Longrightarrow> inj_on f S \<Longrightarrow>
    S' \<subseteq> S \<Longrightarrow> fmap f S - fmap f S' = fmap f (S - S')" 
  apply (subst fmap_set_rep', assumption)
  apply (subst fmap_set_rep')
   apply (erule finite_subset, assumption)
  apply (subst fmap_set_rep')
  apply (rule_tac A = "S - S'" and B = S in finite_subset)
  apply blast
  apply assumption
by (erule fmap_set_del_set0)

lemma fmap_set_del_set: "finite S \<Longrightarrow> inj f \<Longrightarrow>
    finite S' \<Longrightarrow>  fmap f S - fmap f S' = fmap f (S - S')" 
  apply (subst fmap_set_rep', assumption)
  apply (subst fmap_set_rep', assumption)
  apply (subst fmap_set_rep')
  apply simp

apply (erule fmap_set_del_set0)
  oops


lemma image_inj[rule_format]: "inj f \<Longrightarrow> f ` S = f ` S' \<Longrightarrow> S = S'"
  by (simp add: inj_image_eq_iff)




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

end