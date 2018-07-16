theory MC 
imports Main
begin
declare [[show_types]]

thm monotone_def
definition monotone :: "('a set \<Rightarrow> 'a set) \<Rightarrow> bool"
where "monotone \<tau> \<equiv> (\<forall> p q. p \<subseteq> q \<longrightarrow> \<tau> p \<subseteq> \<tau> q )"

lemma monotoneE: "monotone \<tau> \<Longrightarrow> p \<subseteq> q \<Longrightarrow> \<tau> p \<subseteq> \<tau> q"
by (simp add: monotone_def)

lemma lfp1: "monotone \<tau> \<longrightarrow> (lfp \<tau> = \<Inter> {Z. \<tau> Z \<subseteq> Z})"
apply (simp add: monotone_def lfp_def)
done

lemma gfp1: "monotone \<tau> \<longrightarrow> (gfp \<tau> = \<Union> {Z. Z \<subseteq> \<tau> Z})"
apply (simp add: monotone_def gfp_def)
done

primrec power :: "['a \<Rightarrow> 'a, nat] \<Rightarrow> ('a \<Rightarrow> 'a)" ("(_ ^ _)" 40)
where 
power_zero: "(f ^ 0) = (\<lambda> x. x)" |
power_suc: "(f ^ (Suc n)) = (f o (f ^ n))"

lemma predtrans_empty: "monotone \<tau> \<Longrightarrow> \<forall> i. (\<tau> ^ i) ({}) \<subseteq> (\<tau> ^(i + 1))({})"
apply (rule allI)
apply (induct_tac i)
apply simp
apply (subgoal_tac "(\<tau> ((\<tau> ^ n) {})) \<subseteq> (\<tau> ((\<tau> ^ (n + (1 :: nat))) {}))")
apply simp
apply (erule monotoneE)
by assumption

lemma ex_card: "finite S \<Longrightarrow> \<exists> n:: nat. card S = n"
by simp

lemma less_not_le: "\<lbrakk>(x:: nat) < y; y \<le> x\<rbrakk> \<Longrightarrow> False"
by arith

lemma infchain_outruns_all: "\<lbrakk> finite (UNIV :: 'a set) \<rbrakk> \<Longrightarrow>
\<forall>i :: nat. (\<tau> ^ i) ({}:: 'a set) \<subset> (\<tau> ^ i + (1 :: nat)) {} \<Longrightarrow> \<forall>j :: nat. \<exists>i :: nat. j < card ((\<tau> ^ i) {})"
apply (rule allI)
apply (induct_tac j)
apply (drule_tac x = 0 in spec)
apply (rule_tac x = 1 in exI)
apply simp
apply (subgoal_tac "card {} = 0")
apply (erule subst)
apply (rule psubset_card_mono)
apply (rule_tac B = UNIV in finite_subset)
apply simp
apply assumption+
apply simp
(* step *)
apply (erule exE)
apply (rule_tac x = "i + 1" in exI)
apply (drule_tac x = i in spec)
apply (subgoal_tac "card((\<tau> ^ i) {}) < card((\<tau> ^ i + (1 :: nat)) {})")
apply arith
apply (rule psubset_card_mono)
apply (rule_tac B = UNIV in finite_subset)
apply simp
by assumption

lemma no_infinite_subset_chain: "\<lbrakk> finite (UNIV :: 'a set); 
       monotone (\<tau> :: ('a set \<Rightarrow> 'a set));
        \<forall>i :: nat. (\<tau> ^ i) {} \<subset> (\<tau> ^ i + (1 :: nat)) {} \<rbrakk> \<Longrightarrow> False"

(* idea: Since UNIV is finite, we have from ex_card that there is
    an n with card UNIV = n. Now, use infchain_outruns_all to show as 
    contradiction point that
    \<exists>i\<Colon>nat. card UNIV < card ((\<tau> ^ i) {}). Since all sets
    are subsets of UNIV, we also have card ((\<tau> ^ i) {}) \<le> card UNIV:
    Contradiction!, i.e. proof of False  *)
apply (subgoal_tac "\<forall> (j :: nat). (\<exists> (i :: nat). j < card((\<tau> ^ i){}))")
apply (subgoal_tac "\<exists> n. card(UNIV :: 'a set) = n")
defer
apply (erule ex_card)
apply (erule infchain_outruns_all)
apply assumption
apply (erule exE)
apply (rotate_tac -2)
apply (drule_tac x = "card UNIV" in spec)
apply (erule exE)
apply (subgoal_tac "(card((\<tau> ^ i){})) \<le> (card UNIV)")
apply (erule less_not_le)
apply assumption
(* *)
apply (rule Finite_Set.card_mono)
apply assumption
by (rule subset_UNIV)

lemma finite_fixp: "\<lbrakk> finite(UNIV :: 'a set); monotone (\<tau> :: ('a set \<Rightarrow> 'a set))\<rbrakk>
                     \<Longrightarrow> \<exists> i. (\<tau> ^ i) ({}) = (\<tau> ^(i + 1))({})"
(* idea: 
with predtrans_empty we know \<forall> i. (\<tau> ^ i) ({}) \<subseteq> (\<tau> ^(i + 1))({}) (1).
If we can additionally show \<exists> i.  (\<tau> ^ i) ({}) \<supseteq> (\<tau> ^(i + 1))({}) (2),
we can get the goal together with equalityI (\<subseteq> + \<supseteq> \<longrightarrow> =). To prove
(1) we observe that (\<tau> ^ i) ({}) \<supseteq> (\<tau> ^(i + 1))({}) can be inferred
from \<not> ( (\<tau> ^ i) ({}) \<subset> (\<tau> ^(i + 1))({})) and (1).
Finally, the latter is solved directly by no_infinite_subset_chain.
 *)
apply (frule predtrans_empty)
apply (subgoal_tac "(\<exists> i :: nat. \<not>((\<tau> ^ i) {} \<subset> (\<tau> ^(i + 1)) {}))")
apply blast
(*
apply (erule exE)
apply (rule_tac x = i in exI)
apply (rule equalityI)
apply simp
apply (subgoal_tac "(\<tau> ^ i) {} \<subset> (\<tau> ^ i + (1\<Colon>nat)) {} \<or>  (\<tau> ^ i) {} = (\<tau> ^ i + (1\<Colon>nat)) {}") 
apply (erule disjE)
apply (erule notE)
apply assumption
apply (erule subst)
apply (rule subset_refl)
apply (fold subset_iff_psubset_eq)
apply (erule spec)
*)
(* reformulate goal to better fit no_infinite_subset_chain *)
apply (subgoal_tac "\<not> (\<forall> i :: nat. (\<tau> ^ i) {} \<subset> (\<tau> ^(i + 1)) {})")
apply blast
apply (rule notI)
apply (rule no_infinite_subset_chain)
by assumption

lemma predtrans_UNIV: "monotone \<tau> \<Longrightarrow> \<forall> i. (\<tau> ^ i) (UNIV) \<supseteq> (\<tau> ^(i + 1))(UNIV)"
apply (rule allI)
apply (induct_tac i)
apply simp
apply (subgoal_tac "(\<tau> ((\<tau> ^ n) UNIV)) \<supseteq> (\<tau> ((\<tau> ^ (n + (1 :: nat))) UNIV))")
apply simp
apply (erule monotoneE)
by assumption

lemma card_univ_subtract: "\<lbrakk> finite (UNIV :: 'a set); monotone (\<tau> :: 'a set \<Rightarrow> 'a set);
 (\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^ i + (1 :: nat)) (UNIV :: 'a set) \<subset> (\<tau> ^ i) UNIV)\<rbrakk>
 \<Longrightarrow> (\<forall> i :: nat. card((\<tau> ^ i) (UNIV ::'a set)) \<le> (card (UNIV :: 'a set)) - i)"
apply (rule allI)
apply (induct_tac i)
apply simp
(* step *)
apply (drule_tac x = n in spec)
thm psubset_card_mono
apply (subgoal_tac "card((\<tau> ^ n + (1 :: nat)) UNIV) < card((\<tau> ^ n) UNIV)")
apply simp
apply (rule psubset_card_mono)
apply (rule finite_subset) 
apply (rule subset_UNIV)
by assumption

lemma card_UNIV_tau_i_below_zero: "\<lbrakk> finite (UNIV :: 'a set); monotone (\<tau> :: 'a set \<Rightarrow> 'a set);
 (\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^ i + (1 :: nat)) (UNIV :: 'a set) \<subset> (\<tau> ^ i) UNIV)\<rbrakk>
 \<Longrightarrow> card((\<tau> ^ (card (UNIV ::'a set))) (UNIV ::'a set)) \<le> 0"
apply (frule card_univ_subtract)
apply assumption+
apply (rotate_tac -1)
apply (drule_tac x = "card (UNIV ::'a set)" in spec)
by simp

lemma finite_card_zero_empty: "\<lbrakk> finite S; card S \<le> 0\<rbrakk> \<Longrightarrow> S = {}"
by simp

lemma UNIV_tau_i_is_empty: "\<lbrakk> finite (UNIV :: 'a set); monotone (\<tau> :: 'a set \<Rightarrow> 'a set);
 (\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^ i + (1 :: nat)) (UNIV :: 'a set) \<subset> (\<tau> ^ i) UNIV)\<rbrakk>
 \<Longrightarrow> (\<tau> ^ (card (UNIV ::'a set))) (UNIV ::'a set) = {}"
apply (rule finite_card_zero_empty)
apply (rule finite_subset)
apply (rule subset_UNIV)
apply assumption
apply (rule card_UNIV_tau_i_below_zero)
by assumption

lemma down_chain_reaches_empty':
 "\<lbrakk>finite (UNIV :: 'a set); monotone (\<tau> :: 'a set \<Rightarrow> 'a set);
   (\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^ i + (1 :: nat)) UNIV \<subset> (\<tau> ^ i) UNIV)\<rbrakk>
  \<Longrightarrow> (\<exists> (j :: nat). (\<tau> ^ j) UNIV = {})"
apply (rule_tac x = "(card (UNIV :: 'a set))" in exI)
apply (rule UNIV_tau_i_is_empty)
by assumption


lemma no_infinite_subset_chain2: "\<lbrakk> finite (UNIV :: 'a set); 
       monotone (\<tau> :: ('a set \<Rightarrow> 'a set));
        \<forall>i :: nat. (\<tau> ^ i) UNIV \<supset> (\<tau> ^ i + (1 :: nat)) UNIV \<rbrakk> \<Longrightarrow> False"
(* idea: if UNIV is finite, there is a j such that (\<tau> ^ j) UNIV = {}.
   Then (\<tau> ^ (j + 1)) UNIV \<subset> (\<tau> ^ j) UNIV = {} contradiction *)
apply (subgoal_tac "\<exists> j :: nat. (\<tau> ^ j) UNIV = {}")
apply (erule exE)
apply (drule_tac x = j in spec)
apply (subgoal_tac "(\<tau> ^ j + (1 :: nat)) UNIV \<subset> {}")
apply simp
apply (erule subst)
apply assumption
(* lemma  
\<forall>i :: nat. (\<tau> ^ i + (1\<Colon>nat)) UNIV \<subset> (\<tau> ^ i) UNIV \<Longrightarrow> \<exists>j :: nat. (\<tau> ^ j) UNIV = {} *)
apply (rule down_chain_reaches_empty')
apply assumption+
(* by (erule spec) *)
done

lemma finite_fixp2: "\<lbrakk> finite(UNIV :: 'a set); monotone (\<tau> :: ('a set \<Rightarrow> 'a set))\<rbrakk>
                     \<Longrightarrow> \<exists> i. (\<tau> ^ i) UNIV = (\<tau> ^(i + 1)) UNIV"
(*similar to the {} case *)
apply (frule predtrans_UNIV)
apply (subgoal_tac "(\<exists> i :: nat. \<not>((\<tau> ^ i) UNIV \<supset> (\<tau> ^(i + 1)) UNIV))")
apply blast
(* *)
apply (subgoal_tac "\<not> (\<forall> i :: nat. (\<tau> ^ i) UNIV \<supset> (\<tau> ^(i + 1)) UNIV)")
apply blast
apply (rule notI)
apply (rule no_infinite_subset_chain2)
by assumption


lemma mono_monotone: "mono (\<tau> :: ('a set \<Rightarrow> 'a set)) \<Longrightarrow> monotone \<tau>"
by (simp add: monotone_def mono_def)

lemma monotone_mono: "monotone (\<tau> :: ('a set \<Rightarrow> 'a set)) \<Longrightarrow> mono \<tau>"
by (simp add: monotone_def mono_def)

lemma power_power: "((\<tau> :: ('a set \<Rightarrow> 'a set)) ^^ n) = ((\<tau> :: ('a set \<Rightarrow> 'a set)) ^ n)"
apply (induct_tac n)
apply simp
by simp

lemma empty_bot: "bot = {}"
by (rule refl)

declare [[show_sorts]]
lemma lfp_Kleene_iter_set: "monotone (f :: ('a set \<Rightarrow> 'a set)) \<Longrightarrow>
   (f ^ Suc(n)) {} = (f ^ n) {} \<Longrightarrow> lfp f  = (f ^ n){}"
apply (drule monotone_mono)
thm lfp_Kleene_iter
apply (drule lfp_Kleene_iter)
by (simp add: power_power)+   

lemma lfp_loop: "\<lbrakk> finite (UNIV :: 'b set) ; monotone (\<tau> :: ('b set \<Rightarrow> 'b set)) 
                 \<rbrakk> \<Longrightarrow> \<exists> n . lfp \<tau>  = (\<tau> ^ n) {}"
apply (frule finite_fixp)
apply assumption
apply (erule exE)
apply (rule_tac x = i in exI)
apply (rule lfp_Kleene_iter_set) 
apply assumption
apply (rule sym)
by simp

(* These next two are produced as duals from the corresponding
   theorems in HOL/ZF/Nat.thy. Why are they not in the HOL/Library? *)
lemma Kleene_iter_gpfp:
assumes "mono f" and "p \<le> f p" shows "p \<le> (f^^k) (top::'a::order_top)"
proof(induction k)
  case 0 show ?case by simp
next
  case Suc
  from monoD[OF assms(1) Suc] assms(2)
  show ?case by simp
qed

lemma gfp_Kleene_iter: assumes "mono f" and "(f^^Suc k) top = (f^^k) top"
shows "gfp f = (f^^k) top"
proof(rule antisym)
  show "(f^^k) top \<le> gfp f"
  proof(rule gfp_upperbound)
    show "(f^^k) top \<le> f ((f^^k) top) " using assms(2) by simp
  qed
next
  show "gfp f \<le> (f^^k) top"
    using Kleene_iter_gpfp[OF assms(1)] gfp_unfold[OF assms(1)] by simp
qed

lemma gfp_Kleene_iter_set: "monotone (f :: ('a set \<Rightarrow> 'a set)) \<Longrightarrow>
   (f ^ Suc(n)) UNIV = (f ^ n) UNIV \<Longrightarrow> gfp f  = (f ^ n) UNIV"
apply (drule monotone_mono)
apply (drule gfp_Kleene_iter)
by (simp add: power_power)+   

(* lemma finiteS\<and>monotone\<tau> −\<rightarrow>(\<exists>m.gfp\<tau> =\<tau>^mS) *)
lemma gfp_loop: "\<lbrakk> finite (UNIV :: 'b set) ; monotone (\<tau> :: ('b set \<Rightarrow> 'b set)) 
                 \<rbrakk> \<Longrightarrow> \<exists> n . gfp \<tau>  = (\<tau> ^ n)(UNIV :: 'b set)"
apply (frule finite_fixp2)
apply assumption
apply (erule exE)
apply (rule_tac x = i in exI)
apply (rule gfp_Kleene_iter_set) 
apply assumption
apply (rule sym)
by simp

(* Definitions of the CTL Operators *)
(*
class state = 
  fixes state_transition :: "['a :: type, 'a] \<Rightarrow> bool"  ("(_ \<rightarrow>\<^sub>i _)" 50)
*)
(*  
class finite =
  assumes finite_Univ : "finite (UNIV)"
*)
(* temporarily changed class type to class finite *)    
class state = 
  fixes state_transition :: "['a :: type, 'a] \<Rightarrow> bool"  ("(_ \<rightarrow>\<^sub>i _)" 50)

    
definition AX where "AX f \<equiv> {s. {f0. s \<rightarrow>\<^sub>i f0} \<subseteq> f}"
definition EX' where "EX' f \<equiv> {s . \<exists> f0 \<in> f. s \<rightarrow>\<^sub>i f0 }"

definition AF where "AF f \<equiv> lfp (\<lambda> Z. f \<union> AX Z)"
definition EF where "EF f \<equiv> lfp (\<lambda> Z. f \<union> EX' Z)"
definition AG where "AG f \<equiv> gfp (\<lambda> Z. f \<inter> AX Z)"
definition EG where "EG f \<equiv> gfp (\<lambda> Z. f \<inter> EX' Z)"
definition AU where "AU f1 f2 \<equiv> lfp(\<lambda> Z. f2 \<union> (f1 \<inter> AX Z))"
definition EU where "EU f1 f2 \<equiv> lfp(\<lambda> Z. f2 \<union> (f1 \<inter> EX' Z))"
definition AR where "AR f1 f2 \<equiv> gfp(\<lambda> Z. f2 \<inter> (f1 \<union> AX Z))"
definition ER where "ER f1 f2 \<equiv> gfp(\<lambda> Z. f2 \<inter> (f1 \<union> EX' Z))"

(* Kripke and MC *)
datatype 'a kripke = 
  Kripke "'a set" "'a set"

primrec states where "states (Kripke S I) = S" 
primrec init where "init (Kripke S I) = I" 

(*  
definition L where "L I \<equiv> \<exists> l a c. enables I l a c"
*)

definition check ("_ \<turnstile> _" 50)
 where "M \<turnstile> f \<equiv> (init M) \<subseteq> {s \<in> (states M). s \<in> f }"


definition state_transition_refl ("(_ \<rightarrow>\<^sub>i* _)" 50)
where "s \<rightarrow>\<^sub>i* s' \<equiv> ((s,s') \<in> {(x,y). state_transition x y}\<^sup>*)"

  
(* support *)
lemma EF_lem0: "(x \<in> EF f) = (x \<in> f \<union> EX' (lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z)))"

apply (subgoal_tac "lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z) = 
                    f \<union> (EX' (lfp (\<lambda>Z :: 'a set. f \<union> EX' Z)))")
apply (rule iffI)
apply (simp add: EF_def) 
apply (simp add: EF_def) 
apply (rule def_lfp_unfold)
apply (rule reflexive)
apply (unfold mono_def EX'_def)
by auto

lemma EF_lem00: "(EF f) = (f \<union> EX' (lfp (\<lambda> Z :: ('a :: state) set. f \<union> EX' Z)))"
apply (rule equalityI)
apply (rule subsetI)
apply (simp add: EF_lem0)
apply (rule subsetI)
by (simp add: EF_lem0)

lemma EF_lem000: "(EF f) = (f \<union> EX' (EF f))"
apply (subst EF_lem00)
apply (fold EF_def)  
by (rule refl)

lemma EF_lem1: "x \<in> f \<or> x \<in> (EX' (EF f)) \<Longrightarrow> x \<in> EF f"
apply (simp add: EF_def) 
apply (subgoal_tac "lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z) = 
                    f \<union> (EX' (lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z)))")
apply (erule ssubst)
apply simp
apply (rule def_lfp_unfold)
apply (rule reflexive)
apply (unfold mono_def EX'_def)
by auto

lemma EF_lem2b: "x \<in> (EX' (EF f)) \<Longrightarrow> x \<in> EF f"
apply (rule EF_lem1)
by (erule disjI2)

lemma EF_lem2a: "x \<in> f \<Longrightarrow> x \<in> EF f"
apply (rule EF_lem1)
  by (erule disjI1)

lemma EF_lem2c: "x \<notin> f \<Longrightarrow> x \<in> EF (- f)"
  apply (subgoal_tac "x \<in> (- f)")
  prefer 2
   apply simp
by (erule EF_lem2a)
    
lemma EF_lem2d: "x \<notin> EF f \<Longrightarrow> x \<notin> f"
  apply (erule contrapos_nn)
  by (erule EF_lem2a)
    

(* not true     
lemma EF_lem2b: "x \<in> EF f \<longrightarrow> x \<in> f"
    apply (subst EF_lem000)
*)

lemma EF_lem3b: "x \<in> EX' (f \<union> EX' (EF f)) \<Longrightarrow> x \<in> (EF f)"
apply (simp add: EF_lem0)
apply (rule disjI2)
apply (fold EF_def)
apply (subst EF_lem00)
apply (fold EF_def)
by assumption

lemma EX_lem0l: "x \<in> (EX' f) \<Longrightarrow> x \<in> (EX' (f \<union> g))"
apply (unfold EX'_def)
by blast

lemma EX_lem0r: "x \<in> (EX' g) \<Longrightarrow> x \<in> (EX' (f \<union> g))"
apply (unfold EX'_def)
by blast

lemma EX_step: "\<lbrakk> x  \<rightarrow>\<^sub>i y; y \<in> f \<rbrakk> \<Longrightarrow> x \<in> EX' f"
apply (unfold EX'_def)
apply simp
apply (rule_tac x = y in bexI)
by (assumption)+

lemma EF_E[rule_format]: "\<forall> f. x \<in> (EF (f :: ('a :: state) set)) \<longrightarrow> x \<in> (f \<union> EX' (EF f))"
  apply (insert EF_lem000)
  apply (rule allI)
  apply (drule_tac x = f in meta_spec)
  apply (erule subst)  
  apply (rule impI)
      by assumption
      
  
lemma EF_step: "\<lbrakk> x  \<rightarrow>\<^sub>i y; y \<in> f \<rbrakk> \<Longrightarrow> x \<in> EF f"
  apply (rule EF_lem3b)
    apply (erule EX_step)
  by simp
    
lemma EF_step_step: "\<lbrakk> x  \<rightarrow>\<^sub>i y; y \<in> EF f \<rbrakk> \<Longrightarrow> x \<in> EF f"
  apply (drule EF_E)
  apply (rule EF_lem3b)
  apply (erule EX_step)
by (assumption)

    
lemma EF_step_star: "\<lbrakk> x  \<rightarrow>\<^sub>i* y; y \<in> f \<rbrakk> \<Longrightarrow> x \<in> EF f"
  apply (simp add: state_transition_refl_def)
  apply (rule mp)
   prefer 2
   apply (rotate_tac -1)
   apply assumption
  apply (erule converse_rtrancl_induct)
   apply clarify
    apply (erule EF_lem2a)
  apply (clarify)
  apply (erule EF_step_step)
  by assumption

lemma EF_induct_prep: "(a::'a::state) \<in> lfp (\<lambda> Z. (f::'a::state set) \<union> EX' Z) \<Longrightarrow>
    mono  (\<lambda> Z. (f::'a::state set) \<union> EX' Z) \<Longrightarrow>
    (\<And>x::'a::state.
        x \<in> ((\<lambda> Z. (f::'a::state set) \<union> EX' Z)(lfp (\<lambda> Z. (f::'a::state set) \<union> EX' Z) \<inter> {x::'a::state. (P::'a::state \<Rightarrow> bool) x})) \<Longrightarrow> P x) \<Longrightarrow>
    P a"
  apply (rule_tac A = "EF f" in def_lfp_induct_set)
     apply (rule EF_def)
    apply assumption
   by (simp add: EF_def)+
    
lemma EF_induct: "(a::'a::state) \<in> EF (f :: 'a :: state set) \<Longrightarrow>
    mono  (\<lambda> Z. (f::'a::state set) \<union> EX' Z) \<Longrightarrow>
    (\<And>x::'a::state.
        x \<in> ((\<lambda> Z. (f::'a::state set) \<union> EX' Z)(EF f \<inter> {x::'a::state. (P::'a::state \<Rightarrow> bool) x})) \<Longrightarrow> P x) \<Longrightarrow>
    P a"
apply (simp add: EF_def)  
  apply (erule EF_induct_prep)
    apply assumption
  by simp
    
lemma valEF_E: "M \<turnstile> EF f \<Longrightarrow> x \<in> init M \<Longrightarrow> x \<in> EF f"
  apply (simp add: check_def)     
    apply (drule subsetD)
   apply assumption
  by simp
    
lemma valEFI: " \<forall> x \<in> init M. x \<in> EF f \<Longrightarrow> M \<turnstile> EF f"
  apply (simp add: check_def)
    apply (rule subsetI)
  apply (drule_tac x = x in bspec)
   apply assumption
  apply (rule CollectI)
  apply (simp add: init_def)
    oops
    
lemma EF_step_star_rev[rule_format]: "x \<in> EF s \<Longrightarrow>  (\<exists> y \<in> s.  x  \<rightarrow>\<^sub>i* y)"
  apply (erule EF_induct)
   apply (simp add: mono_def EX'_def)
   apply force
  apply (erule UnE)
   apply (rule_tac x = x in bexI)
    apply (simp add: state_transition_refl_def)
   apply assumption
  apply (simp add: EX'_def)
  apply (erule bexE)
  apply (erule IntE)
  apply (drule CollectD)
  apply (erule bexE)
  apply (rule_tac x = xb in bexI)
   apply (simp add: state_transition_refl_def)
   apply (rule rtrancl_trans)
    apply (rule r_into_rtrancl)
    apply (rule CollectI)
    apply simp
  by assumption+
    
      
lemma EF_step_inv: "(I \<subseteq> {sa::'s :: state. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF s})  
         \<Longrightarrow> \<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y"
  apply clarify
apply (drule subsetD)
   apply assumption
  apply (drule CollectD)
  apply (erule conjE)
by (erule EF_step_star_rev)
 
  
(* AG lemmas *)  
  
 lemma AG_in_lem:   "x \<in> AG s \<Longrightarrow> x \<in> s"  
  apply (simp add: AG_def)
  apply (simp add: gfp_def)
  apply (erule exE)
  apply (erule conjE)+
by (erule subsetD, assumption)
 

lemma AG_lem1: "x \<in> s \<and> x \<in> (AX (AG s)) \<Longrightarrow> x \<in> AG s"
  apply (simp add: AG_def)
  apply (subgoal_tac "gfp (\<lambda>Z::'a set. s \<inter> AX Z) =
                      s \<inter> (AX (gfp (\<lambda>Z::'a set. s \<inter> AX Z)))")
      apply (erule ssubst)
   apply simp
  apply (rule def_gfp_unfold)
    apply (rule reflexive)
  apply (unfold mono_def AX_def)
  by auto

lemma AG_lem2: "x \<in> AG s \<Longrightarrow> x \<in> (s \<inter> (AX (AG s)))"
  apply (subgoal_tac "AG s = s \<inter> (AX (AG s))")
   apply (erule subst)
   apply assumption
   apply (simp add: AG_def)
  apply (rule def_gfp_unfold)
    apply (rule reflexive)
  apply (unfold mono_def AX_def)
  by auto
    
lemma AG_lem3: "AG s = (s \<inter> (AX (AG s)))"    
  apply (rule equalityI)  
  apply (rule subsetI)
   apply (erule AG_lem2)
    apply (rule subsetI)
  apply (rule AG_lem1)
  by simp
    
lemma AG_step: "y \<rightarrow>\<^sub>i z \<Longrightarrow> y \<in> AG s \<Longrightarrow> z \<in> AG s"  
apply (drule AG_lem2)
  apply (erule IntE)
  apply (unfold AX_def)
  apply simp
  apply (erule subsetD)
 by simp
    
lemma AG_all_s: " x \<rightarrow>\<^sub>i* y \<Longrightarrow> x \<in> AG s \<Longrightarrow> y \<in> AG s"
    apply (simp add: state_transition_refl_def)
  apply (rule mp)
   prefer 2
   apply (rotate_tac -1)
   apply assumption
  apply (erule rtrancl_induct)
   apply (rule impI, assumption)
  apply clarify
by (erule AG_step, assumption)

  
lemma AG_imp_notnotEF: 
"I \<noteq> {} \<Longrightarrow> ((Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> AG s)) \<Longrightarrow> 
 (\<not>(Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF (- s)))"
  apply (rule notI)
   apply (simp add: check_def)
    apply (subgoal_tac "{sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s} \<inter>
                        {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)} = {}")
  apply (subgoal_tac "? x. x : I")
     apply (erule exE)
     apply blast
    apply blast
  apply (subgoal_tac "(? x. x \<in> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s} \<and>
                           x \<in> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)}) \<Longrightarrow> False")
    apply blast
    apply (erule exE)
   apply (erule conjE)
   apply (subgoal_tac "x \<in> s")
    apply (subgoal_tac "x \<in> - s")
     apply blast
  prefer 2
  apply (subgoal_tac "x \<in> AG s")
    apply (erule AG_in_lem)
    apply simp
   apply (subgoal_tac "x \<in> EF s")
  prefer 2
    apply (rule EF_step_star)
     prefer 2
     apply assumption
    apply (simp add: state_transition_refl_def)
   apply (subgoal_tac "x \<in> EF (- s)")
  prefer 2
    apply simp
   apply (rotate_tac -1)
   apply (drule EF_step_star_rev)
   apply (erule bexE) 
    apply (subgoal_tac "x \<in> AG s")
    apply (drule AG_all_s)
     apply assumption
  apply (rotate_tac -1)
    apply (drule AG_in_lem)
    apply blast
by simp
  
      
lemma check2_def: "(Kripke S I \<turnstile> f) = (I \<subseteq> S \<inter> f)"
  apply (simp add: check_def)
by blast
 
    
end