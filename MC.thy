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
by (simp add: monotone_def lfp_def)

lemma gfp1: "monotone \<tau> \<longrightarrow> (gfp \<tau> = \<Union> {Z. Z \<subseteq> \<tau> Z})"
by (simp add: monotone_def gfp_def)

primrec power :: "['a \<Rightarrow> 'a, nat] \<Rightarrow> ('a \<Rightarrow> 'a)" ("(_ ^ _)" 40)
where 
power_zero: "(f ^ 0) = (\<lambda> x. x)" |
power_suc: "(f ^ (Suc n)) = (f o (f ^ n))"

lemma predtrans_empty: 
  assumes "monotone \<tau>"
  shows "\<forall> i. (\<tau> ^ i) ({}) \<subseteq> (\<tau> ^(i + 1))({})"
proof (rule allI, induct_tac i)
  show "(\<tau> ^ 0::nat) {} \<subseteq> (\<tau> ^ (0::nat) + (1::nat)) {}" by simp
next show "\<And>(i::nat) n::nat. (\<tau> ^ n) {} \<subseteq> (\<tau> ^ n + (1::nat)) {} 
      \<Longrightarrow> (\<tau> ^ Suc n) {} \<subseteq> (\<tau> ^ Suc n + (1::nat)) {}"
  proof -
    fix i n
    assume a : " (\<tau> ^ n) {} \<subseteq> (\<tau> ^ n + (1::nat)) {}"
    have "(\<tau> ((\<tau> ^ n) {})) \<subseteq> (\<tau> ((\<tau> ^ (n + (1 :: nat))) {}))" using assms
      apply (rule monotoneE)
      by (rule a)
    thus "(\<tau> ^ Suc n) {} \<subseteq> (\<tau> ^ Suc n + (1::nat)) {}" by simp
  qed
qed

lemma ex_card: "finite S \<Longrightarrow> \<exists> n:: nat. card S = n"
by simp

lemma less_not_le: "\<lbrakk>(x:: nat) < y; y \<le> x\<rbrakk> \<Longrightarrow> False"
by arith

lemma infchain_outruns_all: 
  assumes "finite (UNIV :: 'a set)" 
    and "\<forall>i :: nat. (\<tau> ^ i) ({}:: 'a set) \<subset> (\<tau> ^ i + (1 :: nat)) {}"
  shows "\<forall>j :: nat. \<exists>i :: nat. j < card ((\<tau> ^ i) {})"
proof (rule allI, induct_tac j)
  show "\<exists>i::nat. (0::nat) < card ((\<tau> ^ i) {})" using assms   
    apply (drule_tac x = 0 in spec)
    apply (rule_tac x = 1 in exI)
    apply simp
    apply (subgoal_tac "card {} = 0")
    apply (erule subst)
    apply (rule psubset_card_mono)
    apply (rule_tac B = UNIV in finite_subset)
    apply simp
    apply assumption+
      by simp
  next show "\<And>(j::nat) n::nat. \<exists>i::nat. n < card ((\<tau> ^ i) {}) 
             \<Longrightarrow> \<exists>i::nat. Suc n < card ((\<tau> ^ i) {})"
    proof -
      fix j n
      assume a: "\<exists>i::nat. n < card ((\<tau> ^ i) {})"
      obtain i where "n < card ((\<tau> ^ (i :: nat)) {})" 
        apply (rule exE)
         apply (rule a)
        by simp
      thus "\<exists> i. Suc n < card ((\<tau> ^ i) {})" using assms
        apply (rule_tac x = "i + 1" in exI)
        apply (subgoal_tac "card((\<tau> ^ i) {}) < card((\<tau> ^ i + (1 :: nat)) {})")
        apply arith
        apply (rule psubset_card_mono)
        apply (rule_tac B = UNIV in finite_subset)
        apply simp
        apply (rule assms)
        by (erule spec)
    qed
  qed

lemma no_infinite_subset_chain: 
   assumes "finite (UNIV :: 'a set)"
    and    "monotone (\<tau> :: ('a set \<Rightarrow> 'a set))"
    and    "\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^ i) {} \<subset> (\<tau> ^ i + (1 :: nat)) ({} :: 'a set)" 
  shows   "False"
(* idea: Since UNIV is finite, we have from ex_card that there is
    an n with card UNIV = n. Now, use infchain_outruns_all to show as 
    contradiction point that
    \<exists>i\<Colon>nat. card UNIV < card ((\<tau> ^ i) {}). Since all sets
    are subsets of UNIV, we also have card ((\<tau> ^ i) {}) \<le> card UNIV:
    Contradiction!, i.e. proof of False  *)
proof -
  have a: "\<forall> (j :: nat). (\<exists> (i :: nat). (j :: nat) < card((\<tau> ^ i)({} :: 'a set)))" using assms
    apply (erule_tac \<tau> = \<tau> in infchain_outruns_all)
    by assumption
  hence b: "\<exists> (n :: nat). card(UNIV :: 'a set) = n" using assms
    by (erule_tac S = UNIV in ex_card)
  from this obtain n where c: "card(UNIV :: 'a set) = n" by (erule exE)
  hence   d: "\<exists>i::nat. card UNIV < card ((\<tau> ^ i) {})" using a
    apply (drule_tac x = "card UNIV" in spec)
    by assumption
  from this obtain i where e: "card (UNIV :: 'a set) < card ((\<tau> ^ i) {})"
    by (erule exE)
  hence f: "(card((\<tau> ^ i){})) \<le> (card (UNIV :: 'a set))" using assms
    thm Finite_Set.card_mono
      apply (rule_tac A = "((\<tau> ^ i){})" in Finite_Set.card_mono)
      apply assumption
    by (rule subset_UNIV)
  thus "False" using e
    thm less_not_le
    apply (erule_tac y = "card((\<tau> ^ i){})" in less_not_le)
    by assumption
qed

lemma finite_fixp: 
  assumes "finite(UNIV :: 'a set)" 
      and "monotone (\<tau> :: ('a set \<Rightarrow> 'a set))"
    shows "\<exists> i. (\<tau> ^ i) ({}) = (\<tau> ^(i + 1))({})"
(* idea: 
with predtrans_empty we know \<forall> i. (\<tau> ^ i) ({}) \<subseteq> (\<tau> ^(i + 1))({}) (1).
If we can additionally show \<exists> i.  (\<tau> ^ i) ({}) \<supseteq> (\<tau> ^(i + 1))({}) (2),
we can get the goal together with equalityI (\<subseteq> + \<supseteq> \<longrightarrow> =). To prove
(1) we observe that (\<tau> ^ i) ({}) \<supseteq> (\<tau> ^(i + 1))({}) can be inferred
from \<not> ( (\<tau> ^ i) ({}) \<subset> (\<tau> ^(i + 1))({})) and (1).
Finally, the latter is solved directly by no_infinite_subset_chain.
 *)
proof -
  have a: "\<forall>i::nat. (\<tau> ^ i) ({}:: 'a set) \<subseteq> (\<tau> ^ i + (1::nat)) {}" 
    thm predtrans_empty
    apply(rule predtrans_empty)
    by (rule assms(2))
  hence b: "(\<exists> i :: nat. \<not>((\<tau> ^ i) {} \<subset> (\<tau> ^(i + 1)) {}))" using assms
    apply (subgoal_tac "\<not> (\<forall> i :: nat. (\<tau> ^ i) {} \<subset> (\<tau> ^(i + 1)) {})")
    apply blast
    apply (rule notI)
    apply (rule no_infinite_subset_chain)
    by assumption
  thus "\<exists> i. (\<tau> ^ i) ({}) = (\<tau> ^(i + 1))({})" using a
    by blast
qed

lemma predtrans_UNIV: 
  assumes "monotone \<tau>"
  shows "\<forall> i. (\<tau> ^ i) (UNIV) \<supseteq> (\<tau> ^(i + 1))(UNIV)"
proof (rule allI, induct_tac i)
  show "(\<tau> ^ (0::nat) + (1::nat)) UNIV \<subseteq> (\<tau> ^ 0::nat) UNIV" by simp
next show "\<And>(i::nat) n::nat.
       (\<tau> ^ n + (1::nat)) UNIV \<subseteq> (\<tau> ^ n) UNIV \<Longrightarrow> (\<tau> ^ Suc n + (1::nat)) UNIV \<subseteq> (\<tau> ^ Suc n) UNIV"
  proof -
    fix i n
    assume a: "(\<tau> ^ n + (1::nat)) UNIV \<subseteq> (\<tau> ^ n) UNIV"
    have "(\<tau> ((\<tau> ^ n) UNIV)) \<supseteq> (\<tau> ((\<tau> ^ (n + (1 :: nat))) UNIV))" using assms
      apply (rule monotoneE)
      by (rule a)
    thus "(\<tau> ^ Suc n + (1::nat)) UNIV \<subseteq> (\<tau> ^ Suc n) UNIV" by simp
   qed
 qed

lemma Suc_less_le: "x < (y - n) \<Longrightarrow> x \<le> (y - (Suc n))"
 by simp

lemma card_univ_subtract: 
  assumes "finite (UNIV :: 'a set)" and  "monotone (\<tau> :: 'a set \<Rightarrow> 'a set)"
     and  "(\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^ i + (1 :: nat)) (UNIV :: 'a set) \<subset> (\<tau> ^ i) UNIV)"
   shows "(\<forall> i :: nat. card((\<tau> ^ i) (UNIV ::'a set)) \<le> (card (UNIV :: 'a set)) - i)"
proof (rule allI, induct_tac i) 
  show "card ((\<tau> ^ 0::nat) UNIV) \<le> card (UNIV :: 'a set) - (0::nat)" using assms
    by (simp)
next show "\<And>(i::nat) n::nat.
       card ((\<tau> ^ n) (UNIV :: 'a set)) \<le> card (UNIV :: 'a set) - n \<Longrightarrow>
       card ((\<tau> ^ Suc n) (UNIV :: 'a set)) \<le> card (UNIV :: 'a set) - Suc n" using assms
  proof -
    fix i n
    assume a: "card ((\<tau> ^ n) (UNIV :: 'a set)) \<le> card (UNIV :: 'a set) - n"
    have b: "(\<tau> ^ n + (1::nat)) (UNIV :: 'a set) \<subset> (\<tau> ^ n) UNIV" using assms
      by (erule_tac x = n in spec)
    have "card((\<tau> ^ n + (1 :: nat)) (UNIV :: 'a set)) < card((\<tau> ^ n) (UNIV :: 'a set))" 
      apply (rule psubset_card_mono)
      apply (rule finite_subset) 
      apply (rule subset_UNIV)
       apply (rule assms(1))
      by (rule b)
    thus "card ((\<tau> ^ Suc n) (UNIV :: 'a set)) \<le> card (UNIV :: 'a set) - Suc n" using a
      by simp
    qed
  qed

lemma card_UNIV_tau_i_below_zero: 
  assumes "finite (UNIV :: 'a set)" and "monotone (\<tau> :: 'a set \<Rightarrow> 'a set)"
   and  "(\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^ i + (1 :: nat)) (UNIV :: 'a set) \<subset> (\<tau> ^ i) UNIV)"
 shows "card((\<tau> ^ (card (UNIV ::'a set))) (UNIV ::'a set)) \<le> 0"
proof -
  have "(\<forall> i :: nat. card((\<tau> ^ i) (UNIV ::'a set)) \<le> (card (UNIV :: 'a set)) - i)" using assms
    by (rule card_univ_subtract)
  thus "card((\<tau> ^ (card (UNIV ::'a set))) (UNIV ::'a set)) \<le> 0"
   apply (drule_tac x = "card (UNIV ::'a set)" in spec)
    by simp
qed

lemma finite_card_zero_empty: "\<lbrakk> finite S; card S \<le> 0\<rbrakk> \<Longrightarrow> S = {}"
by simp

lemma UNIV_tau_i_is_empty:
  assumes "finite (UNIV :: 'a set)" and "monotone (\<tau> :: 'a set \<Rightarrow> 'a set)"
    and   "(\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^ i + (1 :: nat)) (UNIV :: 'a set) \<subset> (\<tau> ^ i) UNIV)"
  shows "(\<tau> ^ (card (UNIV ::'a set))) (UNIV ::'a set) = {}"
proof - 
  have "card ((\<tau> ^ card (UNIV ::'a set)) UNIV) \<le> (0::nat)" using assms
    apply (rule card_UNIV_tau_i_below_zero) 
    .
  thus "(\<tau> ^ (card (UNIV ::'a set))) (UNIV ::'a set) = {}" using assms
    apply (rule_tac S = "(\<tau> ^ (card (UNIV ::'a set))) (UNIV ::'a set)" in finite_card_zero_empty)
    apply (rule finite_subset)
    apply (rule subset_UNIV)
    .
qed


lemma down_chain_reaches_empty:
  assumes "finite (UNIV :: 'a set)" and "monotone (\<tau> :: 'a set \<Rightarrow> 'a set)"
   and "(\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^ i + (1 :: nat)) UNIV \<subset> (\<tau> ^ i) UNIV)"
 shows "\<exists> (j :: nat). (\<tau> ^ j) UNIV = {}"
proof -
  have "(\<tau> ^ ((card (UNIV :: 'a set)))) UNIV = {}" using assms
    apply (rule UNIV_tau_i_is_empty)
    .
  thus "\<exists> (j :: nat). (\<tau> ^ j) UNIV = {}" 
    by (rule exI)
qed

lemma no_infinite_subset_chain2: 
  assumes "finite (UNIV :: 'a set)" and "monotone (\<tau> :: ('a set \<Rightarrow> 'a set))"
      and "\<forall>i :: nat. (\<tau> ^ i) UNIV \<supset> (\<tau> ^ i + (1 :: nat)) UNIV"
  shows "False"
proof -
  have "\<exists> j :: nat. (\<tau> ^ j) UNIV = {}" using assms
    apply (rule down_chain_reaches_empty)
    .
  from this obtain j where a: "(\<tau> ^ j) UNIV = {}" by (erule exE)
  have "(\<tau> ^ j + (1::nat)) UNIV \<subset> (\<tau> ^ j) UNIV" using assms
    by (erule_tac x = j in spec)
  thus False using a by simp 
qed

lemma finite_fixp2: 
  assumes "finite(UNIV :: 'a set)" and "monotone (\<tau> :: ('a set \<Rightarrow> 'a set))"
  shows "\<exists> i. (\<tau> ^ i) UNIV = (\<tau> ^(i + 1)) UNIV"
proof -
  have "\<forall>i::nat. (\<tau> ^ i + (1::nat)) UNIV \<subseteq> (\<tau> ^ i) UNIV" 
    apply (rule predtrans_UNIV) using assms
    by (simp add: assms(2))
  moreover have "\<exists>i::nat. \<not> (\<tau> ^ i + (1::nat)) UNIV \<subset> (\<tau> ^ i) UNIV" using assms
  proof -
    have "\<not> (\<forall> i :: nat. (\<tau> ^ i) UNIV \<supset> (\<tau> ^(i + 1)) UNIV)" 
      apply (rule notI) 
      apply (rule no_infinite_subset_chain2) using assms
      .
    thus "\<exists>i::nat. \<not> (\<tau> ^ i + (1::nat)) UNIV \<subset> (\<tau> ^ i) UNIV" by blast
  qed
  ultimately show "\<exists> i. (\<tau> ^ i) UNIV = (\<tau> ^(i + 1)) UNIV" 
    by blast
qed

lemma mono_monotone: "mono (\<tau> :: ('a set \<Rightarrow> 'a set)) \<Longrightarrow> monotone \<tau>"
by (simp add: monotone_def mono_def)

lemma monotone_mono: "monotone (\<tau> :: ('a set \<Rightarrow> 'a set)) \<Longrightarrow> mono \<tau>"
by (simp add: monotone_def mono_def)

lemma power_power: "((\<tau> :: ('a set \<Rightarrow> 'a set)) ^^ n) = ((\<tau> :: ('a set \<Rightarrow> 'a set)) ^ n)"
proof (induct_tac n)
  show "\<tau> ^^ (0::nat) = (\<tau> ^ 0::nat)" by (simp add: id_def)
next show "\<And>n::nat. \<tau> ^^ n = (\<tau> ^ n) \<Longrightarrow> \<tau> ^^ Suc n = (\<tau> ^ Suc n)"
    by simp
qed

lemma lfp_Kleene_iter_set: "monotone (f :: ('a set \<Rightarrow> 'a set)) \<Longrightarrow>
   (f ^ Suc(n)) {} = (f ^ n) {} \<Longrightarrow> lfp f  = (f ^ n){}"
by (simp add: monotone_mono lfp_Kleene_iter power_power)

lemma lfp_loop: 
  assumes "finite (UNIV :: 'b set)" and "monotone (\<tau> :: ('b set \<Rightarrow> 'b set))"
  shows "\<exists> n . lfp \<tau>  = (\<tau> ^ n) {}"
proof -
  have "\<exists>i::nat. (\<tau> ^ i) {} = (\<tau> ^ i + (1::nat)) {}"  using assms
    by (rule finite_fixp)
  from this obtain i where " (\<tau> ^ i) {} = (\<tau> ^ i + (1::nat)) {}"
    by (erule exE)
  hence "(\<tau> ^ i) {} = (\<tau> ^ Suc i) {}"
    by simp
  hence "(\<tau> ^ Suc i) {} = (\<tau> ^ i) {}"
    by (rule sym)
  hence "lfp \<tau> = (\<tau> ^ i) {}"
     by (simp add: assms(2) lfp_Kleene_iter_set)
   thus   "\<exists> n . lfp \<tau>  = (\<tau> ^ n) {}" 
   by (rule exI) 
qed

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

lemma gfp_Kleene_iter_set: 
  assumes "monotone (f :: ('a set \<Rightarrow> 'a set))"
      and "(f ^ Suc(n)) UNIV = (f ^ n) UNIV"
    shows "gfp f  = (f ^ n) UNIV"
proof -
  have a: "mono f" using assms
    by (erule_tac \<tau> = f in monotone_mono)
  hence b: "(f ^^ Suc (n)) UNIV = (f ^^ n) UNIV" using assms
    by (simp add: power_power)
  hence c: "gfp f = (f ^^ (n))(UNIV :: 'a set)" using assms a
    thm gfp_Kleene_iter
    apply (erule_tac f = f and k = n in gfp_Kleene_iter)
    .
  thus "gfp f = (f ^ (n))(UNIV :: 'a set)" using assms a
    by (simp add: power_power)
qed    
    
lemma gfp_loop: 
  assumes "finite (UNIV :: 'b set)"
   and "monotone (\<tau> :: ('b set \<Rightarrow> 'b set))"
    shows "\<exists> n . gfp \<tau>  = (\<tau> ^ n)(UNIV :: 'b set)"
proof -
  have " \<exists>i::nat. (\<tau> ^ i)(UNIV :: 'b set) = (\<tau> ^ i + (1::nat)) UNIV" using assms
    by (rule finite_fixp2)
  from this obtain i where "(\<tau> ^ i)(UNIV :: 'b set) = (\<tau> ^ i + (1::nat)) UNIV" by (erule exE)
  thus "\<exists> n . gfp \<tau>  = (\<tau> ^ n)(UNIV :: 'b set)" using assms
    apply (rule_tac x = i in exI)
    apply (rule gfp_Kleene_iter_set) 
    apply assumption
    apply (rule sym)
    by simp
qed


(* Definitions of the generic type of state with state transition and CTL Operators*)
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

(* Kripke and Modelchecking  -- FIXME:  typedef to incorporate init K \<subseteq> states K *)
datatype 'a kripke = 
  Kripke "'a set" "'a set"

primrec states where "states (Kripke S I) = S" 
primrec init where "init (Kripke S I) = I" 

definition check ("_ \<turnstile> _" 50)
 where "M \<turnstile> f \<equiv> (init M) \<subseteq> {s \<in> (states M). s \<in> f }"

definition state_transition_refl ("(_ \<rightarrow>\<^sub>i* _)" 50)
where "s \<rightarrow>\<^sub>i* s' \<equiv> ((s,s') \<in> {(x,y). state_transition x y}\<^sup>*)"
  
(* Support lemmas *)
lemma EF_lem0: "(x \<in> EF f) = (x \<in> f \<union> EX' (lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z)))"
proof -
  have "lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z) = 
                    f \<union> (EX' (lfp (\<lambda>Z :: 'a set. f \<union> EX' Z)))"
    apply (rule def_lfp_unfold)
    apply (rule reflexive)
    apply (unfold mono_def EX'_def)
    by auto
  thus "(x \<in> EF (f :: ('a :: state) set)) = (x \<in> f \<union> EX' (lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z)))"
    by (simp add: EF_def) 
qed
    
lemma EF_lem00: "(EF f) = (f \<union> EX' (lfp (\<lambda> Z :: ('a :: state) set. f \<union> EX' Z)))"
proof (rule equalityI)
  show "EF f \<subseteq> f \<union> EX' (lfp (\<lambda>Z::'a set. f \<union> EX' Z))"
   apply (rule subsetI)
   by (simp add: EF_lem0)
  next show "f \<union> EX' (lfp (\<lambda>Z::'a set. f \<union> EX' Z)) \<subseteq> EF f"
   apply (rule subsetI)
   by (simp add: EF_lem0)
 qed

lemma EF_lem000: "(EF f) = (f \<union> EX' (EF f))"
proof (subst EF_lem00)
  show "f \<union> EX' (lfp (\<lambda>Z::'a set. f \<union> EX' Z)) = f \<union> EX' (EF f)"
    apply (fold EF_def)  
    by (rule refl)
qed

lemma EF_lem1: "x \<in> f \<or> x \<in> (EX' (EF f)) \<Longrightarrow> x \<in> EF f"
proof (simp add: EF_def)
  assume a: "x \<in> f \<or> x \<in> EX' (lfp (\<lambda>Z::'a set. f \<union> EX' Z))"
  show "x \<in> lfp (\<lambda>Z::'a set. f \<union> EX' Z)"
  proof -
    have b: "lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z) =
                    f \<union> (EX' (lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z)))"
      apply (rule def_lfp_unfold)
      apply (rule reflexive)
      apply (unfold mono_def EX'_def)
      by auto
    thus "x \<in> lfp (\<lambda>Z::'a set. f \<union> EX' Z)" using a
     apply (subst b)
     by blast
 qed
qed

lemma EF_lem2b: 
    assumes "x \<in> (EX' (EF f))"
   shows "x \<in> EF f"
proof (rule EF_lem1)
  show "x \<in> f \<or> x \<in> EX' (EF f)" 
    apply (rule disjI2)
    by (rule assms)
qed

lemma EF_lem2a: assumes "x \<in> f" shows "x \<in> EF f"
proof (rule EF_lem1)
  show "x \<in> f \<or> x \<in> EX' (EF f)"
    apply (rule disjI1)
    by (rule assms)
qed

lemma EF_lem2c: assumes "x \<notin> f" shows "x \<in> EF (- f)"
proof -
  have "x \<in> (- f)" using assms
    by simp
  thus "x \<in> EF (- f)"
    by (rule EF_lem2a)
qed

lemma EF_lem2d: assumes "x \<notin> EF f" shows "x \<notin> f"
proof -
  have "x \<in> f \<Longrightarrow> x \<in> EF f" 
    by (erule EF_lem2a)
  thus "x \<notin> f" using assms
    thm contrapos_nn
    apply (erule_tac P = "x \<in> f" in contrapos_nn)
    apply (erule meta_mp)
    .
qed

lemma EF_lem3b: assumes "x \<in> EX' (f \<union> EX' (EF f))" shows "x \<in> (EF f)"
proof (simp add: EF_lem0)
  show "x \<in> f \<or> x \<in> EX' (lfp (\<lambda>Z::'a set. f \<union> EX' Z))" 
   apply (rule disjI2)
   apply (fold EF_def)
   apply (subst EF_lem00)
   apply (fold EF_def)
   by (rule assms)
qed

lemma EX_lem0l: "x \<in> (EX' f) \<Longrightarrow> x \<in> (EX' (f \<union> g))"
proof (unfold EX'_def)
  show "x \<in> {s::'a. \<exists>f0::'a\<in>f. s \<rightarrow>\<^sub>i f0} \<Longrightarrow> x \<in> {s::'a. \<exists>f0::'a\<in>f \<union> g. s \<rightarrow>\<^sub>i f0}"
    by blast
qed

lemma EX_lem0r: "x \<in> (EX' g) \<Longrightarrow> x \<in> (EX' (f \<union> g))"
proof (unfold EX'_def)
  show "x \<in> {s::'a. \<exists>f0::'a\<in>g. s \<rightarrow>\<^sub>i f0} \<Longrightarrow> x \<in> {s::'a. \<exists>f0::'a\<in>f \<union> g. s \<rightarrow>\<^sub>i f0}"
    by blast
qed

lemma EX_step: assumes "x  \<rightarrow>\<^sub>i y" and "y \<in> f" shows "x \<in> EX' f"
proof (unfold EX'_def)
  show " x \<in> {s::'a. \<exists>f0::'a\<in>f. s \<rightarrow>\<^sub>i f0}" 
    apply simp
    apply (rule_tac x = y in bexI)
    by (rule assms)+
qed

lemma EF_E[rule_format]: "\<forall> f. x \<in> (EF (f :: ('a :: state) set)) \<longrightarrow> x \<in> (f \<union> EX' (EF f))"
proof -
  have a: "\<And>f::'a set. EF (f :: ('a :: state) set) = f \<union> EX' (EF f)"
    by (rule EF_lem000)
  thus "(\<forall> f. x \<in> EF (f :: ('a :: state) set) \<longrightarrow> x \<in> f \<union> EX' (EF f))" 
    apply (rule_tac P = "(\<lambda> f. x \<in> EF (f :: ('a :: state) set) \<longrightarrow> x \<in> f \<union> EX' (EF f))" in allI)
    apply (subst a) 
    apply (rule impI)
    by assumption
qed

lemma EF_step: assumes "x  \<rightarrow>\<^sub>i y" and "y \<in> f" shows "x \<in> EF f"
proof (rule EF_lem3b)
  show "x \<in> EX' (f \<union> EX' (EF f))" 
    apply (rule EX_step)
    apply (rule assms(1))
    by (simp add: assms(2))
qed

lemma EF_step_step: assumes "x  \<rightarrow>\<^sub>i y" and "y \<in> EF f" shows  "x \<in> EF f"
proof -
  have "y \<in> f \<union> EX' (EF f)"
    apply (rule EF_E)
    by (rule assms(2))
  thus "x \<in> EF f"
    apply (rule_tac x = x and f = f in EF_lem3b)
    apply (rule EX_step)
    by (rule assms)
qed

lemma EF_step_star: "\<lbrakk> x  \<rightarrow>\<^sub>i* y; y \<in> f \<rbrakk> \<Longrightarrow> x \<in> EF f"
proof (simp add: state_transition_refl_def)
  show "(x, y) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y}\<^sup>* \<Longrightarrow> y \<in> f \<Longrightarrow> x \<in> EF f"
  proof (erule converse_rtrancl_induct)
    show "y \<in> f \<Longrightarrow> y \<in> EF f" 
      by (erule EF_lem2a)
    next show "\<And>(ya::'a) z::'a. y \<in> f \<Longrightarrow>
                 (ya, z) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y} \<Longrightarrow>
                 (z, y) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y}\<^sup>* \<Longrightarrow> z \<in> EF f \<Longrightarrow> ya \<in> EF f"
        apply (clarify)
        apply (erule EF_step_step)
        by assumption
    qed
  qed

lemma EF_induct_prep: 
  assumes "(a::'a::state) \<in> lfp (\<lambda> Z. (f::'a::state set) \<union> EX' Z)"
       and "mono  (\<lambda> Z. (f::'a::state set) \<union> EX' Z)"
     shows "(\<And>x::'a::state.
     x \<in> ((\<lambda> Z. (f::'a::state set) \<union> EX' Z)(lfp (\<lambda> Z. (f::'a::state set) \<union> EX' Z) \<inter> {x::'a::state. (P::'a::state \<Rightarrow> bool) x})) \<Longrightarrow> P x) \<Longrightarrow>
      P a"
proof -
  show "(\<And>x::'a::state.
     x \<in> ((\<lambda> Z. (f::'a::state set) \<union> EX' Z)(lfp (\<lambda> Z. (f::'a::state set) \<union> EX' Z) \<inter> {x::'a::state. (P::'a::state \<Rightarrow> bool) x})) \<Longrightarrow> P x) \<Longrightarrow>
      P a"
    apply (rule_tac A = "EF f" in def_lfp_induct_set)
    apply (rule EF_def)
    apply (rule assms(2))
    by (simp add: EF_def assms)+
qed

lemma EF_induct: "(a::'a::state) \<in> EF (f :: 'a :: state set) \<Longrightarrow>
    mono  (\<lambda> Z. (f::'a::state set) \<union> EX' Z) \<Longrightarrow>
    (\<And>x::'a::state.
        x \<in> ((\<lambda> Z. (f::'a::state set) \<union> EX' Z)(EF f \<inter> {x::'a::state. (P::'a::state \<Rightarrow> bool) x})) \<Longrightarrow> P x) \<Longrightarrow>
    P a"
proof (simp add: EF_def)
  show "a \<in> lfp (\<lambda>Z::'a set. f \<union> EX' Z) \<Longrightarrow>
    mono (\<lambda>Z::'a set. f \<union> EX' Z) \<Longrightarrow>
    (\<And>x::'a. x \<in> f \<or> x \<in> EX' (lfp (\<lambda>Z::'a set. f \<union> EX' Z) \<inter> Collect P) \<Longrightarrow> P x) \<Longrightarrow> P a"
    apply (erule EF_induct_prep)
    apply assumption
  by simp
qed

lemma valEF_E: "M \<turnstile> EF f \<Longrightarrow> x \<in> init M \<Longrightarrow> x \<in> EF f"
proof (simp add: check_def) 
  show "init M \<subseteq> {s::'a \<in> states M. s \<in> EF f} \<Longrightarrow> x \<in> init M \<Longrightarrow> x \<in> EF f"
   apply (drule subsetD)
   apply assumption
    by simp
qed

lemma EF_step_star_rev[rule_format]: "x \<in> EF s \<Longrightarrow>  (\<exists> y \<in> s.  x  \<rightarrow>\<^sub>i* y)"
proof (erule EF_induct)
  show "mono (\<lambda>Z::'a set. s \<union> EX' Z)"
    apply (simp add: mono_def EX'_def)
    by force
next show "\<And>x::'a. x \<in> s \<union> EX' (EF s \<inter> {x::'a. \<exists>y::'a\<in>s. x \<rightarrow>\<^sub>i* y}) \<Longrightarrow> \<exists>y::'a\<in>s. x \<rightarrow>\<^sub>i* y"
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
qed

lemma EF_step_inv: "(I \<subseteq> {sa::'s :: state. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF s})  
         \<Longrightarrow> \<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y"
proof (clarify)
  show "\<And>x::'s. I \<subseteq> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF s} \<Longrightarrow> x \<in> I \<Longrightarrow> \<exists>y::'s\<in>s. x \<rightarrow>\<^sub>i* y"
    apply (drule subsetD)
    apply assumption
    apply (drule CollectD)
    apply (erule conjE)
    by (erule EF_step_star_rev)
qed
  
(* AG lemmas *)  

lemma AG_in_lem:   "x \<in> AG s \<Longrightarrow> x \<in> s"  
proof (simp add: AG_def gfp_def)
  show "\<exists>xa\<subseteq>s. xa \<subseteq> AX xa \<and> x \<in> xa \<Longrightarrow> x \<in> s"
    apply (erule exE)
    apply (erule conjE)+
    by (erule subsetD, assumption)
qed

lemma AG_lem1: "x \<in> s \<and> x \<in> (AX (AG s)) \<Longrightarrow> x \<in> AG s"
proof (simp add: AG_def)
  show "x \<in> s \<and> x \<in> AX (gfp (\<lambda>Z::'a set. s \<inter> AX Z)) \<Longrightarrow> x \<in> gfp (\<lambda>Z::'a set. s \<inter> AX Z)"
  apply (subgoal_tac "gfp (\<lambda>Z::'a set. s \<inter> AX Z) =
                      s \<inter> (AX (gfp (\<lambda>Z::'a set. s \<inter> AX Z)))")
  apply (erule ssubst)
  apply simp
  apply (rule def_gfp_unfold)
  apply (rule reflexive)
  apply (unfold mono_def AX_def)
  by auto
qed

lemma AG_lem2: "x \<in> AG s \<Longrightarrow> x \<in> (s \<inter> (AX (AG s)))"
proof -
  have a: "AG s = s \<inter> (AX (AG s))"
    apply (simp add: AG_def)
    apply (rule def_gfp_unfold)
    apply (rule reflexive)
    apply (unfold mono_def AX_def)
    by auto
  thus "x \<in> AG s \<Longrightarrow> x \<in> (s \<inter> (AX (AG s)))"
   by (erule subst)
qed

lemma AG_lem3: "AG s = (s \<inter> (AX (AG s)))"    
proof (rule equalityI) 
  show "AG s \<subseteq> s \<inter> AX (AG s)"
    apply (rule subsetI)
    by (erule AG_lem2)
  next show "s \<inter> AX (AG s) \<subseteq> AG s"
    apply (rule subsetI)
    apply (rule AG_lem1)
    by simp
qed

lemma AG_step: "y \<rightarrow>\<^sub>i z \<Longrightarrow> y \<in> AG s \<Longrightarrow> z \<in> AG s"  
proof (drule AG_lem2)
  show "y \<rightarrow>\<^sub>i z \<Longrightarrow> y \<in> s \<inter> AX (AG s) \<Longrightarrow> z \<in> AG s"
    apply (erule IntE)
    apply (unfold AX_def)
    apply simp
    apply (erule subsetD)
    by simp
qed

lemma AG_all_s: " x \<rightarrow>\<^sub>i* y \<Longrightarrow> x \<in> AG s \<Longrightarrow> y \<in> AG s"
proof (simp add: state_transition_refl_def)
  show "(x, y) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y}\<^sup>* \<Longrightarrow> x \<in> AG s \<Longrightarrow> y \<in> AG s"
    apply (erule rtrancl_induct) 
  proof -
    show "x \<in> AG s \<Longrightarrow> x \<in> AG s" by assumption
  next show "\<And>(y::'a) z::'a.
       x \<in> AG s \<Longrightarrow>
       (x, y) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y}\<^sup>* \<Longrightarrow> 
       (y, z) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y} \<Longrightarrow> y \<in> AG s \<Longrightarrow> z \<in> AG s"
      apply clarify
      by (erule AG_step, assumption)
  qed
qed

lemma AG_imp_notnotEF: 
"I \<noteq> {} \<Longrightarrow> ((Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> AG s)) \<Longrightarrow> 
 (\<not>(Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF (- s)))"
proof (rule notI, simp add: check_def)
  assume a0: "I \<noteq> {}" and
    a1: "I \<subseteq> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s}" and
    a2: "I \<subseteq> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)}" 
  show "False"
  proof - 
    have a3: "{sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s} \<inter>
                        {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)} = {}"
      proof -
        have "(? x. x \<in> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s} \<and>
                           x \<in> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)}) \<Longrightarrow> False"
        proof -
          assume a4: "(? x. x \<in> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s} \<and>
                           x \<in> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)})"          
            from a4 obtain x where  a5: "x \<in> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s} \<and>
                                   x \<in> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)}"
            by (erule exE) 
            hence "x \<in> s \<and> x \<in> -s"
            proof -
              have a6: "x \<in> s" using a5
                apply (subgoal_tac "x \<in> AG s")
                apply (erule AG_in_lem)
                by simp
              moreover have "x \<in> -s" using a5
              proof -
                have "x \<in> EF s" 
                  apply (rule_tac y = x in EF_step_star)
                  apply (simp add: state_transition_refl_def)
                  by (rule a6)                  
                thus "x \<in> -s" using a5
                proof -
                  have "x \<in> EF (- s)" using a5
                    by simp
                  moreover from this obtain y where a7: "y \<in> - s \<and> x \<rightarrow>\<^sub>i* y" 
                    apply (rotate_tac -1)
                     apply (drule EF_step_star_rev)
                    by blast
                  moreover have "y \<in> AG s" using a7 a5
                    apply (subgoal_tac "x \<in> AG s")
                    apply (erule conjE)
                     apply (drule AG_all_s)
                      apply assumption+
                    by simp
                  ultimately show "x \<in> -s" using a5
                     apply (rotate_tac -1)
                     apply (drule AG_in_lem)
                     by blast
                qed
              qed
              ultimately show "x \<in> s \<and> x \<in> -s"
                by (rule conjI)
            qed
            thus "False"
              by blast
          qed
        thus "{sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s} \<inter>
                        {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)} = {}"
        by blast
      qed
    moreover have b: "? x. x : I" using a0
      by blast
    moreover obtain x where "x \<in> I" 
        apply (rule exE)
         apply (rule b)
      by simp
    ultimately show "False" using a0 a1 a2
      by blast
  qed
qed

lemma check2_def: "(Kripke S I \<turnstile> f) = (I \<subseteq> S \<inter> f)"
proof (simp add: check_def)
  show "(I \<subseteq> {s::'a \<in> S. s \<in> f}) = (I \<subseteq> S \<and> I \<subseteq> f)" by blast
qed
    
end