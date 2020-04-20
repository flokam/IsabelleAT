section "Attack Trees"
theory AT
imports MC 
begin

text \<open>Attack Trees are an intuitive and practical formal method to analyse and quantify
attacks on security and privacy. They are very useful to identify the steps an attacker
takes through a system when approaching the attack goal. Here, we provide 
a proof calculus to analyse concrete attacks using a notion of attack validity.
We define a state based semantics with Kripke models and the temporal logic
CTL in the proof assistant Isabelle \cite{npw:02} using its Higher Order Logic 
(HOL). We prove the correctness and completeness (adequacy) of Attack Trees in Isabelle 
with respect to the model.\<close>


subsection "Attack Tree datatype"
text \<open>The following datatype definition @{text \<open>attree\<close>} defines attack trees.
The simplest case of an attack tree is a base attack.
The principal idea is that base attacks are defined by a pair of
state sets representing the initial states and the {\it attack property}
-- a set of states characterized by the fact that this property holds
in them. 
Attacks can also be combined as the conjunction or disjunction of other attacks. 
The operator @{text \<open>\<oplus>\<^sub>\<or>\<close>} creates or-trees and @{text \<open>\<oplus>\<^sub>\<and>\<close>} creates and-trees.
And-attack trees @{text \<open>l \<oplus>\<^sub>\<and> s\<close>} and or-attack trees @{text \<open>l \<oplus>\<^sub>\<or> s\<close>} 
combine lists of attack trees $l$ either conjunctively or disjunctively and
consist of a list of sub-attacks -- again attack trees.\<close>
datatype ('s :: state) attree = BaseAttack "('s set) * ('s set)" ("\<N>\<^bsub>(_)\<^esub>") |
                  AndAttack "('s attree) list" "('s set) * ('s set)" ("_ \<oplus>\<^sub>\<and>\<^bsup>(_)\<^esup>" 60) | 
                  OrAttack  "('s attree) list" "('s set) * ('s set)" ("_ \<oplus>\<^sub>\<or>\<^bsup>(_)\<^esup>" 61)

primrec attack :: "('s :: state) attree \<Rightarrow> ('s set) * ('s set)"
  where 
"attack (BaseAttack b) = b"|
"attack (AndAttack as s) = s"  | 
"attack (OrAttack as s) = s"

subsection \<open>Attack Tree refinement\<close>
text \<open>When we develop an attack tree, we proceed from an abstract attack, given
by an attack goal, by breaking it down into a series of sub-attacks. This
proceeding corresponds to a process of {\it refinement}. Therefore, as part of
the attack tree calculus, we provide a notion of attack tree refinement.

The relation @{text \<open>refines_to\<close>} "constructs" the attack tree. Here the above
defined attack vectors are used to define how nodes in an attack tree 
can be expanded into more detailed (refined) attack sequences. This 
process of refinement @{text "\<sqsubseteq>"} allows to eventually reach a fully detailed
attack that can then be proved using @{text "\<turnstile>"}.\<close>
inductive refines_to :: "[('s :: state) attree, 's attree] \<Rightarrow> bool" ("_ \<sqsubseteq> _" [40] 40)
where 
refI: "\<lbrakk>  A = ((l @ [ \<N>\<^bsub>(si',si'')\<^esub>] @ l'')\<oplus>\<^sub>\<and>\<^bsup>(si,si''')\<^esup> );
          A' = (l' \<oplus>\<^sub>\<and>\<^bsup>(si',si'')\<^esup>);
          A'' = (l @ l' @ l'' \<oplus>\<^sub>\<and>\<^bsup>(si,si''')\<^esup>)
        \<rbrakk> \<Longrightarrow> A \<sqsubseteq> A''"| 
ref_or: "\<lbrakk> as \<noteq> []; \<forall> A' \<in> set(as). (A  \<sqsubseteq> A') \<and> attack A = s \<rbrakk> \<Longrightarrow> A \<sqsubseteq> (as \<oplus>\<^sub>\<or>\<^bsup>s\<^esup>)" |
ref_trans: "\<lbrakk> A \<sqsubseteq> A'; A' \<sqsubseteq> A'' \<rbrakk> \<Longrightarrow> A \<sqsubseteq> A''"|
ref_refl : "A \<sqsubseteq> A"


subsection \<open>Validity of Attack Trees\<close>
text \<open>A valid attack, intuitively, is one which is fully refined into fine-grained
attacks that are feasible in a model. The general model we provide is
a Kripke structure, i.e., a set of states and a generic state transition.
Thus, feasible steps in the model are single steps of the state transition.
We call them valid base attacks.
The composition of sequences of valid base attacks into and-attacks yields
again valid attacks if the base attacks line up with respect to the states
in the state transition. If there are different valid attacks for the same
attack goal starting from the same initial state set, these can be 
summarized in an or-attack.
More precisely, the different cases of the validity predicate are distinguished
by pattern matching over the attack tree structure.
\begin{itemize}
\item A  base attack @{text \<open>\<N>(s0,s1)\<close>} is  valid if from all
states in the pre-state set @{text \<open>s0\<close>} we can get with a single step of the 
state transition relation to a state in the post-state set \<open>s1\<close>. Note,
that it is sufficient for a post-state to exist for each pre-state. After all,
we are aiming to validate attacks, that is, possible attack paths to some
state that fulfills the attack property.
\item An and-attack @{text \<open>As \<oplus>\<^sub>\<and> (s0,s1)\<close>} is a valid attack
 if either of the following cases holds:
  \begin{itemize}
   \item empty attack sequence @{text \<open>As\<close>}: in this case 
       all pre-states in @{text \<open>s0\<close>} must already be attack states 
       in @{text \<open>s1\<close>}, i.e., @{text \<open>s0 \<subseteq> s1\<close>};
   \item attack sequence @{text \<open>As\<close>} is singleton: in this case, the 
      singleton element attack @{text \<open>a\<close>} in @{text \<open>[a]\<close>}, 
      must be a valid attack and it must be an attack with pre-state 
      @{text \<open>s0\<close>} and post-state @{text \<open>s1\<close>};
   \item otherwise, @{text \<open>As\<close>} must be a list matching @{text \<open>a # l\<close>} for
     some attack @{text \<open>a\<close>} and tail of attack list @{text \<open>l\<close>} such that
     @{text \<open>a\<close>} is a valid attack with pre-state identical to the overall 
     pre-state @{text \<open>s0\<close>} and the goal of the tail @{text \<open>l\<close>} is 
     @{text \<open>s1\<close>} the goal of the  overall attack. The pre-state of the
     attack represented by @{text \<open>l\<close>} is @{text \<open>snd(attack a)\<close>} since this is 
     the post-state set of the first step @{text \<open>a\<close>}.
\end{itemize}
 \item An or-attack @{text \<open>As  \<oplus>\<^sub>\<or>(s0,s1)\<close>} is a valid attack 
  if either of the following cases holds: 
  \begin{itemize}
   \item the empty attack case is identical to the and-attack above: 
       @{text \<open>s0 \<subseteq> s1\<close>};
   \item attack sequence @{text \<open>As\<close>} is singleton: in this case, the 
      singleton element attack @{text \<open>a\<close>}
      must be a valid attack and 
      its pre-state must include the overall attack pre-state set @{text \<open>s0\<close>} 
      (since @{text \<open>a\<close>} is singleton in the or) while the post-state of 
      @{text \<open>a\<close>} needs to be included in the global attack goal @{text \<open>s1\<close>};
   \item otherwise, @{text \<open>As\<close>} must be a list  @{text \<open>a # l\<close>} for
     an attack @{text \<open>a\<close>} and a list @{text \<open>l\<close>} of alternative attacks.
     The pre-states can be just a subset of @{text \<open>s0\<close>} (since there are
     other attacks in @{text \<open>l\<close>} that can cover the rest) and the goal
     states @{text \<open>snd(attack a)\<close>} need to lie all in the overall goal
     state @{text \<open>set s1\<close>}. The other or-attacks in @{text \<open>l\<close>} need
     to cover only the pre-states @{text \<open>fst s - fst(attack a)\<close>}
     (where @{text \<open>-\<close>} is set difference) and have the same goal @{text \<open>snd s\<close>}.
   \end{itemize}
\end{itemize}
The proof calculus is thus completely described by one recursive function. \<close>
fun is_attack_tree :: "[('s :: state) attree] \<Rightarrow> bool"  ("\<turnstile>_" [40] 40) 
where 
att_base:  "(\<turnstile> \<N>\<^bsub>s\<^esub>) = ( (\<forall> x \<in> (fst s). (\<exists> y \<in> (snd s). x  \<rightarrow>\<^sub>i y )))" |
att_and: "(\<turnstile>((As :: ('s :: state attree list)) \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>)) = 
               (case As of
                  [] \<Rightarrow> (fst s \<subseteq> snd s)
                | [a] \<Rightarrow> ( \<turnstile> a \<and> attack a = s) 
                | (a # l) \<Rightarrow> (( \<turnstile> a) \<and>  (fst(attack a) = fst s) \<and> 
                            (\<turnstile>(l \<oplus>\<^sub>\<and>\<^bsup>(snd(attack a),snd(s))\<^esup>))))" |
att_or: "(\<turnstile>((As :: ('s :: state attree list)) \<oplus>\<^sub>\<or>\<^bsup>s\<^esup>)) = 
               (case As of 
                  [] \<Rightarrow> (fst s \<subseteq> snd s) 
                | [a] \<Rightarrow> ( \<turnstile> a \<and> (fst(attack a) \<supseteq> fst s) \<and> (snd(attack a) \<subseteq> snd s)) 
                | (a # l) \<Rightarrow> (( \<turnstile> a) \<and> fst(attack a) \<subseteq> fst s \<and> 
                              snd(attack a) \<subseteq> snd s \<and>
                       ( \<turnstile>(l \<oplus>\<^sub>\<or>\<^bsup>(fst s - fst(attack a), snd s)\<^esup>))))" 
text \<open>Since the definition is constructive, code can be generated directly from it, here
into the programming language Scala.\<close>
export_code is_attack_tree in Scala    

subsection "Lemmas for Attack Tree validity"
lemma att_and_one: assumes "\<turnstile> a" and  "attack a = s"
  shows  "\<turnstile>([a] \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>)"
proof -
  show " \<turnstile>([a] \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>)" using assms
    by (subst att_and, simp del: att_and att_or)
qed

declare is_attack_tree.simps[simp del]
  
lemma att_and_empty[rule_format] : " \<turnstile>([] \<oplus>\<^sub>\<and>\<^bsup>(s', s'')\<^esup>) \<longrightarrow> s' \<subseteq> s''"
proof -
  show " \<turnstile>([] \<oplus>\<^sub>\<and>\<^bsup>(s', s'')\<^esup>) \<longrightarrow> s' \<subseteq> s''"
    by (simp add: is_attack_tree.simps(2))
qed

lemma att_and_empty2: " \<turnstile>([] \<oplus>\<^sub>\<and>\<^bsup>(s, s)\<^esup>)"
proof -
  show " \<turnstile>([] \<oplus>\<^sub>\<and>\<^bsup>(s, s)\<^esup>)"
    by (simp add: is_attack_tree.simps(2))
qed

lemma att_or_empty[rule_format] : " \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>(s', s'')\<^esup>) \<longrightarrow> s' \<subseteq> s''"
proof -
  show " \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>(s', s'')\<^esup>) \<longrightarrow> s' \<subseteq> s''"
    by (simp add: is_attack_tree.simps(3))
qed

lemma att_or_empty_back[rule_format]: " s' \<subseteq> s'' \<longrightarrow>  \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>(s', s'')\<^esup>)"
proof -
  show "s' \<subseteq> s'' \<longrightarrow>  \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>(s', s'')\<^esup>)"
    by (simp add: is_attack_tree.simps(3))
qed

lemma att_or_empty_rev: assumes "\<turnstile>(l \<oplus>\<^sub>\<or>\<^bsup>(s, s')\<^esup>)" 
                  and "\<not>(s \<subseteq> s')" shows "l \<noteq> []"    
proof -
  show  "l \<noteq> []" using assms
    using att_or_empty by blast
qed

lemma att_or_empty2: "\<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>(s, s)\<^esup>)"
proof -
  show " \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>(s, s)\<^esup>)"
    by (simp add: att_or_empty_back)
qed

lemma att_andD1: " \<turnstile>(x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>) \<Longrightarrow> \<turnstile> x1"
proof -
  show " \<turnstile>(x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>) \<Longrightarrow> \<turnstile> x1"
    by (metis (no_types, lifting) is_attack_tree.simps(2) list.exhaust list.simps(4) list.simps(5))
qed

lemma att_and_nonemptyD2[rule_format] : 
       "(x2 \<noteq> [] \<longrightarrow> \<turnstile>(x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>) \<longrightarrow> \<turnstile> (x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>))" 
proof -
  show "(x2 \<noteq> [] \<longrightarrow> \<turnstile>(x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>) \<longrightarrow> \<turnstile> (x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>))"
    by (metis (no_types, lifting) is_attack_tree.simps(2) list.exhaust list.simps(5)) 
qed

lemma att_andD2 : " \<turnstile>(x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>) \<Longrightarrow> \<turnstile> (x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>)" 
proof -
  show " \<turnstile>(x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>) \<Longrightarrow> \<turnstile> (x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>)"
    by (metis (mono_tags, lifting) att_and_empty2 att_and_nonemptyD2 is_attack_tree.simps(2) list.simps(4) list.simps(5))
qed

lemma in_set_list_cons: "x \<in> set x2 \<Longrightarrow> x \<in> set (x1 # x2)"  
  by (rule List.list.set_intros(2))
    
lemma att_and_fst_lem[rule_format]: 
   " \<turnstile>(x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<longrightarrow> xa \<in> fst (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>))
                     \<longrightarrow> xa \<in> fst (attack x1)"  
proof -
  show " \<turnstile>(x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<longrightarrow> xa \<in> fst (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>))
                     \<longrightarrow> xa \<in> fst (attack x1)"  
    by (induct_tac x2a, (subst att_and, simp)+)
qed

lemma att_orD1: " \<turnstile>(x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<Longrightarrow> \<turnstile> x1"
proof -
  show " \<turnstile>(x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<Longrightarrow> \<turnstile> x1"
   by (case_tac x2, (subst (asm) att_or, simp)+)
qed
    
lemma att_or_snd_hd: " \<turnstile>(a # list \<oplus>\<^sub>\<or>\<^bsup>(aa, b)\<^esup>) \<Longrightarrow> snd(attack a) \<subseteq> b"
proof - 
  show " \<turnstile>(a # list \<oplus>\<^sub>\<or>\<^bsup>(aa, b)\<^esup>) \<Longrightarrow> snd(attack a) \<subseteq> b"
   by (case_tac list,  (subst (asm) att_or, simp)+)
qed
 
lemma att_or_singleton[rule_format]: 
   " \<turnstile>([x1] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow> \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>(fst x - fst (attack x1), snd x)\<^esup>)" 
proof -
  show " \<turnstile>([x1] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow> \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>(fst x - fst (attack x1), snd x)\<^esup>)" 
    by (subst att_or, simp, rule impI, rule att_or_empty_back, blast)
qed

lemma att_orD2[rule_format]: 
     " \<turnstile>(x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow>  \<turnstile> (x2 \<oplus>\<^sub>\<or>\<^bsup>(fst x - fst(attack x1), snd x)\<^esup>)"
proof -
  show " \<turnstile>(x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow>  \<turnstile> (x2 \<oplus>\<^sub>\<or>\<^bsup>(fst x - fst(attack x1), snd x)\<^esup>)"
    by (case_tac x2, simp add: att_or_singleton, simp, subst att_or, simp)
qed

lemma att_or_snd_att[rule_format]: "\<forall> x. \<turnstile> (x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow> (\<forall> a \<in> (set x2). snd(attack a) \<subseteq> snd x )" 
proof (induct_tac x2)
  show "\<forall>x::'a set \<times> 'a set.
       \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow> (\<forall>a::'a attree\<in>set []. snd (attack a) \<subseteq> snd x)"
    by (simp add: att_or)
next show "\<And>(a::'a attree) list::'a attree list.
       \<forall>x::'a set \<times> 'a set.
          \<turnstile>(list \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow> (\<forall>a::'a attree\<in>set list. snd (attack a) \<subseteq> snd x) \<Longrightarrow>
       \<forall>x::'a set \<times> 'a set.
          \<turnstile>(a # list \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow> (\<forall>a::'a attree\<in>set (a # list). snd (attack a) \<subseteq> snd x)"
    using att_orD2 att_or_snd_hd by fastforce
qed

lemma singleton_or_lem: " \<turnstile>([x1] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)  \<Longrightarrow> fst x \<subseteq> fst(attack x1)"
proof -
  show " \<turnstile>([x1] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)  \<Longrightarrow> fst x \<subseteq> fst(attack x1)"
    by (subst (asm) att_or, simp)+
qed

lemma or_att_fst_sup0[rule_format]: "x2 \<noteq> [] \<longrightarrow> (\<forall> x. (\<turnstile> ((x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>):: ('s :: state) attree)) \<longrightarrow>
                      ((\<Union> y::'s attree\<in> set x2. fst (attack y)) \<supseteq> fst(x))) "
proof (induct_tac x2)
  show "[] \<noteq> [] \<longrightarrow>
    (\<forall>x::'s set \<times> 's set.
        \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow> fst x \<subseteq> (\<Union>y::'s attree\<in>set []. fst (attack y)))" by simp
  next show "\<And>(a::'s attree) list::'s attree list.
       list \<noteq> [] \<longrightarrow>  (\<forall>x::'s set \<times> 's set.
           \<turnstile>(list \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow> fst x \<subseteq> (\<Union>y::'s attree\<in>set list. fst (attack y))) \<Longrightarrow>
       a # list \<noteq> [] \<longrightarrow>  (\<forall>x::'s set \<times> 's set.
           \<turnstile>(a # list \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow> fst x \<subseteq> (\<Union>y::'s attree\<in>set (a # list). fst (attack y)))"
      using att_orD2 singleton_or_lem by fastforce
  qed

lemma or_att_fst_sup: 
    assumes "(\<turnstile> ((x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>):: ('s :: state) attree))"
    shows   "((\<Union> y::'s attree\<in> set (x1 # x2). fst (attack y)) \<supseteq> fst(x))"
proof -
  show "((\<Union> y::('s :: state) attree\<in> set (x1 # x2). fst (attack y)) \<supseteq> fst(x))" 
    by (rule or_att_fst_sup0, simp, rule assms)
qed

text \<open>The lemma @{text \<open>att_elem_seq\<close>} is the main lemma for Correctness.
  It shows that for a given attack tree x1, for each element in the set of start sets 
  of the first attack, we can reach in zero or more steps a state in the states in which 
  the attack is successful (the final attack state @{text \<open>snd(attack x1)\<close>}).
  This proof is a big alternative to an earlier version of the proof with
  @{text \<open>first_step\<close>} etc that mapped first on a sequence of sets of states.\<close>
lemma att_elem_seq[rule_format]: "\<turnstile> x1 \<longrightarrow> (\<forall> x \<in> fst(attack x1).
                     (\<exists> y. y \<in> snd(attack x1) \<and> x \<rightarrow>\<^sub>i* y))"
text \<open>First attack tree induction\<close>
proof (induct_tac x1)
  text \<open>Base case\<close>
    show "\<And>x::'a set \<times> 'a set. \<turnstile>\<N>\<^bsub>x\<^esub> \<longrightarrow> (\<forall>xa::'a\<in>fst (attack \<N>\<^bsub>x\<^esub>). \<exists>y::'a. y \<in> snd (attack \<N>\<^bsub>x\<^esub>) \<and> xa \<rightarrow>\<^sub>i* y)"
      using EF_step_star is_attack_tree.simps(1) state_transition_refl_def by fastforce
text \<open>Second case @{text\<open>\<and>\<close>} -- setting it up for induction (this time list induction)\<close>
  next show "\<And>(x1a::'a attree list) x2::'a set \<times> 'a set.
       (\<And>x1aa::'a attree.
           x1aa \<in> set x1a \<Longrightarrow>
           \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<Longrightarrow>
       \<turnstile>(x1a \<oplus>\<^sub>\<and>\<^bsup>x2\<^esup>) \<longrightarrow>
       (\<forall>x::'a\<in>fst (attack (x1a \<oplus>\<^sub>\<and>\<^bsup>x2\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x1a \<oplus>\<^sub>\<and>\<^bsup>x2\<^esup>)) \<and> x \<rightarrow>\<^sub>i* y)"
      apply (rule_tac x = x2 in spec)
      apply (subgoal_tac "(\<forall> x1aa::'a attree.
                              x1aa \<in> set x1a \<longrightarrow>
                               \<turnstile>x1aa \<longrightarrow>
                               (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y))")
       apply (rule mp)
        prefer 2
        apply (rotate_tac -1)
        apply assumption
      text \<open>Induction for @{text \<open>\<and>\<close>}: the manual instantiation seems tedious but in the @{text \<open>\<and>\<close>} 
            case necessary to get the right induction hypothesis.\<close>
proof (rule_tac list = "x1a" in list.induct)
  text \<open>The @{text \<open>\<and>\<close>} induction empty case\<close>
      show "(\<forall>x1aa::'a attree.
           x1aa \<in> set [] \<longrightarrow>
           \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<longrightarrow>
       (\<forall>x::'a set \<times> 'a set.
           \<turnstile>([] \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<longrightarrow>
           (\<forall>xa::'a\<in>fst (attack ([] \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack ([] \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y))"
        using att_and_empty state_transition_refl_def by fastforce
      text \<open>The @{text \<open>\<and>\<close>} induction case nonempty\<close>
    next show "\<And>(x1a::'a attree list) (x2::'a set \<times> 'a set) (x1::'a attree) (x2a::'a attree list).
       (\<And>x1aa::'a attree.
           (x1aa \<in> set x1a) \<Longrightarrow>
           ((\<turnstile>x1aa) \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y))) \<Longrightarrow>
       \<forall>x1aa::'a attree.
          (x1aa \<in> set x1a) \<longrightarrow>
          (\<turnstile>x1aa) \<longrightarrow> ((\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<Longrightarrow>
       (\<forall>x1aa::'a attree.
           (x1aa \<in> set x2a) \<longrightarrow>
           (\<turnstile>x1aa) \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<longrightarrow>
       (\<forall>x::'a set \<times> 'a set.
           (\<turnstile>(x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<longrightarrow>
           ((\<forall>xa::'a\<in>fst (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y))) \<Longrightarrow>
       ((\<forall>x1aa::'a attree.
           (x1aa \<in> set (x1 # x2a)) \<longrightarrow>
           (\<turnstile>x1aa) \<longrightarrow> ((\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y))) \<longrightarrow>
       (\<forall>x::'a set \<times> 'a set.
          ( \<turnstile>(x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<longrightarrow>
           (\<forall>xa::'a\<in>fst (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)).
               (\<exists>y::'a. y \<in> snd (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> (xa \<rightarrow>\<^sub>i* y)))))"
        apply (rule impI, rule allI, rule impI)
        text \<open>Set free the Induction Hypothesis: this is necessary to provide the grounds for specific 
              instantiations in the step.\<close>
        apply (subgoal_tac "(\<forall>x::'a set \<times> 'a set.
                             \<turnstile>(x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<longrightarrow>
                             (\<forall>xa::'a\<in>fst (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)).
                              \<exists>y::'a. y \<in> snd (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y))")
         prefer 2
         apply simp
        text \<open>The following induction step for @{text \<open>\<and>\<close>} needs a number of manual instantiations 
              so that the proof is not found automatically. In the subsequent case for @{text \<open>\<or>\<close>}, 
              sledgehammer finds the proof.\<close>
      proof -
        show "\<And>(x1a::'a attree list) (x2::'a set \<times> 'a set) (x1::'a attree) (x2a::'a attree list) x::'a set \<times> 'a set.
       \<forall>x1aa::'a attree.
          x1aa \<in> set (x1 # x2a) \<longrightarrow>
          \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y) \<Longrightarrow>
       \<turnstile>(x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<Longrightarrow>
       \<forall>x::'a set \<times> 'a set.
          \<turnstile>(x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<longrightarrow>
          (\<forall>xa::'a\<in>fst (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y) \<Longrightarrow>
       \<forall>xa::'a\<in>fst (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y"
          apply (rule ballI)
          apply (rename_tac xa)
          text \<open>Prepare the steps\<close> 
          apply (drule_tac x = "(snd(attack x1), snd x)" in spec)
          apply (rotate_tac -1)
          apply (erule impE)
           apply (erule att_andD2)
          text \<open>Premise for x1\<close>
          apply (drule_tac x = x1 in spec)
          apply (drule mp)
           apply simp
          apply (drule mp)
           apply (erule att_andD1)
          text \<open>Instantiate first step for xa\<close>
          apply (rotate_tac -1)
          apply (drule_tac x = xa in bspec)
           apply (erule att_and_fst_lem, assumption)
          apply (erule exE)
          apply (erule conjE)
          text \<open>Take this y and put it as first into the second part\<close>
          apply (drule_tac x = y in bspec)
           apply simp
          apply (erule exE)
          apply (erule conjE)
          text \<open>Bind the first @{text \<open>xa \<rightarrow>\<^sub>i* y\<close>} and second @{text \<open>y \<rightarrow>\<^sub>i* ya\<close>} together for solution\<close>
          apply (rule_tac x = ya in exI)
          apply (rule conjI)
           apply simp
          by (simp add: state_transition_refl_def)
      qed
 next show "\<And>(x1a::'a attree list) x2::'a set \<times> 'a set.
       (\<And>x1aa::'a attree.
           x1aa \<in> set x1a \<Longrightarrow>
           \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<Longrightarrow>
       \<forall>x1aa::'a attree.
          x1aa \<in> set x1a \<longrightarrow> \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)"
     by simp
 qed
 text \<open>The @{text \<open>\<or>\<close>}  attack case is -- after setting up with the generic induction command -- 
       completely automatically using sledgehammer!\<close> 
next fix x1a 
  show "(\<And> x2. (\<And>x1aa.
           x1aa \<in> set x1a \<Longrightarrow> \<turnstile>x1aa \<longrightarrow> (\<forall>x\<in>fst (attack x1aa). \<exists>y. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<Longrightarrow>
       \<turnstile>x1a \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup> \<longrightarrow> (\<forall>x\<in>fst (attack (x1a \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>)). \<exists>y. y \<in> snd (attack (x1a \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>)) \<and> x \<rightarrow>\<^sub>i* y))"
  proof (induction x1a)
    case Nil
    then show ?case
    proof -
      { fix bb :: 'b
        { assume "bb \<notin> snd x2"
          moreover
          { assume "\<not> fst x2 \<subseteq> snd x2"
            then have "\<exists>b. \<not> \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>) \<or> bb \<notin> fst (attack ([] \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>)) \<or> b \<in> snd (attack ([] \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>)) \<and> bb \<rightarrow>\<^sub>i* b"
              by (simp add: is_attack_tree.simps(3)) }
          ultimately have "\<exists>b. \<not> \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>) \<or> bb \<notin> fst (attack ([] \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>)) \<or> b \<in> snd (attack ([] \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>)) \<and> bb \<rightarrow>\<^sub>i* b"
            by auto }
        then have "\<exists>b. \<not> \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>) \<or> bb \<notin> fst (attack ([] \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>)) \<or> b \<in> snd (attack ([] \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>)) \<and> bb \<rightarrow>\<^sub>i* b"
          by (metis (full_types) EF_lem2a EF_step_star_rev attack.simps(3)) }
      then show ?thesis
        by blast
    qed
  next
    case (Cons a x1a)
    then show ?case
      by (smt DiffI att_orD1 att_orD2 att_or_snd_att attack.simps(3) insert_iff list.set(2) prod.sel(1) snd_conv subset_iff) 
  qed
qed
    
lemma att_elem_seq0: "\<turnstile> x1 \<Longrightarrow> (\<forall> x \<in> fst(attack x1).
                     (\<exists> y. y \<in> snd(attack x1) \<and> x \<rightarrow>\<^sub>i* y))"
proof (clarify)
  fix x
  assume  a: "\<turnstile>x1" and b: "x \<in> fst (attack x1) "
  show "\<exists>y::'a. y \<in> snd (attack x1) \<and> x \<rightarrow>\<^sub>i* y" using a b
  by (rule att_elem_seq)
qed
          
subsection \<open>Valid refinements\<close>
definition valid_ref :: "[('s :: state) attree, 's attree] \<Rightarrow> bool" ("_ \<sqsubseteq>\<^sub>V _" 50)
  where
"A \<sqsubseteq>\<^sub>V A' \<equiv>  ( (A \<sqsubseteq> A') \<and>  \<turnstile> A')"

definition ref_validity :: "[('s :: state) attree] \<Rightarrow> bool" ("\<turnstile>\<^sub>V _" 50)
  where
"\<turnstile>\<^sub>V A  \<equiv>  (\<exists> A'. (A \<sqsubseteq>\<^sub>V A'))"

lemma ref_valI: " A \<sqsubseteq> A'\<Longrightarrow>  \<turnstile> A' \<Longrightarrow> \<turnstile>\<^sub>V A"
proof (simp add: ref_validity_def valid_ref_def)
  show "A \<sqsubseteq> A' \<Longrightarrow> \<turnstile>A' \<Longrightarrow> \<exists>A'::'a attree. (A \<sqsubseteq> A') \<and> \<turnstile>A'"
    by (rule exI, rule conjI)
qed

section "Correctness and Completeness"
text \<open>This section presents the main theorems of Correctness and Completeness
      between AT and Kripke, essentially: 

@{text \<open>\<turnstile> (init K, p) \<equiv>  K \<turnstile> EF p\<close>}.

First, we proof a number of lemmas needed for both directions before we 
show the Correctness theorem followed by the Completeness theorem.
\<close>    
subsection \<open>Lemma for Correctness and Completeness\<close>
lemma nth_app_eq[rule_format]: "\<forall> sl x. sl \<noteq> [] \<longrightarrow> sl ! (length sl - Suc (0::nat)) = x \<longrightarrow> 
                    (l @ sl) ! (length l + length sl - Suc (0::nat)) = x"    
proof (rule_tac list = l in list.induct)
  show "\<forall>(sl::'a list) x::'a.
       sl \<noteq> [] \<longrightarrow>
       sl ! (length sl - Suc (0::nat)) = x \<longrightarrow>
       ([] @ sl) ! (length [] + length sl - Suc (0::nat)) = x"
    by simp
next show "\<And>(x1::'a) x2::'a list.
       \<forall>(sl::'a list) x::'a.
          sl \<noteq> [] \<longrightarrow>
          sl ! (length sl - Suc (0::nat)) = x \<longrightarrow>
          (x2 @ sl) ! (length x2 + length sl - Suc (0::nat)) = x \<Longrightarrow>
       \<forall>(sl::'a list) x::'a.
          sl \<noteq> [] \<longrightarrow>
          sl ! (length sl - Suc (0::nat)) = x \<longrightarrow>
          ((x1 # x2) @ sl) ! (length (x1 # x2) + length sl - Suc (0::nat)) = x"
  by simp
qed

lemma nth_app_eq1[rule_format]: "\<forall> sl i.  i < length sla 
                                 \<longrightarrow> (sla @ sl) ! i = sla ! i"
proof (induct_tac sla)
  show " \<forall>(sl::'a list) i::nat. i < length [] \<longrightarrow> ([] @ sl) ! i = [] ! i"
    by simp
next show "\<And>(a::'a) list::'a list.
       \<forall>(sl::'a list) i::nat. i < length list \<longrightarrow> (list @ sl) ! i = list ! i \<Longrightarrow>
       \<forall>(sl::'a list) i::nat.
          i < length (a # list) \<longrightarrow> ((a # list) @ sl) ! i = (a # list) ! i"
    by (meson nth_append)
qed

lemma nth_app_eq1_rev:   "i < length sla \<Longrightarrow>  sla ! i = (sla @ sl) ! i"
proof (subst nth_app_eq1)
  show "i < length sla \<Longrightarrow> i < length sla" by assumption
next show "i < length sla \<Longrightarrow> sla ! i = sla ! i"
    by (rule refl)
qed

lemma nth_app_eq2[rule_format]: "\<forall> sl i. length sla \<le> i \<and> i < length (sla @ sl) 
                     \<longrightarrow> (sla @ sl) ! i = sl ! (i - (length sla))"
proof (induct_tac sla)
  show "\<forall>(sl::'a list) i::nat.
       length [] \<le> i \<and> i < length ([] @ sl) \<longrightarrow> ([] @ sl) ! i = sl ! (i - length [])"
    by simp
next show "\<And>(a::'a) list::'a list.
       \<forall>(sl::'a list) i::nat.
          length list \<le> i \<and> i < length (list @ sl) \<longrightarrow> (list @ sl) ! i = sl ! (i - length list) \<Longrightarrow>
       \<forall>(sl::'a list) i::nat.
          length (a # list) \<le> i \<and> i < length ((a # list) @ sl) \<longrightarrow>
          ((a # list) @ sl) ! i = sl ! (i - length (a # list))"
    by (meson less_not_le nth_append)
qed

lemma tl_ne_ex[rule_format]: "l \<noteq> [] \<longrightarrow> (? x . l = x # (tl l))"
proof (induct_tac l, auto)
qed

lemma tl_nempty_lngth[rule_format]: "tl sl \<noteq> [] \<longrightarrow> 2 \<le> length(sl)"
proof (induct_tac sl)
  show "tl [] \<noteq> [] \<longrightarrow> (2::nat) \<le> length []"
    by simp
next show "\<And>(a::'a) list::'a list.
   tl list \<noteq> [] \<longrightarrow> (2::nat) \<le> length list \<Longrightarrow> tl (a # list) \<noteq> [] \<longrightarrow> (2::nat) \<le> length (a # list)"
    by (simp add: Nitpick.size_list_simp(2))
qed
  
lemma list_app_one_length: "length l = n \<Longrightarrow> (l @ [s]) ! n = s"
proof (erule subst, simp)
qed
  
lemma tl_lem1[rule_format]: "l \<noteq> [] \<longrightarrow> tl l = [] \<longrightarrow> length l = 1"
proof (induct_tac l, simp+)
qed
  
lemma nth_tl_length[rule_format]: "tl sl \<noteq> [] \<longrightarrow>
      tl sl ! (length (tl sl) - Suc (0::nat)) = sl ! (length sl - Suc (0::nat))" 
proof (rule_tac list = sl in list.induct, simp+)
qed

lemma nth_tl_length1[rule_format]: "tl sl \<noteq> [] \<longrightarrow>
      tl sl ! n = sl ! (n + 1)" 
proof (rule_tac list = sl in list.induct, simp+)
qed
   
lemma ineq1: "i < length sla - n  \<Longrightarrow>
       (0::nat) \<le> n \<Longrightarrow> i < length sla"  
proof (simp)  
qed

lemma ineq2[rule_format]: "length sla \<le> i \<longrightarrow> i + (1::nat) - length sla = i - length sla + 1"
proof (arith)
qed

lemma ineq3: "tl sl \<noteq> []  \<Longrightarrow> length sla \<le> i \<Longrightarrow> i < length (sla @ tl sl) - (1::nat)
              \<Longrightarrow> i - length sla + (1::nat) < length sl - (1::nat)"    
proof (simp)
qed

lemma tl_eq1[rule_format]: "sl \<noteq> [] \<longrightarrow> tl sl ! (0::nat) = sl ! Suc (0::nat)"  
proof (rule_tac list = sl in list.induct, simp+)
qed

lemma tl_eq2[rule_format]: "tl sl = [] \<longrightarrow> sl ! (0::nat) = sl ! (length sl - (1::nat))"
proof (induct_tac sl, simp+)
qed

lemma tl_eq3[rule_format]: "tl sl \<noteq> [] \<longrightarrow>
    tl sl ! (length sl - Suc (Suc (0::nat))) = sl ! (length sl - Suc (0::nat))"    
proof (induct_tac sl, simp+)
qed

lemma nth_app_eq3: assumes "tl sl \<noteq> []"
  shows "(sla @ tl sl) ! (length (sla @ tl sl) - (1::nat)) = sl ! (length sl - (1::nat))" 
proof (subst nth_app_eq2)
  show "length sla \<le> length (sla @ tl sl) - (1::nat) \<and> length (sla @ tl sl) - (1::nat) < length (sla @ tl sl)"
    proof -
    have "2 \<le> length sl" using assms by (rule tl_nempty_lngth)
    thus "length sla \<le> length (sla @ tl sl) - (1::nat) \<and> length (sla @ tl sl) - (1::nat) < length (sla @ tl sl)"
    by force
  qed
next show "tl sl ! (length (sla @ tl sl) - (1::nat) - length sla) = sl ! (length sl - (1::nat))" using assms
    by (simp, rule tl_eq3)
qed

lemma not_empty_ex: "A \<noteq> {} \<Longrightarrow> ? x. x \<in> A"
proof (force)
qed

lemma in_set_list_head: "x \<in> set (x # x2)"  
proof (rule List.list.set_intros(1))
qed

lemma fst_att_eq: "(fst x # sl) ! (0::nat) = fst (attack (al \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>))"
proof (simp)
qed

lemma list_eq1[rule_format]: "sl \<noteq> [] \<longrightarrow>
     (fst x # sl) ! (length (fst x # sl) - (1::nat)) = sl ! (length sl - (1::nat))"
proof (induct_tac sl, auto)
qed

lemma attack_eq1: "snd (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) = snd (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>(snd (attack x1), snd x)\<^esup>))"
proof (simp)
qed

lemma attack_eq2 : "(fst (attack x1), snd (attack x1)) = attack x1"
proof (simp)
qed

lemma fst_lem1[rule_format]: "\<forall> (a:: 's set) b (c :: 's set) d. (a, c) = (b, d) \<longrightarrow> a = b"
proof (auto)
qed

lemma fst_eq1: "(sla ! (0::nat), y) = attack x1 \<Longrightarrow>
       sla ! (0::nat) = fst (attack x1)"
proof (rule_tac c = y and d = "snd(attack  x1)" in fst_lem1, simp)
qed
    
lemma base_att_lem1: " y0 \<subseteq> y1 \<Longrightarrow> \<turnstile> \<N>\<^bsub>(y1, y)\<^esub> \<Longrightarrow>\<turnstile> \<N>\<^bsub>(y0, y)\<^esub>"
proof (simp add: att_base, blast)
qed

lemma ref_pres_att: "A \<sqsubseteq> A' \<Longrightarrow> attack A = attack A'"
proof (erule refines_to.induct)
  show "\<And>(A::'a attree) (l::'a attree list) (si'::'a set) (si''::'a set) (l''::'a attree list) (si::'a set)
       (si'''::'a set) (A'::'a attree) (l'::'a attree list) A''::'a attree.
       A = (l @ [\<N>\<^bsub>(si', si'')\<^esub>] @ l'' \<oplus>\<^sub>\<and>\<^bsup>(si, si''')\<^esup>) \<Longrightarrow>
       A' = (l' \<oplus>\<^sub>\<and>\<^bsup>(si', si'')\<^esup>) \<Longrightarrow> A'' = (l @ l' @ l'' \<oplus>\<^sub>\<and>\<^bsup>(si, si''')\<^esup>) \<Longrightarrow> attack A = attack A''"
    by simp
next show "\<And>(as::'a attree list) (A::'a attree) (s::'a set \<times> 'a set).
       as \<noteq> [] \<Longrightarrow>
       (\<forall>A'::'a attree\<in> (set as). ((A \<sqsubseteq> A') \<and> (attack A = attack A')) \<and> attack A = s) \<Longrightarrow>
       attack A = attack (as \<oplus>\<^sub>\<or>\<^bsup>s\<^esup>)"
    using last_in_set by auto
next show "\<And>(A::'a attree) (A'::'a attree) A''::'a attree.
       A \<sqsubseteq> A' \<Longrightarrow> attack A = attack A' \<Longrightarrow> A' \<sqsubseteq> A'' \<Longrightarrow> attack A' = attack A'' \<Longrightarrow> attack A = attack A''"
    by simp
next show "\<And>A::'a attree. attack A = attack A" by (rule refl)
qed

lemma  base_subset: 
    assumes "xa \<subseteq> xc"
    shows  "\<turnstile>\<N>\<^bsub>(x, xa)\<^esub> \<Longrightarrow> \<turnstile>\<N>\<^bsub>(x, xc)\<^esub>" 
proof (simp add: att_base)
  show " \<forall>x::'a\<in>x. \<exists>xa::'a\<in>xa. x \<rightarrow>\<^sub>i xa \<Longrightarrow> \<forall>x::'a\<in>x. \<exists>xa::'a\<in>xc. x \<rightarrow>\<^sub>i xa"
    by (meson assms in_mono)
qed

subsection "Correctness Theorem"
text \<open>Proof with induction over the definition of EF using the main 
lemma @{text \<open>att_elem_seq0\<close>}. 

There is also a second version of Correctness for valid refinements.\<close>

theorem AT_EF: assumes " \<turnstile> (A :: ('s :: state) attree)"
               and  "attack A = (I,s)"
               shows "Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s"
proof (simp add:check_def)
  show "I \<subseteq> {sa::('s :: state). (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF s}" 
  proof (rule subsetI, rule CollectI, rule conjI, simp add: state_transition_refl_def)
    show "\<And>x::'s. x \<in> I \<Longrightarrow> \<exists>i::'s\<in>I. (i, x) \<in> {(x::'s, y::'s). x \<rightarrow>\<^sub>i y}\<^sup>*"
    by (rule_tac x = x in bexI, simp)
next show "\<And>x::'s. x \<in> I \<Longrightarrow> x \<in> EF s" using assms
  proof -
    have a: "\<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y" using assms
    proof -
      have "\<forall>x::'s\<in>fst (attack A). \<exists>y::'s. y \<in> snd (attack A) \<and> x \<rightarrow>\<^sub>i* y"
        by (rule att_elem_seq0, rule assms)
      thus " \<forall>x::'s\<in>I. \<exists>y::'s\<in>s. x \<rightarrow>\<^sub>i* y" using assms
      by force  
    qed
    thus "\<And>x::'s. x \<in> I \<Longrightarrow> x \<in> EF s" 
    proof -
      fix x
      assume b: "x \<in> I"
      have "\<exists>y::'s\<in>s::('s :: state) set. x \<rightarrow>\<^sub>i* y" 
        by (rule_tac x = x and A = I in bspec, rule a, rule b)
      from this obtain y where "y \<in> s" and "x \<rightarrow>\<^sub>i* y" by (erule bexE)
      thus "x \<in> EF s" 
       by (erule_tac f = s in EF_step_star)
   qed  
  qed
 qed
qed

theorem ATV_EF: "\<lbrakk> \<turnstile>\<^sub>V (A :: ('s :: state) attree); (I,s) = attack A \<rbrakk> \<Longrightarrow>
 (Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s) } (I :: ('s :: state)set)  \<turnstile> EF s)"   
proof (simp add: ref_validity_def)
  show "(\<exists>A'::'s attree. (A \<sqsubseteq>\<^sub>V A')) \<Longrightarrow> (I, s) = attack A \<Longrightarrow> Kripke {s::'s. \<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* s} I \<turnstile> EF s"
    using AT_EF ref_pres_att valid_ref_def by fastforce
qed
    
subsection "Completeness Theorem"
text \<open>This section contains the completeness direction, informally:

@{text \<open>\<turnstile> EF s \<Longrightarrow> \<exists> A. \<turnstile> A \<and> attack A = (I,s)\<close>}.

The main theorem is presented last since its
proof just summarises a number of main lemmas @{text \<open>Compl_step1, Compl_step2,
Compl_step3, Compl_step4\<close>} which are presented first together with other
auxiliary lemmas.\<close>

subsubsection "Lemma @{text \<open>Compl_step1\<close>}"
lemma Compl_step1: 
"Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s 
\<Longrightarrow> \<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y"
proof (simp add:check_def, clarify)
  fix x
  assume a: "I \<subseteq> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF s}" and b: "x \<in> I "
  show "\<exists>y::'s\<in>s. x \<rightarrow>\<^sub>i* y"
  proof -
    have c: "x \<in> {sa::'s. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF s}" 
      by (rule subsetD, rule a, rule b)
    moreover have d: "(\<exists>i::('s :: state) \<in>I. i \<rightarrow>\<^sub>i* x) \<and> x \<in> EF s"
       by (rule_tac P = "(\<lambda> x. (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* x) \<and> x \<in> EF s)" in CollectD, rule c) 
     ultimately show "\<exists>y::'s\<in>s. x \<rightarrow>\<^sub>i* y" 
       apply (rule_tac x = x and s = s in EF_step_star_rev)
       by (erule conjE)
   qed
 qed

subsubsection "Lemma @{text \<open>Compl_step2\<close>}"
text \<open>First, we prove some auxiliary lemmas.\<close>
lemma rtrancl_imp_singleton_seq2: "x \<rightarrow>\<^sub>i* y \<Longrightarrow> 
          x = y \<or> (\<exists> s. s \<noteq> [] \<and> (tl s \<noteq> []) \<and> s ! 0 = x \<and> s ! (length s - 1) = y \<and> 
               (\<forall> i < (length s - 1). (s ! i) \<rightarrow>\<^sub>i (s ! (Suc i))))"
proof (unfold state_transition_refl_def, erule rtrancl_induct)
  show "x = x \<or>
    (\<exists>s::'a list.
        s \<noteq> [] \<and>
        tl s \<noteq> [] \<and>
        s ! (0::nat) = x \<and> s ! (length s - (1::nat)) = x \<and> (\<forall>i<length s - (1::nat). s ! i \<rightarrow>\<^sub>i s ! Suc i))"
    by (rule disjI1, rule refl) 
next show "\<And>(y::'a) z::'a.
       (x, y) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y} \<Longrightarrow>
       x = y \<or>
       (\<exists>s::'a list.
           s \<noteq> [] \<and>
           tl s \<noteq> [] \<and>
           s ! (0::nat) = x \<and>
           s ! (length s - (1::nat)) = y \<and> (\<forall>i<length s - (1::nat). s ! i \<rightarrow>\<^sub>i s ! Suc i)) \<Longrightarrow>
       x = z \<or>
       (\<exists>s::'a list.
           s \<noteq> [] \<and>
           tl s \<noteq> [] \<and>
           s ! (0::nat) = x \<and> s ! (length s - (1::nat)) = z \<and> (\<forall>i<length s - (1::nat). s ! i \<rightarrow>\<^sub>i s ! Suc i))"
  proof (erule disjE)
    show "\<And>(y::'a) z::'a.
       (x, y) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y} \<Longrightarrow>
       x = y \<Longrightarrow>
       x = z \<or>
       (\<exists>s::'a list.
           s \<noteq> [] \<and>
           tl s \<noteq> [] \<and>
           s ! (0::nat) = x \<and> s ! (length s - (1::nat)) = z \<and> (\<forall>i<length s - (1::nat). s ! i \<rightarrow>\<^sub>i s ! Suc i))"
      by (rule disjI2, rule_tac x = "[y,z]" in exI, simp)
  next show "\<And>(y::'a) z::'a.
       (x, y) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y} \<Longrightarrow>
       \<exists>s::'a list.
          s \<noteq> [] \<and>
          tl s \<noteq> [] \<and>
          s ! (0::nat) = x \<and>
          s ! (length s - (1::nat)) = y \<and> (\<forall>i<length s - (1::nat). s ! i \<rightarrow>\<^sub>i s ! Suc i) \<Longrightarrow>
       x = z \<or>
       (\<exists>s::'a list.
           s \<noteq> [] \<and>
           tl s \<noteq> [] \<and>
           s ! (0::nat) = x \<and> s ! (length s - (1::nat)) = z \<and> (\<forall>i<length s - (1::nat). s ! i \<rightarrow>\<^sub>i s ! Suc i))"
    proof (erule exE, erule conjE, rule disjI2)
      show "\<And>(y::'a) (z::'a) s::'a list.
       (x, y) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y} \<Longrightarrow>
       s \<noteq> [] \<Longrightarrow>
       tl s \<noteq> [] \<and>
       s ! (0::nat) = x \<and> s ! (length s - (1::nat)) = y \<and> (\<forall>i<length s - (1::nat). s ! i \<rightarrow>\<^sub>i s ! Suc i) \<Longrightarrow>
       \<exists>s::'a list.
          s \<noteq> [] \<and>
          tl s \<noteq> [] \<and>
          s ! (0::nat) = x \<and> s ! (length s - (1::nat)) = z \<and> (\<forall>i<length s - (1::nat). s ! i \<rightarrow>\<^sub>i s ! Suc i)"
      proof (rule_tac x = "s @ [z]" in exI, rule conjI, simp, subst nth_app_eq1,
             simp, erule conjE, rule conjI, simp, rule conjI, simp, rule conjI, simp, 
            rule allI, rule impI)
        fix y z s i
        assume a1: "(x, y) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y}\<^sup>*" 
           and a2: "(y, z) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y}"
           and a3: "s \<noteq> []"
           and a4: "tl s \<noteq> []"
           and a5: "s ! (0::nat) = x \<and> s ! (length s - (1::nat)) = y \<and> (\<forall>i<length s - (1::nat). s ! i \<rightarrow>\<^sub>i s ! Suc i)"
           and a6: "i < length (s @ [z]) - (1::nat)"
        show  "(s @ [z]) ! i \<rightarrow>\<^sub>i (s @ [z]) ! Suc i"
        proof -
          have a7: "(i < length s - 1) | (i = length s - 1)" using a1 a2 a3 a4 a5 a6 by force
          hence a8: "i < length s - (1::nat) \<Longrightarrow> (s @ [z]) ! i \<rightarrow>\<^sub>i (s @ [z]) ! Suc i"
            by (simp add: Nitpick.size_list_simp(2) a3 a5 nth_append)
          hence a9: "i = length s - (1::nat) \<Longrightarrow> (s @ [z]) ! i \<rightarrow>\<^sub>i (s @ [z]) ! Suc i" using a3 a2 a5
            apply simp
            by (erule conjE, subst nth_app_eq1, simp+)
          thus "(s @ [z]) ! i \<rightarrow>\<^sub>i (s @ [z]) ! Suc i" using a7 a8
            by blast 
        qed
      qed
    qed
  qed
qed

lemma tl_nempty_length[rule_format]: "s \<noteq> [] \<longrightarrow> tl s \<noteq> [] \<longrightarrow> 0 < length s - 1"
proof (rule_tac list = s in list.induct, simp+)
qed

lemma tl_nempty_length2[rule_format]: "s \<noteq> [] \<longrightarrow> tl s \<noteq> [] \<longrightarrow> Suc 0 < length s"
proof (rule_tac list = s in list.induct, simp+)
qed

lemma length_last[rule_format]: "(l @ [x]) ! (length (l @ [x]) - 1) = x"
proof (rule_tac list = l in list.induct, simp+)
qed

lemma Compl_step2: "\<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y \<Longrightarrow> 
                   ( \<forall> x \<in> I.  x \<in> s \<or> (\<exists> (sl :: ((('s :: state) set)list)). 
                  (sl \<noteq> []) \<and> (tl sl \<noteq> []) \<and>
                 (sl ! 0, sl ! (length sl - 1)) = ({x},s) \<and>
                 (\<forall> i < (length sl - 1).  \<turnstile> \<N>\<^bsub>(sl ! i,sl ! (i+1) )\<^esub>
                         )))"
proof (rule ballI, drule_tac x = x in bspec, assumption, erule bexE)
  fix x y
  assume a: "x \<in> I" and b: "y \<in> s" and  c: "x \<rightarrow>\<^sub>i* y"
  show "x \<in> s \<or>
       (\<exists>sl::'s set list.
           sl \<noteq> [] \<and>
           tl sl \<noteq> [] \<and>
           (sl ! (0::nat), sl ! (length sl - (1::nat))) = ({x}, s) \<and>
           (\<forall>i<length sl - (1::nat). \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1::nat)))\<^esub>))"
  proof -
    have d : "x = y \<or>
       (\<exists>s::'s list.
           s \<noteq> [] \<and>
           tl s \<noteq> [] \<and>
           s ! (0::nat) = x \<and>
           s ! (length s - (1::nat)) = y \<and> (\<forall>i<length s - (1::nat). s ! i \<rightarrow>\<^sub>i s ! Suc i))"
      by (rule rtrancl_imp_singleton_seq2, rule c)
    thus "x \<in> s \<or>
       (\<exists>sl::'s set list.
           sl \<noteq> [] \<and>
           tl sl \<noteq> [] \<and>
           (sl ! (0::nat), sl ! (length sl - (1::nat))) = ({x}, s) \<and>
           (\<forall>i<length sl - (1::nat). \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1::nat)))\<^esub>))"
      apply (insert d)
      apply (erule disjE)
       apply (rule disjI1)
       apply (erule ssubst, rule b)
      apply (rule disjI2)
      apply (erule exE)
      apply (erule conjE)+
      apply (rule_tac x = "[{sa ! j}. j \<leftarrow> [0..<(length sa - 1)]] @ [s]" in exI)
      apply (rule conjI)
       apply simp
    proof -
      fix sa :: "'s list"
      assume e: "sa \<noteq> []" and f: "tl sa \<noteq> []" and g: "sa ! (0::nat) = x" 
         and h: "sa ! (length sa - (1::nat)) = y " and i: "\<forall>i<length sa - (1::nat). sa ! i \<rightarrow>\<^sub>i sa ! Suc i"
      have j: "map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] \<noteq> []" 
        by (subgoal_tac "length sa - 1 > 0", simp, rule tl_nempty_length, rule e, rule f)
      have k: "((map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - Suc (0::nat)] @ [s]) ! (length sa - Suc (0::nat))) = s"
        by (rule list_app_one_length, simp)
      show "tl (map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) \<noteq> [] \<and>
       ((map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) ! (0::nat),
        (map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) !
        (length (map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) - (1::nat))) =
       ({x}, s) \<and>
       (\<forall>i<length (map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) - (1::nat).
           \<turnstile>\<N>\<^bsub>((map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) ! i,
                (map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) ! (i + (1::nat)))\<^esub>)"
        apply (rule conjI)
        apply (insert j, simp)
        apply (rule conjI)
         apply (subst nth_app_eq1, simp)
         apply (subst length_last)
         apply (subst nth_map, simp)
         apply (subgoal_tac "[0::nat..<length sa - (1::nat)] ! (0::nat)  = 0", simp, rule g)
         apply (subst nth_upt, simp)
         apply arith
        apply (rule allI)
        apply (rule impI)
        apply simp
        apply (subst nth_app_eq1, simp)
        apply (case_tac "Suc i < length sa - Suc (0::nat)")
         apply (subst nth_app_eq1, simp)
         apply (subst nth_map, force)
         apply (simp add: att_base i)
        apply (subgoal_tac "Suc i = length sa - Suc (0::nat)")
         apply simp
         apply (subst k)
         apply (subst att_base)
         apply (rule ballI)
         apply simp
         apply (rule_tac x = "sa ! (Suc i)" in bexI, insert i, drule_tac x = i in spec, erule mp, simp)
         apply (insert b h)
        by simp+
    qed
  qed
qed

subsubsection "Lemma @{text \<open>Compl_step3\<close>}"
text \<open>First, we need a few lemmas.\<close>
lemma map_hd_lem[rule_format] : "n > 0 \<longrightarrow> (f 0 #  map (\<lambda>i::nat. f i) [1::nat..<n]) = map  (\<lambda>i::nat. f i) [0..<n]"    
proof (simp add : hd_map upt_rec)
qed

lemma map_Suc_lem[rule_format] : "n > 0 \<longrightarrow> map (\<lambda> i:: nat. f i)[1..<n] =
                                  map (\<lambda> i:: nat. f(Suc i))[0..<(n - 1)]"
proof (case_tac n, simp+)
  show "\<And>nat::nat.
       n = Suc nat \<Longrightarrow>
       Suc (0::nat) \<le> nat \<longrightarrow> map f [Suc (0::nat)..<nat] @ [f nat] = map (\<lambda>i::nat. f (Suc i)) [0::nat..<nat]"
  by (induct_tac nat, simp+)
qed

lemma forall_ex_fun: "finite S \<Longrightarrow> (\<forall> x \<in> S. (\<exists> y. P y x)) \<longrightarrow> (\<exists> f. \<forall> x \<in> S. P (f x) x)"
proof (erule finite_induct, simp)
  fix F x
  assume a: "finite F" and b: "(x :: 'a) \<notin> F"
  assume c: "(\<forall>x::'a\<in>F. \<exists>y::'b. P y x) \<longrightarrow> (\<exists>f::'a \<Rightarrow> 'b. \<forall>x::'a\<in>F. P (f x) x)"
  show "(\<forall>x::'a\<in>insert x F. \<exists>y::'b. P y x) \<longrightarrow> (\<exists>f::'a \<Rightarrow> 'b. \<forall>x::'a\<in>insert x F. P (f x) x)" 
  proof (clarify)
    assume d: "(\<forall>x::'a\<in>insert x F. \<exists>y::'b. P y x)"
    have "(\<forall>x::'a\<in>F. \<exists>y::'b. P y x)" using b d by simp
    hence "\<exists>f::'a \<Rightarrow> 'b. \<forall>x::'a\<in>F. P (f x) x" using c
      by (rule_tac P = "(\<forall>x::'a\<in>F. \<exists>y::'b. P y x)" in mp)
    from this obtain f where f: "\<forall>x::'a\<in>F. P (f x) x" by (erule exE)
    from d obtain y where "P y x" by blast
    thus "(\<exists>f::'a \<Rightarrow> 'b. \<forall>x::'a\<in>insert x F. P (f x) x)" using f 
      by (rule_tac x = "\<lambda> z. if z = x then y else f z" in exI, simp)
  qed
qed

primrec nodup :: "['a, 'a list] \<Rightarrow> bool"
  where 
    nodup_nil: "nodup a [] = True" |
    nodup_step: "nodup a (x # ls) = (if x = a then (a \<notin> (set ls)) else nodup a ls)"

definition nodup_all:: "'a list \<Rightarrow> bool"
  where
    "nodup_all l \<equiv> \<forall> x \<in> set l. nodup x l"

lemma nodup_all_lem[rule_format]: 
  "nodup_all (x1 # a # l) \<longrightarrow> (insert x1 (insert a (set l)) - {x1}) = insert a (set l)"
proof (rule_tac list = l in list.induct, (simp add: nodup_all_def)+)
qed

lemma nodup_all_tl[rule_format]: "nodup_all (x # l) \<longrightarrow> nodup_all l"  
proof (rule_tac list = l in list.induct, (simp add: nodup_all_def)+)
qed

lemma finite_nodup: "finite I \<Longrightarrow> \<exists> l. set l = I \<and> nodup_all l"
proof (erule finite.induct)
  show " \<exists>l::'a list. set l = {} \<and> nodup_all l"
    by (rule_tac x = "[]" in exI, simp add: nodup_all_def)
next show "\<And>(A::'a set) a::'a.
       finite A \<Longrightarrow> \<exists>l::'a list. set l = A \<and> nodup_all l \<Longrightarrow> \<exists>l::'a list. set l = insert a A \<and> nodup_all l"
    by (metis (full_types) List.set_insert insert_absorb insert_iff nodup_all_def nodup_step not_in_set_insert)
qed

lemma Compl_step3: "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow>
     ( \<forall> x \<in> I.  x \<in> s \<or> (\<exists> (sl :: ((('s :: state) set)list)). 
                  (sl \<noteq> []) \<and> (tl sl \<noteq> []) \<and>
                 (sl ! 0, sl ! (length sl - 1)) = ({x},s) \<and>
                 (\<forall> i < (length sl - 1).  \<turnstile> \<N>\<^bsub>(sl ! i,sl ! (i+1) )\<^esub>
                         )) \<Longrightarrow> 
     (\<exists> lI. set lI = {x :: 's :: state. x \<in> I \<and> x \<notin> s} \<and> (\<exists> Sj :: ((('s :: state) set)list) list. 
               length Sj = length lI \<and> nodup_all lI \<and>
            (\<forall> j < length Sj. (((Sj ! j)  \<noteq> []) \<and> (tl (Sj ! j) \<noteq> []) \<and>
                 ((Sj ! j) ! 0, (Sj ! j) ! (length (Sj ! j) - 1)) = ({lI ! j},s) \<and>
                 (\<forall> i < (length (Sj ! j) - 1).  \<turnstile> \<N>\<^bsub>((Sj ! j) ! i, (Sj ! j) ! (i+1) )\<^esub>
                         ))))))"  
proof -
  assume i: "I \<noteq> {}" and f: "finite I" and
      fa: "\<forall>x::'s\<in>I.
       x \<in> s \<or>
       (\<exists>sl::'s set list.
           sl \<noteq> [] \<and>
           tl sl \<noteq> [] \<and>
           (sl ! (0::nat), sl ! (length sl - (1::nat))) = ({x}, s) \<and>
           (\<forall>i<length sl - (1::nat). \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1::nat)))\<^esub>))"
  have a: "\<exists> lI. set lI = {x::'s \<in> I. x \<notin> s} \<and> nodup_all lI"
    by (simp add: f finite_nodup)
  from this obtain lI where b: "set lI = {x::'s \<in> I. x \<notin> s} \<and> nodup_all lI"
    by (erule exE)
  thus "\<exists>lI::'s list.
       set lI = {x::'s \<in> I. x \<notin> s} \<and>
       (\<exists>Sj::'s set list list.
           length Sj = length lI \<and>
           nodup_all lI \<and>
           (\<forall>j<length Sj.
               Sj ! j \<noteq> [] \<and>
               tl (Sj ! j) \<noteq> [] \<and>
               (Sj ! j ! (0::nat), Sj ! j ! (length (Sj ! j) - (1::nat))) = ({lI ! j}, s) \<and>
               (\<forall>i<length (Sj ! j) - (1::nat). \<turnstile>\<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1::nat)))\<^esub>)))"
    apply (rule_tac x = lI in exI)
    apply (rule conjI)
     apply (erule conjE, assumption)
  proof -
    have c:  "\<forall> x \<in> set(lI). (\<exists> sl::'s set list.
              sl \<noteq> [] \<and>
              tl sl \<noteq> [] \<and>
              (sl ! (0::nat), sl ! (length sl - (1::nat))) = ({x}, s) \<and>
              (\<forall>i<length sl - (1::nat). \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1::nat)))\<^esub>))"
      using b fa by fastforce
    thus "\<exists>Sj::'s set list list.
       length Sj = length lI \<and>
       nodup_all lI \<and>
       (\<forall>j<length Sj.
           Sj ! j \<noteq> [] \<and>
           tl (Sj ! j) \<noteq> [] \<and>
           (Sj ! j ! (0::nat), Sj ! j ! (length (Sj ! j) - (1::nat))) = ({lI ! j}, s) \<and>
           (\<forall>i<length (Sj ! j) - (1::nat). \<turnstile>\<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1::nat)))\<^esub>))"
     apply (subgoal_tac "finite (set lI)")
     apply (rotate_tac -1)
     apply (drule forall_ex_fun)
     apply (drule mp)
     apply assumption
     apply (erule exE)
     apply (rule_tac x = "[f (lI ! j). j \<leftarrow> [0..<(length lI)]]" in exI)
     apply simp
     apply (insert b)
     apply (erule conjE, assumption)
     apply (rule_tac A = "set lI" and B = I in finite_subset)
     apply blast
     by (rule f)
  qed
qed

subsubsection \<open>Lemma @{text \<open>Compl_step4\<close>}\<close>
text \<open>Again, we need some additional lemmas first.\<close>
lemma list_one_tl_empty[rule_format]: "length l = Suc (0 :: nat) \<longrightarrow> tl l = []"
proof (rule_tac list = l in list.induct, simp+)
qed

lemma list_two_tl_not_empty[rule_format]: "\<forall> list. length l = Suc (Suc (length list)) \<longrightarrow> tl l \<noteq> []"  
proof (rule_tac list = l in list.induct, simp+, force)
qed

lemma or_empty: "\<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>({}, s)\<^esup>)" 
proof (simp add: att_or)
qed

text \<open>Note, this is not valid for any l, i.e., @{text \<open>\<turnstile> l \<oplus>\<^sub>\<or>\<^bsup>({}, s)\<^esup>\<close>} is not a theorem.\<close>

lemma list_or_upt[rule_format]:
 "\<forall> l . lI \<noteq> [] \<longrightarrow> length l = length lI \<longrightarrow> nodup_all lI \<longrightarrow>
  (\<forall> i < length lI. (\<turnstile> (l ! i)) \<and> (attack (l ! i) = ({lI ! i}, s))) 
                \<longrightarrow> ( \<turnstile> (l \<oplus>\<^sub>\<or>\<^bsup>(set lI, s)\<^esup>))"     
proof (rule_tac list = lI in list.induct, simp, clarify)
  fix x1 x2 l
  show "\<forall>l::'a attree list.
          x2 \<noteq> [] \<longrightarrow>
          length l = length x2 \<longrightarrow>
          nodup_all x2 \<longrightarrow>
          (\<forall>i<length x2. \<turnstile>(l ! i) \<and> attack (l ! i) = ({x2 ! i}, s)) \<longrightarrow> \<turnstile>(l \<oplus>\<^sub>\<or>\<^bsup>(set x2, s)\<^esup>) \<Longrightarrow>
       x1 # x2 \<noteq> [] \<Longrightarrow>
       length l = length (x1 # x2) \<Longrightarrow>
       nodup_all (x1 # x2) \<Longrightarrow>
       \<forall>i<length (x1 # x2). \<turnstile>(l ! i) \<and> attack (l ! i) = ({(x1 # x2) ! i}, s) \<Longrightarrow> \<turnstile>(l \<oplus>\<^sub>\<or>\<^bsup>(set (x1 # x2), s)\<^esup>)"
    apply (case_tac x2, simp, subst att_or, case_tac l, simp+)
    text \<open>Case @{text \<open>\<forall>i<Suc (Suc (length list)). \<turnstile>l ! i \<and> attack (l ! i) = ({(x1 # a # list) ! i}, s) \<Longrightarrow>
       x2 = a # list \<Longrightarrow>  \<turnstile>l \<oplus>\<^sub>\<or>\<^bsup>(insert x1 (insert a (set list)), s)\<^esup>\<close>}\<close>
    apply (subst att_or, case_tac l, simp, clarify, simp, rename_tac lista, case_tac lista, simp+)
    text \<open>Remaining conjunct of three conditions: @{text \<open> \<turnstile>aa \<and>
       fst (attack aa) \<subseteq> insert x1 (insert a (set list)) \<and>
       snd (attack aa) \<subseteq> s \<and> \<turnstile>ab # listb \<oplus>\<^sub>\<or>\<^bsup>(insert x1 (insert a (set list)) - fst (attack aa), s)\<^esup>\<close>}\<close>
    apply (rule conjI)
    text \<open>First condition @{text \<open> \<turnstile>aa\<close>}\<close>
     apply (drule_tac x = 0 in spec, drule mp, simp, (erule conjE)+, simp, rule conjI)
    text \<open>Second condition @{text \<open>fst (attack aa) \<subseteq> insert x1 (insert a (set list))\<close>}\<close>
     apply (drule_tac x = 0 in spec, drule mp, simp, erule conjE, simp)
    text \<open>The remaining conditions 

          @{text \<open>snd (attack aa) \<subseteq> s \<and> \<turnstile>ab # listb \<oplus>\<^sub>\<or>\<^bsup>(insert x1 (insert a (set list)) - fst (attack aa), s)\<^esup>\<close>}
 
          are solved automatically!\<close>
    by (metis Suc_mono add.right_neutral add_Suc_right list.size(4) nodup_all_lem nodup_all_tl nth_Cons_0 nth_Cons_Suc order_refl prod.sel(1) prod.sel(2) zero_less_Suc)
qed

lemma app_tl_empty_hd[rule_format]: "tl (l @ [a]) = [] \<longrightarrow> hd (l @ [a]) = a"
  by (induction l) auto
       
lemma tl_hd_empty[rule_format]: "tl (l @ [a]) = [] \<longrightarrow> l = []"
  by (induction l) auto

lemma tl_hd_not_empty[rule_format]: "tl (l @ [a]) \<noteq> [] \<longrightarrow> l \<noteq> []"
  by (induction l) auto
  
lemma app_tl_empty_length[rule_format]: "tl (map f [0::nat..<length l] @ [a]) = []  
                                        \<Longrightarrow> l = []"
proof (drule tl_hd_empty, simp)
qed

lemma not_empty_hd_fst[rule_format]: "l \<noteq> [] \<longrightarrow> hd(l @ [a]) = l ! 0"
  by (induction l) auto
  
lemma app_tl_hd_list[rule_format]: "tl (map f [0::nat..<length l] @ [a]) \<noteq> []  
                             \<Longrightarrow> hd(map f [0::nat..<length l] @ [a]) = (map f [0::nat..<length l]) ! 0"
proof (drule tl_hd_not_empty, erule not_empty_hd_fst)
qed

lemma tl_app_in[rule_format]: "l \<noteq> [] \<longrightarrow>
   map f [0::nat..<(length l - (Suc 0:: nat))] @ [f(length l - (Suc 0 :: nat))] = map f [0::nat..<length l]"    
  by (induction l) auto

lemma map_fst[rule_format]: "n > 0 \<longrightarrow> map f [0::nat..<n] = f 0 # (map f [1..<n])"
  by (induction n) auto

lemma step_lem[rule_format]:  "l \<noteq> [] \<Longrightarrow>
       tl (map (\<lambda> i. f((x1 # a # l) ! i)((a # l) ! i)) [0::nat..<length l]) =
       map (\<lambda>i::nat. f((a # l) ! i)(l ! i)) [0::nat..<length l - (1::nat)]"
proof (simp)
  assume l: "l \<noteq> []"
    have a: "map (\<lambda>i::nat. f ((x1 # a # l) ! i) ((a # l) ! i)) [0::nat..<length l] =
                 (f(x1)(a) # (map (\<lambda>i::nat. f ((a # l) ! i) (l ! i)) [0::nat..<(length l - 1)]))"
    proof -
      have b : "map (\<lambda>i::nat. f ((x1 # a # l) ! i) ((a # l) ! i)) [0::nat..<length l] =
                     f ((x1 # a # l) ! 0) ((a # l) ! 0) # 
                     (map (\<lambda>i::nat. f ((x1 # a # l) ! i) ((a # l) ! i)) [1::nat..<length l])"
        by (rule map_fst, simp, rule l)
      have c: "map (\<lambda>i::nat. f ((x1 # a # l) ! i) ((a # l) ! i)) [Suc (0::nat)..<length l] =
                map (\<lambda>i::nat. f ((x1 # a # l) ! Suc i) ((a # l) ! Suc i)) [(0::nat)..<(length l - 1)]"
        by (subgoal_tac "[Suc (0::nat)..<length l] = map Suc [0..<(length l - 1)]", 
             simp, simp add: map_Suc_upt l)
      thus "map (\<lambda>i::nat. f ((x1 # a # l) ! i) ((a # l) ! i)) [0::nat..<length l] =
             f x1 a # map (\<lambda>i::nat. f ((a # l) ! i) (l ! i)) [0::nat..<length l - (1::nat)]"
         by (simp add: b c)
    qed
    thus "l \<noteq> [] \<Longrightarrow>
    tl (map (\<lambda>i::nat. f ((x1 # a # l) ! i) ((a # l) ! i)) [0::nat..<length l]) =
    map (\<lambda>i::nat. f ((a # l) ! i) (l ! i)) [0::nat..<length l - Suc (0::nat)]" 
      by (subst a, simp)
  qed

lemma step_lem2a[rule_format]: "0 < length list \<Longrightarrow> map (\<lambda>i::nat. \<N>\<^bsub>((x1 # a # list) ! i, (a # list) ! i)\<^esub>)
        [0::nat..<length list] @
       [\<N>\<^bsub>((x1 # a # list) ! length list, (a # list) ! length list)\<^esub>] =
       aa # listb \<longrightarrow> \<N>\<^bsub>((x1, a))\<^esub> = aa"
proof (subst map_fst, assumption, simp)
qed

lemma step_lem2b[rule_format]: "0 = length list \<Longrightarrow> map (\<lambda>i::nat. \<N>\<^bsub>((x1 # a # list) ! i, (a # list) ! i)\<^esub>)
        [0::nat..<length list] @
       [\<N>\<^bsub>((x1 # a # list) ! length list, (a # list) ! length list)\<^esub>] =
       aa # listb \<longrightarrow> \<N>\<^bsub>((x1, a))\<^esub> = aa"
proof (simp)
qed

lemma step_lem2: "map (\<lambda>i::nat. \<N>\<^bsub>((x1 # a # list) ! i, (a # list) ! i)\<^esub>)
        [0::nat..<length list] @
       [\<N>\<^bsub>((x1 # a # list) ! length list, (a # list) ! length list)\<^esub>] =
       aa # listb \<Longrightarrow> \<N>\<^bsub>((x1, a))\<^esub> = aa"
proof (case_tac "length list", rule step_lem2b, erule sym, assumption)
  show "\<And>nat::nat.
       map (\<lambda>i::nat. \<N>\<^bsub>((x1 # a # list) ! i, (a # list) ! i)\<^esub>) [0::nat..<length list] @
       [\<N>\<^bsub>((x1 # a # list) ! length list, (a # list) ! length list)\<^esub>] =
       aa # listb \<Longrightarrow>
       length list = Suc nat \<Longrightarrow> \<N>\<^bsub>(x1, a)\<^esub> = aa"
    by (rule_tac list = list in step_lem2a, simp)
qed

lemma base_list_and[rule_format]: "Sji \<noteq> [] \<longrightarrow> tl Sji \<noteq> [] \<longrightarrow>
         (\<forall> li.  Sji ! (0::nat) = li \<longrightarrow>
        Sji! (length (Sji) - 1) = s \<longrightarrow>
       (\<forall>i<length (Sji) - 1. \<turnstile>\<N>\<^bsub>(Sji ! i, Sji ! Suc i)\<^esub>) \<longrightarrow>
       \<turnstile> (map (\<lambda>i::nat. \<N>\<^bsub>(Sji ! i, Sji ! Suc i)\<^esub>)
          [0::nat..<length (Sji) - Suc (0::nat)] \<oplus>\<^sub>\<and>\<^bsup>(li, s)\<^esup>))"
proof (induction Sji)
  case Nil
  then show ?case by simp
next
  case (Cons a Sji)
  then show ?case 
    apply (subst att_and, case_tac Sji, simp, simp)
    apply (rule impI)+
  proof -
    fix aa list
    show "list \<noteq> [] \<longrightarrow>
       list ! (length list - Suc 0) = s \<longrightarrow>
       (\<forall>i<length list. \<turnstile>\<N>\<^bsub>((aa # list) ! i, list ! i)\<^esub>) \<longrightarrow>
       \<turnstile>(map (\<lambda>i. \<N>\<^bsub>((aa # list) ! i, list ! i)\<^esub>) [0..<length list] \<oplus>\<^sub>\<and>\<^bsup>(aa, s)\<^esup>) \<Longrightarrow>
       Sji = aa # list \<Longrightarrow>
       (aa # list) ! length list = s \<Longrightarrow>
       \<forall>i<Suc (length list). \<turnstile>\<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub> \<Longrightarrow>
       case map (\<lambda>i. \<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>) [0..<length list] @
            [\<N>\<^bsub>((a # aa # list) ! length list, s)\<^esub>] of
       [] \<Rightarrow> fst (a, s) \<subseteq> snd (a, s) | [aa] \<Rightarrow> \<turnstile>aa \<and> attack aa = (a, s)
       | aa # ab # list \<Rightarrow>
           \<turnstile>aa \<and> fst (attack aa) = fst (a, s) \<and> \<turnstile>(ab # list \<oplus>\<^sub>\<and>\<^bsup>(snd (attack aa), snd (a, s))\<^esup>)"
     proof (case_tac "map (\<lambda>i. \<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>) [0..<length list] @
            [\<N>\<^bsub>((a # aa # list) ! length list, s)\<^esub>]", simp, clarify, simp)
      fix ab lista
      show "list \<noteq> [] \<longrightarrow>
       (\<forall>i<length list. \<turnstile>\<N>\<^bsub>((aa # list) ! i, list ! i)\<^esub>) \<longrightarrow>
       \<turnstile>(map (\<lambda>i. \<N>\<^bsub>((aa # list) ! i, list ! i)\<^esub>)
          [0..<length list] \<oplus>\<^sub>\<and>\<^bsup>(aa, list ! (length list - Suc 0))\<^esup>) \<Longrightarrow>
       Sji = aa # list \<Longrightarrow>
       \<forall>i<Suc (length list). \<turnstile>\<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub> \<Longrightarrow>
       map (\<lambda>i. \<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>) [0..<length list] @
       [\<N>\<^bsub>((a # aa # list) ! length list, (aa # list) ! length list)\<^esub>] =
       ab # lista \<Longrightarrow>
       s = (aa # list) ! length list \<Longrightarrow>
       case lista of [] \<Rightarrow> \<turnstile>ab \<and> attack ab = (a, (aa # list) ! length list)
       | aba # lista \<Rightarrow>
           \<turnstile>ab \<and> fst (attack ab) = a \<and> \<turnstile>(aba # lista \<oplus>\<^sub>\<and>\<^bsup>(snd (attack ab), (aa # list) ! length list)\<^esup>)"
      proof (case_tac lista, simp, rule conjI, force, erule conjE,
               subgoal_tac "length list = 0", force, simp+)
        fix ac listb
        assume a0: "list \<noteq> [] \<longrightarrow>
                    (\<forall>i<length list. \<turnstile>\<N>\<^bsub>((aa # list) ! i, list ! i)\<^esub>) \<longrightarrow>
                     \<turnstile>(map (\<lambda>i. \<N>\<^bsub>((aa # list) ! i, list ! i)\<^esub>)
                      [0..<length list] \<oplus>\<^sub>\<and>\<^bsup>(aa, list ! (length list - Suc 0))\<^esup>)"
        and a1: "\<forall>i<Suc (length list). \<turnstile>\<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>"
        and a2: "map (\<lambda>i. \<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>) [0..<length list] @
                      [\<N>\<^bsub>((a # aa # list) ! length list, (aa # list) ! length list)\<^esub>] =
                 ab # ac # listb "
        have na: "\<N>\<^bsub>(a, aa)\<^esub> = ab" by (rule step_lem2, rule a2)
        have naaa: "list \<noteq> [] \<Longrightarrow> map (\<lambda>i::nat. \<N>\<^bsub>((aa # list) ! i, list ! i)\<^esub>) [0::nat..<length list] =
                    tl (map (\<lambda>i::nat. \<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>) [0::nat..<length list] @
                                          [\<N>\<^bsub>((a # aa # list) ! length list, (aa # list) ! length list)\<^esub>] )" 
             by (subgoal_tac "tl (map (\<lambda>i::nat. \<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>) [0::nat..<length list])
                    =  (map (\<lambda>i::nat. \<N>\<^bsub>((aa # list) ! i, (list) ! i)\<^esub>) [0::nat..<(length list - 1)])",
                 simp, rule sym, erule tl_app_in, erule step_lem)
        have naa: "list \<noteq> [] \<Longrightarrow> 
                     map (\<lambda>i. \<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>) [0..<length list] @
                     [\<N>\<^bsub>((a # aa # list) ! length list, (aa # list) ! length list)\<^esub>] =
                      ab # ac # listb \<Longrightarrow> 
                      map (\<lambda>i::nat. \<N>\<^bsub>((aa # list) ! i, list ! i)\<^esub>)
                         [0::nat..<length list] = ac # listb" by (drule naaa, simp)
        have nl: "list \<noteq> []" by (insert a2, force)
        show "s = (aa # list) ! length list \<Longrightarrow>
              \<turnstile>ab \<and> fst (attack ab) = a \<and> \<turnstile>(ac # listb \<oplus>\<^sub>\<and>\<^bsup>(snd (attack ab), (aa # list) ! length list)\<^esup>)"
          by (metis (no_types, lifting) One_nat_def Suc_less_eq a0 a1 a2 attack.simps(1) length_greater_0_conv na naa nl nth_Cons_0 nth_Cons_Suc nth_Cons_pos prod.sel(1) prod.sel(2) zero_less_Suc)
      qed
    qed
  qed
qed

lemma Compl_step4: "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow> \<not> I \<subseteq> s \<Longrightarrow>
(\<exists> lI. set lI = {x. x \<in> I \<and> x \<notin> s} \<and> (\<exists> Sj :: ((('s :: state) set)list) list. 
               length Sj = length lI \<and> nodup_all lI \<and>
            (\<forall> j < length Sj. (((Sj ! j)  \<noteq> []) \<and> (tl (Sj ! j) \<noteq> []) \<and>
                 ((Sj ! j) ! 0, (Sj ! j) ! (length (Sj ! j) - 1)) = ({lI ! j},s) \<and>
                 (\<forall> i < (length (Sj ! j) - 1).  \<turnstile> \<N>\<^bsub>((Sj ! j) ! i, (Sj ! j) ! (i+1) )\<^esub>
                         )))))
 \<Longrightarrow>  \<exists> (A :: ('s :: state) attree).  \<turnstile> A \<and> attack A = (I,s)"
proof (erule exE, erule conjE, erule exE, erule conjE)
  fix lI Sj
  assume  a: "I \<noteq> {}" and b: "finite I" and c: "\<not> I \<subseteq> s"
       and d: "set lI = {x::'s \<in> I. x \<notin> s}" and e: "length Sj = length lI"
       and f: "nodup_all lI \<and> 
              (\<forall>j<length Sj. Sj ! j \<noteq> [] \<and>
                             tl (Sj ! j) \<noteq> [] \<and>
           (Sj ! j ! (0::nat), Sj ! j ! (length (Sj ! j) - (1::nat))) = ({lI ! j}, s) \<and>
           (\<forall>i<length (Sj ! j) - (1::nat). \<turnstile>\<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1::nat)))\<^esub>))"
  show    "\<exists>A::'s attree. \<turnstile>A \<and> attack A = (I, s)"
    apply (rule_tac x = 
 "[([] \<oplus>\<^sub>\<or>\<^bsup>({x. x \<in> I \<and> x \<in> s}, s)\<^esup>),
    ([[ \<N>\<^bsub>((Sj ! j) ! i, (Sj ! j) ! (i + (1::nat)))\<^esub>. 
      i \<leftarrow> [0..<(length (Sj ! j)-(1::nat))]] \<oplus>\<^sub>\<and>\<^bsup>(({lI ! j},s))\<^esup>. j \<leftarrow> [0..<(length Sj)]]
     \<oplus>\<^sub>\<or>\<^bsup>({x. x \<in> I \<and> x \<notin> s},s)\<^esup>)] \<oplus>\<^sub>\<or>\<^bsup>(I, s)\<^esup>" in exI)
  proof 
    show  "\<turnstile>([[] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<in> s}, s)\<^esup>,
       map (\<lambda>j::nat.
               ((map (\<lambda>i::nat. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1::nat)))\<^esub>)
                [0::nat..<length (Sj ! j) - (1::nat)]) \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>))
       [0::nat..<length Sj] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<notin> s}, s)\<^esup>] \<oplus>\<^sub>\<or>\<^bsup>(I, s)\<^esup>)"
    proof -
      have g: "I - {x::'s \<in> I. x \<in> s} = {x::'s \<in> I. x \<notin> s}" by blast
      thus "\<turnstile>([[] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<in> s}, s)\<^esup>,
       (map (\<lambda>j::nat.
               ((map (\<lambda>i::nat. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1::nat)))\<^esub>)
                [0::nat..<length (Sj ! j) - (1::nat)]) \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>))
       [0::nat..<length Sj]) \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<notin> s}, s)\<^esup>] \<oplus>\<^sub>\<or>\<^bsup>(I, s)\<^esup>)"
        apply (subst att_or, simp)
      proof 
        show "I - {x \<in> I. x \<in> s} = {x \<in> I. x \<notin> s} \<Longrightarrow> \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>({x \<in> I. x \<in> s}, s)\<^esup>)"
          by (metis (no_types, lifting) CollectD att_or_empty_back subsetI)
      next show "I - {x \<in> I. x \<in> s} = {x \<in> I. x \<notin> s} \<Longrightarrow>
    \<turnstile>([map (\<lambda>j. ((map (\<lambda>i. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! Suc i)\<^esub>) [0..<length (Sj ! j) - Suc 0]) \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>))
        [0..<length Sj] \<oplus>\<^sub>\<or>\<^bsup>({x \<in> I. x \<notin> s}, s)\<^esup>] \<oplus>\<^sub>\<or>\<^bsup>({x \<in> I. x \<notin> s}, s)\<^esup>)"
          text \<open>Use lemma @{text \<open>list_or_upt\<close>} to distribute attack validity  over list lI\<close>
      proof (erule ssubst, subst att_or, simp, rule subst, rule d, rule_tac lI = lI in list_or_upt)
        show "lI \<noteq> []" 
        proof - 
          have "set lI \<noteq> {}"  
            apply(subst d)
          proof -
            have "\<exists> x. x \<in> I \<and> x \<notin> s" using c by blast
            from this obtain x where " x \<in> I \<and> x \<notin> s" by (erule exE)
            thus "{x::'s \<in> I. x \<notin> s} \<noteq> {}" by blast
          qed
          thus "lI \<noteq> []" by force
        qed  
      next show "(length
                 (map (\<lambda>j::nat.
                     ((map (\<lambda>i::nat. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! Suc i)\<^esub>)
                   [0::nat..<length (Sj ! j) - Suc (0::nat)]) \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>))
                 [0::nat..<length Sj])) =  (length lI)" by (simp add: e)
      next show "nodup_all lI" by (simp add: f)
      next show "\<And>i::nat.
       i < length lI \<Longrightarrow>
       \<turnstile>(map (\<lambda>j::nat.
                 ((map (\<lambda>i::nat. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! Suc i)\<^esub>)
                  [0::nat..<length (Sj ! j) - Suc (0::nat)]) \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>))
          [0::nat..<length Sj] !
         i) \<and>
       (attack
        (map (\<lambda>j::nat.
                 ((map (\<lambda>i::nat. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! Suc i)\<^esub>)
                  [0::nat..<length (Sj ! j) - Suc (0::nat)]) \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>))
          [0::nat..<length Sj] !
         i) =
       ({lI ! i}, s))"
        proof (simp add: a b c d e f)
          show "\<And>i::nat.
                i < length lI \<Longrightarrow>
                \<turnstile>(map (\<lambda>ia::nat. \<N>\<^bsub>(Sj ! i ! ia, Sj ! i ! Suc ia)\<^esub>)
                [0::nat..<length (Sj ! i) - Suc (0::nat)] \<oplus>\<^sub>\<and>\<^bsup>({lI ! i}, s)\<^esup>)"
          proof -
            have ff: "(\<forall>j<length Sj. Sj ! j \<noteq> [] \<and>
                                tl (Sj ! j) \<noteq> [] \<and>
                  (Sj ! j ! (0::nat), Sj ! j ! (length (Sj ! j) - (1::nat))) = ({lI ! j}, s) \<and>
                  (\<forall>i<length (Sj ! j) - (1::nat). \<turnstile>\<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1::nat)))\<^esub>))" 
              by (rule conjunct2, rule f)
            thus "\<And>i::nat.
                    i < length lI \<Longrightarrow>
                    \<turnstile>(map (\<lambda>ia::nat. \<N>\<^bsub>(Sj ! i ! ia, Sj ! i ! Suc ia)\<^esub>)
                    [0::nat..<length (Sj ! i) - Suc (0::nat)] \<oplus>\<^sub>\<and>\<^bsup>({lI ! i}, s)\<^esup>)"
              by (simp add: base_list_and e)          
          qed
        qed
      qed
    qed
  qed
next show "attack
     ([[] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<in> s}, s)\<^esup>,
       (map (\<lambda>j::nat.
               ((map (\<lambda>i::nat. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1::nat)))\<^esub>)
                [0::nat..<length (Sj ! j) - (1::nat)]) \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>))
        [0::nat..<length Sj]) \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<notin> s}, s)\<^esup>] \<oplus>\<^sub>\<or>\<^bsup>(I, s)\<^esup>) =
    (I, s)"
   by simp
qed
qed

subsubsection \<open>Main Theorem Completeness\<close> 
theorem Completeness: "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow> 
Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s 
\<Longrightarrow> \<exists> (A :: ('s :: state) attree). \<turnstile> A \<and> attack A = (I,s)"
proof (case_tac "I \<subseteq> s")
  show "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow>
    Kripke {s::'s. \<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* s} I \<turnstile> EF s \<Longrightarrow> I \<subseteq> s \<Longrightarrow> \<exists>A::'s attree. \<turnstile>A \<and> attack A = (I, s)"
    using att_or_empty_back attack.simps(3) by blast
next 
  show "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow>
    Kripke {s::'s. \<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* s} I \<turnstile> EF s \<Longrightarrow> \<not> I \<subseteq> s 
   \<Longrightarrow> \<exists>A::'s attree. \<turnstile>A \<and> attack A = (I, s)"
    by (iprover intro: Compl_step1 Compl_step2 Compl_step3 Compl_step4 elim: )
qed

subsubsection \<open>Contrapositions of Correctness and Completeness\<close>   
lemma contrapos_compl: 
  "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow> 
  (\<not> (\<exists> (A :: ('s :: state) attree). \<turnstile> A \<and> attack A = (I, - s))) \<Longrightarrow>
\<not> (Kripke {s. \<exists>i\<in>I. i \<rightarrow>\<^sub>i* s} I \<turnstile> EF (- s))"
  using Completeness by auto

lemma contrapos_corr:   
"(\<not>(Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I  \<turnstile> EF s))
\<Longrightarrow> attack A = (I,s) 
\<Longrightarrow> \<not> (\<turnstile> A)"
  using AT_EF by blast

end