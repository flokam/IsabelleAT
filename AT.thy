theory AT
imports MC 
begin

(* Attack trees with a Kripke semantics;
 Generalised attacktree structure with only one generic base_attack type 'a
  that encompasses all of abstract attack annotation 'a (could be string but also
  the type of predicates for representing the actual attack predicate
  inside the attack tree explicitly rather than just its name) as
  well as the type of base attacks.
   For the example Infrastructure framework 'a would contain the actor and the action
     *)
datatype ('s :: state) attree = BaseAttack "('s set) * ('s set)" ("\<N>\<^bsub>(_)\<^esub>") |
                  AndAttack "('s attree) list" "('s set) * ('s set)" ("_ \<oplus>\<^sub>\<and>\<^bsup>(_)\<^esup>" 50) | 
                  OrAttack  "('s attree) list" "('s set) * ('s set)" ("_ \<oplus>\<^sub>\<or>\<^bsup>(_)\<^esup>" 51)

             
primrec attack :: "('s :: state) attree \<Rightarrow> ('s set) * ('s set)"
  where 
"attack (BaseAttack b) = b"|
"attack (AndAttack as s) = s"  | 
"attack (OrAttack as s) = s"

(* The relation refines_to "constructs" the attack tree. Here the above 
   defined attack vectors are used to define how nodes in an attack tree 
   can be expanded into more detailed (refined) attack sequences. This 
   process of refinement "\<sqsubseteq>" allows to eventually reach a fully detailed
   attack that can then be proved using "\<turnstile>" .
  New idea for a general refinement and proof calculus only assuming a
  general state transition:
  'a attree nodes consist two sets of 'a states (I0,P) where I0 represents
  the initial states for that attack and P represents the property that
  defines the attack, e.g. enables cockpit Eve put.
  The refinement can now similarly to the special version for Insiders
  relate pre-state(s) with state transition and post-state.
  End-points, i.e. base attacks, are those where either no state change or
  just one step. This is subject of the \<turnstile> rules. The refinement rules
  are probably mostly unchanged yet there might be an additional one for
  or because the pre-set allows different alternative starting points
  for disjunctive attacks. 
*)
inductive refines_to :: "[('s :: state) attree, 's attree] \<Rightarrow> bool" ("_ \<sqsubseteq> _" 50)
where 
refI: "\<lbrakk>  A = ((l @ [ \<N>\<^bsub>(si',si'')\<^esub>] @ l'')\<oplus>\<^sub>\<and>\<^bsup>(si,si''')\<^esup> );
          A' = (l' \<oplus>\<^sub>\<and>\<^bsup>(si',si'')\<^esup>);
          A'' = (l @ l' @ l'' \<oplus>\<^sub>\<and>\<^bsup>(si,si''')\<^esup>)
        \<rbrakk> \<Longrightarrow> A \<sqsubseteq> A''"| 
ref_or: "\<lbrakk> as \<noteq> []; \<forall> A' \<in> set(as). A  \<sqsubseteq> A'\<and> attack A = s \<rbrakk> \<Longrightarrow> A \<sqsubseteq> as \<oplus>\<^sub>\<or>\<^bsup>s\<^esup>" |
ref_trans: "\<lbrakk> A \<sqsubseteq> A'; A' \<sqsubseteq> A'' \<rbrakk> \<Longrightarrow> A \<sqsubseteq> A''"|
ref_refl : "A \<sqsubseteq> A"

lemma non_empty_list_induction[rule_format] : "(\<forall> a . (P::'a::type list \<Rightarrow> bool) [a]) \<longrightarrow>
(\<forall> (x1::'a::type) x2::'a::type list. P x2 \<longrightarrow> P (x1 # x2)) \<longrightarrow>
(list \<noteq> [] \<longrightarrow> P (list::'a::type list))"    
proof (rule list.induct) 
  show "(\<forall>a::'a. P [a]) \<longrightarrow> (\<forall>(x1::'a) x2::'a list. P x2 \<longrightarrow> P (x1 # x2)) \<longrightarrow> [] \<noteq> [] \<longrightarrow> P []"
    by simp
next show "\<And>(x1::'a) x2::'a list.
       (\<forall>a::'a. P [a]) \<longrightarrow> (\<forall>(x1::'a) x2::'a list. P x2 \<longrightarrow> P (x1 # x2)) \<longrightarrow> x2 \<noteq> [] \<longrightarrow> P x2 \<Longrightarrow>
       (\<forall>a::'a. P [a]) \<longrightarrow> (\<forall>(x1::'a) x2::'a list. P x2 \<longrightarrow> P (x1 # x2)) \<longrightarrow> x1 # x2 \<noteq> [] \<longrightarrow> P (x1 # x2)"
  apply clarify
  apply (case_tac x2)
  by simp+
qed

lemma non_empty_list_induction2: "(\<And> a . (P::'a::type list \<Rightarrow> bool) [a]) \<Longrightarrow>
(\<And> (x1::'a::type) x2::'a::type list. P x2 \<Longrightarrow> P (x1 # x2)) \<Longrightarrow>
(list \<noteq> [] \<longrightarrow> P (list::'a::type list))"    
proof (rule impI)
  show "(\<And> a . (P::'a::type list \<Rightarrow> bool) [a]) \<Longrightarrow>
        (\<And> (x1::'a::type) x2::'a::type list. P x2 \<Longrightarrow> P (x1 # x2)) \<Longrightarrow>
        (list \<noteq> [] \<Longrightarrow> P (list::'a::type list))" 
  apply (rule non_empty_list_induction)
  by simp+
qed

(* Central constructive predicate to define the validity of an attack tree *)
fun is_attack_tree :: "[('s :: state) attree] \<Rightarrow> bool"  ("\<turnstile>_" 50) 
where 
att_base:  "(\<turnstile> \<N>\<^bsub>s\<^esub>) = ( (\<forall> x \<in> (fst s). (\<exists> y \<in> (snd s). x  \<rightarrow>\<^sub>i y )))" |
att_and: " (\<turnstile> (As :: ('s :: state attree list)) \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>) = 
               (case As of
                  [] \<Rightarrow> (fst s \<subseteq> snd s)
                | [a] \<Rightarrow> ( \<turnstile> a \<and> attack a = s) 
                | (a # l) \<Rightarrow> (( \<turnstile> a) \<and>  (fst(attack a) = fst s) \<and> 
                            ( \<turnstile> l \<oplus>\<^sub>\<and>\<^bsup>(snd(attack a),snd(s))\<^esup>)))" |
att_or: " (\<turnstile> (As :: ('s :: state attree list)) \<oplus>\<^sub>\<or>\<^bsup>s\<^esup>) = 
               (case As of 
                  [] \<Rightarrow> (fst s \<subseteq> snd s) 
                | [a] \<Rightarrow> ( \<turnstile> a \<and> (fst(attack a) \<supseteq> fst s) \<and> (snd(attack a) \<subseteq> snd s)) 
                | (a # l) \<Rightarrow> (( \<turnstile> a) \<and> fst(attack a) \<subseteq> fst s \<and> 
                              snd(attack a) \<subseteq> snd s \<and>
                       ( \<turnstile> l \<oplus>\<^sub>\<or>\<^bsup>(fst s - fst(attack a), snd s)\<^esup>)))" 

export_code is_attack_tree in Scala    

lemma att_and_one: assumes "\<turnstile> a" and  "attack a = s"
  shows  "\<turnstile>[a] \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>"
proof -
  show " \<turnstile>[a] \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>" using assms
    apply (subst att_and)
    by (simp del: att_and att_or)
qed

declare is_attack_tree.simps[simp del]
  
lemma att_and_empty[rule_format] : " \<turnstile>[] \<oplus>\<^sub>\<and>\<^bsup>(s', s'')\<^esup> \<longrightarrow> s' \<subseteq> s''"
proof -
  show " \<turnstile>[] \<oplus>\<^sub>\<and>\<^bsup>(s', s'')\<^esup> \<longrightarrow> s' \<subseteq> s''"
   apply (subst att_and)  
   by simp
qed

lemma att_and_empty2: " \<turnstile>[] \<oplus>\<^sub>\<and>\<^bsup>(s, s)\<^esup>"
proof -
  show " \<turnstile>[] \<oplus>\<^sub>\<and>\<^bsup>(s, s)\<^esup>"
    apply (subst att_and)  
    by simp
qed

lemma att_or_empty[rule_format] : " \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>(s', s'')\<^esup> \<longrightarrow> s' \<subseteq> s''"
proof -
  show " \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>(s', s'')\<^esup> \<longrightarrow> s' \<subseteq> s''"
    apply (subst att_or)  
    by simp
qed

lemma att_or_empty_back[rule_format]: " s' \<subseteq> s'' \<longrightarrow>  \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>(s', s'')\<^esup>"
proof -
  show " s' \<subseteq> s'' \<longrightarrow>  \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>(s', s'')\<^esup>"
   apply (subst att_or)
   by simp
qed

lemma att_or_empty_rev: assumes "\<turnstile> l \<oplus>\<^sub>\<or>\<^bsup>(s, s')\<^esup>" 
                  and "\<not>(s \<subseteq> s')" shows "l \<noteq> []"    
proof -
  show  "l \<noteq> []" using assms
    apply (rule_tac P = "l = []" in contrapos_nn)
    apply assumption
    apply (rule att_or_empty)
    by simp
qed

lemma att_or_empty2: " \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>(s, s)\<^esup>"
proof -
  show " \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>(s, s)\<^esup>"
    apply (subst att_or)
    by simp
qed

lemma att_andD1: " \<turnstile>x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> \<Longrightarrow> \<turnstile> x1"
proof -
  show " \<turnstile>x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> \<Longrightarrow> \<turnstile> x1"
    apply (case_tac x2)
    by (subst (asm) att_and, simp)+
qed

lemma att_and_nonemptyD2[rule_format] : 
       "(x2 \<noteq> [] \<longrightarrow> \<turnstile>x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> \<longrightarrow> \<turnstile> x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>)" 
proof -
  show "(x2 \<noteq> [] \<longrightarrow> \<turnstile>x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> \<longrightarrow> \<turnstile> x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>)" 
    apply (rule non_empty_list_induction2)
    by (subst att_and, simp)+
qed

lemma att_andD2 : " \<turnstile>x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> \<Longrightarrow> \<turnstile> x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>" 
proof -
  show " \<turnstile>x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> \<Longrightarrow> \<turnstile> x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>"
   apply (case_tac x2)
   apply (subst (asm) att_and)
   apply (subst att_and, simp)
   apply (rule att_and_nonemptyD2)
   apply simp
   by assumption
qed

lemma in_set_list_cons: "x \<in> set x2 \<Longrightarrow> x \<in> set (x1 # x2)"  
  by (rule List.list.set_intros(2))
    
lemma att_and_fst_lem[rule_format]: 
   " \<turnstile>x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup> \<longrightarrow> xa \<in> fst (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>))
                     \<longrightarrow> xa \<in> fst (attack x1)"  
proof -
  show " \<turnstile>x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup> \<longrightarrow> xa \<in> fst (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>))
                     \<longrightarrow> xa \<in> fst (attack x1)"  
   apply (induct_tac x2a)
   by (subst att_and, simp)+
qed

lemma att_orD1: " \<turnstile>x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<Longrightarrow> \<turnstile> x1"
proof -
  show " \<turnstile>x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<Longrightarrow> \<turnstile> x1"
   apply (case_tac x2)
   by (subst (asm) att_or, simp)+
qed
    
lemma att_or_snd_hd: " \<turnstile>a # list \<oplus>\<^sub>\<or>\<^bsup>(aa, b)\<^esup> \<Longrightarrow> snd(attack a) \<subseteq> b"
proof - 
  show " \<turnstile>a # list \<oplus>\<^sub>\<or>\<^bsup>(aa, b)\<^esup> \<Longrightarrow> snd(attack a) \<subseteq> b"
   apply (case_tac list)
   by (subst (asm) att_or, simp)+
qed
 
lemma att_or_singleton[rule_format]: 
   " \<turnstile>[x1] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow> \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>(fst x - fst (attack x1), snd x)\<^esup>" 
proof -
  show " \<turnstile>[x1] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow> \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>(fst x - fst (attack x1), snd x)\<^esup>" 
   apply (subst att_or)
   apply simp
   apply (rule impI)
   apply (rule att_or_empty_back)
   by blast
qed

lemma att_orD2[rule_format]: 
     " \<turnstile>x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow>  \<turnstile> x2 \<oplus>\<^sub>\<or>\<^bsup>(fst x - fst(attack x1), snd x)\<^esup>"
proof -
  show " \<turnstile>x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow>  \<turnstile> x2 \<oplus>\<^sub>\<or>\<^bsup>(fst x - fst(attack x1), snd x)\<^esup>"
   apply (case_tac x2)
   apply (rule impI)
   apply (subst att_or)
   apply simp
   apply (rule att_or_empty)
   apply (erule att_or_singleton)
   apply simp
   apply (subst att_or)
   by simp
qed

lemma att_or_snd_att[rule_format]: "\<forall> x. \<turnstile> x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow> (\<forall> a \<in> (set x2). snd(attack a) \<subseteq> snd x )" 
proof (induct_tac x2)
  show "\<forall>x::'a set \<times> 'a set.
       \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow> (\<forall>a::'a attree\<in>set []. snd (attack a) \<subseteq> snd x)"
    by (simp add: att_or)
next show "\<And>(a::'a attree) list::'a attree list.
       \<forall>x::'a set \<times> 'a set.
          \<turnstile>list \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow> (\<forall>a::'a attree\<in>set list. snd (attack a) \<subseteq> snd x) \<Longrightarrow>
       \<forall>x::'a set \<times> 'a set.
          \<turnstile>a # list \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow> (\<forall>a::'a attree\<in>set (a # list). snd (attack a) \<subseteq> snd x)"
    apply clarify
    apply (subgoal_tac "ab = a \<or> ab \<in> set list")
    apply (erule disjE)
    apply (drule att_or_snd_hd)
    apply simp
    apply (erule subsetD, assumption)
    apply (drule att_orD2)
    apply (drule_tac x = "(fst (aa, b) - fst (attack a), snd (aa, b))" in spec)
    apply (drule mp, assumption)
    apply simp
    apply (drule_tac x = ab in bspec, assumption)
    apply (erule subsetD, assumption)
    by simp
qed

lemma singleton_or_lem: " \<turnstile>[x1] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>  \<Longrightarrow> fst x \<subseteq> fst(attack x1)"
proof -
  show " \<turnstile>[x1] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>  \<Longrightarrow> fst x \<subseteq> fst(attack x1)"
    by (subst (asm) att_or, simp)+
qed

lemma or_att_fst_sup0[rule_format]: "x2 \<noteq> [] \<longrightarrow> (\<forall> x. (\<turnstile> ((x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>):: ('s :: state) attree)) \<longrightarrow>
                      ((\<Union> y::'s attree\<in> set x2. fst (attack y)) \<supseteq> fst(x))) "
proof (induct_tac x2)
  show "[] \<noteq> [] \<longrightarrow>
    (\<forall>x::'s set \<times> 's set.
        \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow> fst x \<subseteq> (\<Union>y::'s attree\<in>set []. fst (attack y)))" by simp
  next show "\<And>(a::'s attree) list::'s attree list.
       list \<noteq> [] \<longrightarrow>  (\<forall>x::'s set \<times> 's set.
           \<turnstile>list \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow> fst x \<subseteq> (\<Union>y::'s attree\<in>set list. fst (attack y))) \<Longrightarrow>
       a # list \<noteq> [] \<longrightarrow>  (\<forall>x::'s set \<times> 's set.
           \<turnstile>a # list \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow> fst x \<subseteq> (\<Union>y::'s attree\<in>set (a # list). fst (attack y)))"
    apply (case_tac list)
    apply (subst att_or)
    apply simp
    apply clarify
    apply simp
    apply (frule att_orD2)
    apply (drule_tac x = "fst (ab, b) - fst (attack a)" in spec)
    apply (drule mp)
    apply (rule_tac x = "snd (ab, b)" in exI, assumption)
    apply simp
    apply (case_tac "x \<in> fst(attack a)")
    apply (erule disjI1)
    apply (subgoal_tac "x \<in> fst (attack aa) \<union> (\<Union>x::'s attree\<in>set lista. fst (attack x))")
    apply (erule UnE)
    apply (rule disjI2, erule disjI1)    
    apply (rule disjI2)+
    apply simp
    apply (erule subsetD)
    by simp
qed

lemma or_att_fst_sup: 
    assumes "(\<turnstile> ((x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>):: ('s :: state) attree))"
    shows   "((\<Union> y::'s attree\<in> set (x1 # x2). fst (attack y)) \<supseteq> fst(x))"
proof -
  show "((\<Union> y::('s :: state) attree\<in> set (x1 # x2). fst (attack y)) \<supseteq> fst(x))" 
    apply (rule or_att_fst_sup0)
    apply simp
    by (rule assms)
qed

(***** att_elem_seq is the main lemma for Correctness. ******
  It shows that for a given attack tree x1, for each element in the set of start sets 
  of the first attack, we can reach in zero or more steps a state in the states in which 
  the attack is successful (the final attack state snd(attack x1)).
  This proof is a Big alternative to an earlier version of the proof with
  first_step etc that mapped first on a sequence of sets of states .
*)    
lemma att_elem_seq[rule_format]: "\<turnstile> x1 \<longrightarrow> (\<forall> x \<in> fst(attack x1).
                     (\<exists> y. y \<in> snd(attack x1) \<and> x \<rightarrow>\<^sub>i* y))"
(* first attack tree induction *)
proof (induct_tac x1)
  (* base case *)
    show "\<And>x::'a set \<times> 'a set. \<turnstile>\<N>\<^bsub>x\<^esub> \<longrightarrow> (\<forall>xa::'a\<in>fst (attack \<N>\<^bsub>x\<^esub>). \<exists>y::'a. y \<in> snd (attack \<N>\<^bsub>x\<^esub>) \<and> xa \<rightarrow>\<^sub>i* y)"
      apply (simp add: att_base)
      apply clarify
      apply simp
      apply (drule_tac x = xa in bspec,assumption)
      apply (erule bexE)
      apply (rule_tac x = x in exI)
      apply (rule conjI, assumption)
      apply (simp add: state_transition_refl_def)
      by force
(* second case \<and> -- setting it for induction *)
  next show "\<And>(x1a::'a attree list) x2::'a set \<times> 'a set.
       (\<And>x1aa::'a attree.
           x1aa \<in> set x1a \<Longrightarrow>
           \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<Longrightarrow>
       \<turnstile>x1a \<oplus>\<^sub>\<and>\<^bsup>x2\<^esup> \<longrightarrow>
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
(* induction for \<and>*)
    proof (rule_tac list = "x1a" in list.induct)
      show "(\<forall>x1aa::'a attree.
           x1aa \<in> set [] \<longrightarrow>
           \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<longrightarrow>
       (\<forall>x::'a set \<times> 'a set.
           \<turnstile>[] \<oplus>\<^sub>\<and>\<^bsup>x\<^esup> \<longrightarrow>
           (\<forall>xa::'a\<in>fst (attack ([] \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack ([] \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y))"
        apply clarify
        apply simp
        apply (rule_tac x = "xa" in exI)
        apply (rule_tac conjI)
        apply (drule att_and_empty) 
        apply (erule subsetD, assumption)
        by (simp add: state_transition_refl_def)
      (* \<and> induction case nonempty  *)
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
           (\<turnstile>x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<longrightarrow>
           ((\<forall>xa::'a\<in>fst (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y))) \<Longrightarrow>
       ((\<forall>x1aa::'a attree.
           (x1aa \<in> set (x1 # x2a)) \<longrightarrow>
           (\<turnstile>x1aa) \<longrightarrow> ((\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y))) \<longrightarrow>
       (\<forall>x::'a set \<times> 'a set.
          ( \<turnstile>x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<longrightarrow>
           (\<forall>xa::'a\<in>fst (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)).
               (\<exists>y::'a. y \<in> snd (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> (xa \<rightarrow>\<^sub>i* y)))))"
      apply (rule impI, rule allI, rule impI)
      (* free IH *)
      apply (subgoal_tac " (\<forall>x::'a set \<times> 'a set.
                             \<turnstile>x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup> \<longrightarrow>
                             (\<forall>xa::'a\<in>fst (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)).
                              \<exists>y::'a. y \<in> snd (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y))")
      prefer 2
      (* *)
      apply (rule mp)
      apply assumption
      apply (rule allI)
      apply (rule impI)+
      apply (rotate_tac -4)
      apply (drule_tac x = x1aa in spec)
      apply (rotate_tac -1)
      apply (drule mp)
      apply (erule in_set_list_cons)
      apply (erule mp, assumption)
      proof -
        show "\<And>(x1a::'a attree list) (x2::'a set \<times> 'a set) (x1::'a attree) (x2a::'a attree list) x::'a set \<times> 'a set.
       \<forall>x1aa::'a attree.
          x1aa \<in> set (x1 # x2a) \<longrightarrow>
          \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y) \<Longrightarrow>
       \<turnstile>x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup> \<Longrightarrow>
       \<forall>x::'a set \<times> 'a set.
          \<turnstile>x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup> \<longrightarrow>
          (\<forall>xa::'a\<in>fst (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y) \<Longrightarrow>
       \<forall>xa::'a\<in>fst (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y"
       apply (rule ballI)
       (* prepare the steps *)
       apply (drule_tac x = "(snd(attack x1), snd x)" in spec)
       apply (rotate_tac -1)
       apply (erule impE)
       apply (erule att_andD2)
       (* premise for x1 *)
       apply (drule_tac x = x1 in spec)
       apply (drule mp)
       apply simp
       apply (drule mp)
       apply (erule att_andD1)
       (* instantiate first step for xa *)
       apply (rotate_tac -1)
       apply (drule_tac x = xa in bspec)
       apply (erule att_and_fst_lem, assumption)
       apply (erule exE)
       apply (erule conjE)
       (* take this y and put it as first into the second part *)
       apply (drule_tac x = y in bspec)
       apply simp
       apply (erule exE)
       apply (erule conjE)
       (* bind the first xa \<rightarrow>\<^sub>i* y  and second y \<rightarrow>\<^sub>i* ya together for solution *)
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
(* or_attack case ! *) 
next show "\<And>(x1a::'a attree list) x2::'a set \<times> 'a set.
       (\<And>x1aa::'a attree.
           x1aa \<in> set x1a \<Longrightarrow>
           \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<Longrightarrow>
       \<turnstile>x1a \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup> \<longrightarrow>
       (\<forall>x::'a\<in>fst (attack (x1a \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x1a \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>)) \<and> x \<rightarrow>\<^sub>i* y)"
    (* set up for induction *)
     apply (rule_tac x = x2 in spec)
     apply (subgoal_tac "(\<forall> x1aa::'a attree.
                                x1aa \<in> set x1a \<longrightarrow>
                                \<turnstile>x1aa \<longrightarrow>
                                (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y))") 
     apply (rule mp)
     prefer 2
     apply (rotate_tac -1)
     apply assumption
  (*   apply (thin_tac "(\<And>x1aa::'a attree.
           x1aa \<in> set x1a \<Longrightarrow>
           \<turnstile>x1aa \<longrightarrow>
           (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y))") *)
  proof (rule_tac list = "x1a" in list.induct)
  (* \<and> induction empty case *)
    show "(\<forall>x1aa::'a attree.
           x1aa \<in> set [] \<longrightarrow>
           \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<longrightarrow>
       (\<forall>x::'a set \<times> 'a set.
           \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow>
           (\<forall>xa::'a\<in>fst (attack ([] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack ([] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y))"
     apply clarify
     apply simp
     apply (rule_tac x = "xa" in exI)
     apply (rule_tac conjI)
     apply (drule att_or_empty) 
     apply (erule subsetD, assumption)
     by (simp add: state_transition_refl_def)
(* \<or> induction case nonempty *)
 next show "\<And>(x1a::'a attree list) (x2::'a set \<times> 'a set) (x1::'a attree) x2a::'a attree list.
       (\<And>x1aa::'a attree.
           (x1aa \<in> set x1a) \<Longrightarrow>
           (\<turnstile>x1aa) \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). (\<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y))) \<Longrightarrow>
       \<forall>x1aa::'a attree.
          (x1aa \<in> set x1a) \<longrightarrow>
          (\<turnstile>x1aa) \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). (\<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<Longrightarrow>
       (\<forall>x1aa::'a attree.
           (x1aa \<in> set x2a) \<longrightarrow>
           (\<turnstile>x1aa) \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). (\<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y))) \<longrightarrow>
       (\<forall>x::'a set \<times> 'a set.
           (\<turnstile>x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow>
           (\<forall>xa::'a\<in>fst (attack (x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)). (\<exists>y::'a. y \<in> snd (attack (x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y))) \<Longrightarrow>
       (\<forall>x1aa::'a attree.
           (x1aa \<in> set (x1 # x2a)) \<longrightarrow>
           (\<turnstile>x1aa) \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<longrightarrow>
       (\<forall>x::'a set \<times> 'a set.
           (\<turnstile>x1 # x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow>
           (\<forall>xa::'a\<in>fst (attack (x1 # x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)).
               (\<exists>y::'a. y \<in> snd (attack (x1 # x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y)))" 
      apply (rule impI, rule allI, rule impI)
      (* free IH *)
      apply (subgoal_tac "(\<forall>x::'a set \<times> 'a set.
                           \<turnstile>x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow>
                            (\<forall>xa::'a\<in>fst (attack (x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)).
                             \<exists>y::'a. y \<in> snd (attack (x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y)) ")
      prefer 2
      (* *)
      apply (rule mp)
      apply assumption
      apply (rule allI)
      apply (rule impI)+
      apply (rotate_tac -4)
      apply (drule_tac x = x1aa in spec)
      apply (rotate_tac -1)
      apply (drule mp)
      apply (erule in_set_list_cons)
      apply (erule mp, assumption)
      (* *)
   proof -
     show "\<And>(x1a::'a attree list) (x2::'a set \<times> 'a set) (x1::'a attree) (x2a::'a attree list) x::'a set \<times> 'a set.
       \<forall>x1aa::'a attree.
          x1aa \<in> set (x1 # x2a) \<longrightarrow>
          \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y) \<Longrightarrow>
       \<turnstile>x1 # x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<Longrightarrow>
       \<forall>x::'a set \<times> 'a set.
          \<turnstile>x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup> \<longrightarrow>
          (\<forall>xa::'a\<in>fst (attack (x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y) \<Longrightarrow>
       \<forall>xa::'a\<in>fst (attack (x1 # x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x1 # x2a \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y"
     apply (rule ballI)
     (* prepare the step for xa*)    
     apply (drule_tac x = x1 in spec)
     apply (drule mp)
     apply simp
     apply (drule mp)
     apply (erule att_orD1)
     apply simp
     (* apply or_att_fst_sup to infer from xa \<in> fst x that it is in
       ((\<Union> y::'s attree\<in> set (x1 # x2a). fst (attack y)). Then UnE should
       provide that xa \<in> fst (attack x1) or xa \<in> fst (attack x2) for some x2 \<in> (set x2a)  *)  
     apply (frule or_att_fst_sup)
     apply (drule subsetD, assumption)
     apply (erule UnionE)
     apply simp
     apply (erule disjE)
     (* case xa \<in> fst(attack x1) *)
     apply (drule_tac x = xa in bspec, erule subst, assumption)
     apply (erule exE)
     apply (erule conjE)
     apply (rule_tac x = y in exI)
     apply (rule conjI)
     apply (frule_tac a = x1 and x = x in att_or_snd_att)
     apply simp
     apply (erule subsetD, assumption)
     apply assumption
     (* second case: xa \<in> X; X \<in> (\<lambda>y::'a attree. fst (attack y)) ` set x2a *)
     apply (drule_tac x = "fst x - fst(attack x1)" in spec)
     apply (drule_tac x = "snd x" in spec)
     apply (drule mp)
     apply (erule att_orD2)
     apply (case_tac "xa \<in> fst(attack x1)")
     apply (drule_tac x = xa in bspec, assumption)
     apply (erule exE)
     apply (erule conjE)
     apply (rule_tac x = y in exI)
     apply (rule conjI)
     apply (frule_tac a = x1 and x = x in att_or_snd_att)
     apply simp
     apply (erule subsetD, assumption)
     apply assumption
     (*xa \<notin> fst (attack x1) *)
     apply (rotate_tac -2)
     apply (drule_tac x = xa in bspec)
     apply simp
     by assumption
   qed
   next show "\<And>(x1a::'a attree list) x2::'a set \<times> 'a set.
         (\<And>x1aa::'a attree.
             x1aa \<in> set x1a \<Longrightarrow>
             \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<Longrightarrow>
          \<forall>x1aa::'a attree.
              x1aa \<in> set x1a \<longrightarrow> \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)"
        by simp
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
          
(*** Valid refinements ****)      
definition valid_ref :: "[('s :: state) attree, 's attree] \<Rightarrow> bool" ("_ \<sqsubseteq>\<^sub>V _" 50)
  where
"A \<sqsubseteq>\<^sub>V A' \<equiv>  ( A \<sqsubseteq> A' \<and>  \<turnstile> A')"

definition ref_validity :: "[('s :: state) attree] \<Rightarrow> bool" ("\<turnstile>\<^sub>V _" 50)
  where
"\<turnstile>\<^sub>V A  \<equiv>  (\<exists> A'. A \<sqsubseteq>\<^sub>V A')"

lemma ref_valI: " A \<sqsubseteq> A'\<Longrightarrow>  \<turnstile> A' \<Longrightarrow> \<turnstile>\<^sub>V A"
proof (simp add: ref_validity_def valid_ref_def)
  show "A \<sqsubseteq> A' \<Longrightarrow> \<turnstile>A' \<Longrightarrow> \<exists>A'::'a attree. A \<sqsubseteq> A' \<and> \<turnstile>A'"
    by (rule exI, rule conjI)
qed

(* Main theorems of Correctness and Completeness
   between AT and Kripke, \<turnstile> (init K, p) \<equiv>  K \<turnstile> EF p *) 
(* This proof roughly goes in two steps:
    First, the attack can be refined into an or of single-step attack sequences: 
       \<turnstile> A \<Longrightarrow> 
       \<exists> A'.  A \<sqsubseteq> A' \<and> attack A = attack A' \<and>
          let seq = att_seq A' 
          in (\<forall> i < length seq. nth i seq \<rightarrow>\<^sub>i nth (Suc i) seq) 
    Second, let A' as in previous step, then for all these single-step seq, they 
    are witness for EF s, where s is the final state set of each seq:
    \<lbrakk> attack A = (I,s); seq = att_seq A;  
      (\<forall> i < length seq. nth i seq \<rightarrow>\<^sub>i nth (Suc i) seq) \<rbrakk>
    \<Longrightarrow> Kripke(I,  \<rightarrow>\<^sub>i) \<turnstile> EF s
Proof with induction over definition of EF 
*)    

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
  apply clarify
  apply (drule_tac x = "sl" in spec)
  apply (drule_tac x = "i - 1" in spec)
  apply (case_tac i)
by simp+
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
   apply clarify
   apply simp
   apply (drule_tac x = "sl" in spec)
   apply (drule_tac x = "i - 1" in spec)
   apply (case_tac i)
   by simp+
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
  apply clarify
  apply (case_tac "tl list = []")
  apply (drule tl_ne_ex)
  apply (erule exE)
  by simp+
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
    apply simp
    by (rule tl_eq3)
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

lemma attack_eq1: " snd (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) = snd (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>(snd (attack x1), snd x)\<^esup>))"
proof (simp)
qed

lemma attack_eq2 : " (fst (attack x1), snd (attack x1)) = attack x1"
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
next show "\<And>(as::'a attree list) (A::'a attree) s::'a set \<times> 'a set.
       as \<noteq> [] \<Longrightarrow>
       \<forall>A'::'a attree\<in>set as. (A \<sqsubseteq> A' \<and> attack A = attack A') \<and> attack A = s \<Longrightarrow>
       attack A = attack (as \<oplus>\<^sub>\<or>\<^bsup>s\<^esup>)"
  apply simp
  apply (subgoal_tac "? x. x \<in> set as")
  apply (erule exE)
  apply (drule_tac x = x in bspec)
  apply assumption
  apply (erule conjE)+
  apply assumption
  apply (subgoal_tac "set as \<noteq> {}")
  apply force
  by simp
next show "\<And>(A::'a attree) (A'::'a attree) A''::'a attree.
       A \<sqsubseteq> A' \<Longrightarrow> attack A = attack A' \<Longrightarrow> A' \<sqsubseteq> A'' \<Longrightarrow> attack A' = attack A'' \<Longrightarrow> attack A = attack A''"
    by simp
next show "\<And>A::'a attree. attack A = attack A" by (rule refl)
qed

(* Same goes clearly for \<sqsubseteq>\<^sub>V *)
   
(* Not generally true: a \<and> refinement does not automatically guarantee that 
   the refined AT is valid even if the initial was: the refinement can insert a 
   new subtree that isn't valid. To achieve this, a prerequisite is needed in the 
   below theorem, we need additional assumptions in the intermediate lemmas. 
lemma att_ref_rev [rule_format]: "A \<sqsubseteq> A' \<Longrightarrow> \<turnstile> (A :: ('s :: state) attree) \<longrightarrow>  \<turnstile> A'"

Even the specialisation to just base attacks is not valid for the same reasons as above   
lemma att_ref_rev [rule_format]: " \<turnstile> (A :: ('s :: state) attree) \<Longrightarrow> A \<sqsubseteq> \<N>\<^bsub>attack A\<^esub> \<longrightarrow>  \<turnstile> \<N>\<^bsub>attack A\<^esub>"
*)    

lemma  base_subset: 
    assumes "xa \<subseteq> xc"
    shows  "\<turnstile>\<N>\<^bsub>(x, xa)\<^esub> \<Longrightarrow> \<turnstile>\<N>\<^bsub>(x, xc)\<^esub>" 
proof (simp add: att_base)
  show " \<forall>x::'a\<in>x. \<exists>xa::'a\<in>xa. x \<rightarrow>\<^sub>i xa \<Longrightarrow> \<forall>x::'a\<in>x. \<exists>xa::'a\<in>xc. x \<rightarrow>\<^sub>i xa"
    apply clarify
    apply (drule_tac x = xb in bspec)
    apply assumption
    apply (erule bexE)
    apply (erule_tac x = xaa in bexI)
    apply (rule subsetD)
    apply (rule assms)
    by assumption
qed

(**** Correctness theorem ****)  
theorem AT_EF: assumes " \<turnstile> (A :: ('s :: state) attree)"
               and  "attack A = (I,s)"
               shows "Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s"    
proof (simp add:check_def)
  show "I \<subseteq> {sa::('s :: state). (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF s}" 
   apply (rule subsetI)
   apply (rule CollectI)
   apply (rule conjI)
  proof (simp add: state_transition_refl_def)
    show "\<And>x::'s. x \<in> I \<Longrightarrow> \<exists>i::'s\<in>I. (i, x) \<in> {(x::'s, y::'s). x \<rightarrow>\<^sub>i y}\<^sup>*"
    by (rule_tac x = x in bexI, simp)
next show "\<And>x::'s. x \<in> I \<Longrightarrow> x \<in> EF s" using assms
  proof -
    have a: "\<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y" using assms
    proof -
      have "\<forall>x::'s\<in>fst (attack A). \<exists>y::'s. y \<in> snd (attack A) \<and> x \<rightarrow>\<^sub>i* y"
        apply (rule att_elem_seq0)
        by (rule assms)
      thus " \<forall>x::'s\<in>I. \<exists>y::'s\<in>s. x \<rightarrow>\<^sub>i* y" using assms
      by force  
    qed
    thus "\<And>x::'s. x \<in> I \<Longrightarrow> x \<in> EF s" 
    proof -
      fix x
      assume b: "x \<in> I"
      have "\<exists>y::'s\<in>s::('s :: state) set. x \<rightarrow>\<^sub>i* y" 
        apply (rule_tac x = x and A = I in bspec)
        by (rule a, rule b)
      from this obtain y where "y \<in> s" and "x \<rightarrow>\<^sub>i* y" by (erule bexE)
      thus "x \<in> EF s" 
       apply (erule_tac f = s in EF_step_star)
       by assumption
   qed  
  qed
 qed
qed

theorem ATV_EF: "\<lbrakk> \<turnstile>\<^sub>V (A :: ('s :: state) attree); (I,s) = attack A \<rbrakk> \<Longrightarrow>
 (Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s) } (I :: ('s :: state)set)  \<turnstile> EF s)"   
proof (simp add: ref_validity_def)
  show "\<exists>A'::'s attree. A \<sqsubseteq>\<^sub>V A' \<Longrightarrow> (I, s) = attack A \<Longrightarrow> Kripke {s::'s. \<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* s} I \<turnstile> EF s"
    apply (erule exE)
    apply (simp add: valid_ref_def)
    apply (erule conjE)
    apply (erule AT_EF)
    by (simp add: ref_pres_att)
qed
    
(***** Completeness *****)
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
      apply (rule disjI2) 
      apply (rule_tac x = "[y,z]" in exI)
      by simp
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
            apply (subst nth_app_eq1, simp)
            apply (subst nth_app_eq1, simp)
            apply (insert a5)
            apply (erule conjE)+
            apply (drule_tac x = i in spec)
            apply (erule mp)
            by assumption
          hence a9: "i = length s - (1::nat) \<Longrightarrow> (s @ [z]) ! i \<rightarrow>\<^sub>i (s @ [z]) ! Suc i" using a3 a2
            apply simp
            apply (insert a5)
            apply (erule conjE)
            apply (subst nth_app_eq1, simp)
            by simp
          thus "(s @ [z]) ! i \<rightarrow>\<^sub>i (s @ [z]) ! Suc i" using a7 a8 
            apply (insert a7)
            apply (erule disjE)
            apply (rule a8, assumption)
            by (rule a9, assumption)
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
      apply (rule rtrancl_imp_singleton_seq2)
      by (rule c)
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
      (* *)
      apply (rule_tac x = "[{sa ! j}. j \<leftarrow> [0..<(length sa - 1)]] @ [s]" in exI)
      apply (rule conjI)
      apply simp
    proof -
      fix sa :: "'s list"
      assume e: "sa \<noteq> []" and f: "tl sa \<noteq> []" and g: "sa ! (0::nat) = x" 
         and h: "sa ! (length sa - (1::nat)) = y " and i: "\<forall>i<length sa - (1::nat). sa ! i \<rightarrow>\<^sub>i sa ! Suc i"
      show "tl (map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) \<noteq> [] \<and>
       ((map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) ! (0::nat),
        (map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) !
        (length (map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) - (1::nat))) =
       ({x}, s) \<and>
       (\<forall>i<length (map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) - (1::nat).
           \<turnstile>\<N>\<^bsub>((map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) ! i,
                (map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] @ [s]) ! (i + (1::nat)))\<^esub>)"
       apply (rule conjI)
       apply (subgoal_tac "map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - (1::nat)] \<noteq> []")
       apply simp
       apply (subgoal_tac "length sa - 1 > 0")
       apply simp
       apply (rule tl_nempty_length, rule e, rule f)
       apply (rule conjI)
       apply (subst nth_app_eq1)
       apply simp
       apply (rule tl_nempty_length2, rule e, rule f) 
       apply (subst length_last)
       apply (subst nth_map)
       apply simp
       apply (rule tl_nempty_length2, rule e, rule f) 
       apply (subgoal_tac "[0::nat..<length sa - (1::nat)] ! (0::nat)  = 0")
       apply (simp, rule g)
       apply (subst nth_upt)
       apply simp
       apply (rule tl_nempty_length2, rule e, rule f) 
       apply arith
       apply (rule allI)
       apply (rule impI)
       apply simp
       apply (subst nth_app_eq1)
       apply simp
       apply (case_tac "Suc i < length sa - Suc (0::nat)")
       apply (subst nth_app_eq1)
       apply simp
       apply (subst nth_map)
       apply force
       apply simp
       apply (subst att_base)
       apply (rule ballI)
       apply (simp add: i)
       apply (subgoal_tac "Suc i = length sa - Suc (0::nat)")
       apply simp
       apply (subgoal_tac 
           "((map (\<lambda>j::nat. {sa ! j}) [0::nat..<length sa - Suc (0::nat)] @ [s]) ! (length sa - Suc (0::nat))) = s")
       apply (rotate_tac -1)
       apply (erule ssubst)
       apply (subst att_base)
       apply (rule ballI)
       apply simp
       apply (rule_tac x = "sa ! (Suc i)" in bexI)
       apply (insert i)
       apply (drule_tac x = i in spec)
       apply (erule mp)
       apply simp
       apply (insert b h)
       apply simp
       apply (rule list_app_one_length)
       by simp+
    qed
  qed
qed

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
    hence "\<exists>f::'a \<Rightarrow> 'b. \<forall>x::'a\<in>F. P (f x) x" 
      apply (rule_tac P = "(\<forall>x::'a\<in>F. \<exists>y::'b. P y x)" in mp)
      apply (rule c)
      by assumption
    from this obtain f where f: "\<forall>x::'a\<in>F. P (f x) x" by (erule exE)
    from d obtain y where "P y x" by blast
    thus "(\<exists>f::'a \<Rightarrow> 'b. \<forall>x::'a\<in>insert x F. P (f x) x)" using f 
      apply (rule_tac x = "\<lambda> z. if z = x then y else f z" in exI)
      apply (rule ballI)
      apply (erule insertE)
      by simp+
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
    apply (erule exE)
    apply (erule conjE)
    apply (rule_tac x = "if (a \<in> A) then l else (a # l)" in exI)
    apply (simp add: nodup_all_def)
    by blast
qed

lemma Compl_step3a': "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow>
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
     apply (subgoal_tac "finite {x::'s \<in> I. x \<notin> s}")
     apply (rotate_tac -1)
     apply (erule finite_nodup)
     apply (rule_tac A = "{x::'s \<in> I. x \<notin> s}" and B = I in  finite_subset)
     apply blast
    by (rule f)
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
    proof (clarify)
      fix x
      assume xli: "x \<in> set lI "
      have d: "x \<in> s \<or>
       (\<exists>sl::'s set list.
           sl \<noteq> [] \<and>
           tl sl \<noteq> [] \<and>
           (sl ! (0::nat), sl ! (length sl - (1::nat))) = ({x}, s) \<and>
           (\<forall>i<length sl - (1::nat). \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1::nat)))\<^esub>))"
        apply (insert fa)
        apply (drule_tac x = x in bspec)
        apply (insert xli b)
        apply simp
        apply (erule disjE)
        by simp+
      thus "(\<exists> sl::'s set list.
              sl \<noteq> [] \<and>
              tl sl \<noteq> [] \<and>
              (sl ! (0::nat), sl ! (length sl - (1::nat))) = ({x}, s) \<and>
              (\<forall>i<length sl - (1::nat). \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1::nat)))\<^esub>))"   
        apply (insert d)
        apply (erule disjE)
        apply (insert xli b)
        apply simp
        by assumption
    qed
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

lemma list_one_tl_empty[rule_format]: "length l = Suc (0 :: nat) \<longrightarrow> tl l = []"
proof (rule_tac list = l in list.induct, simp+)
qed

lemma list_two_tl_not_empty[rule_format]: "\<forall> list. length l = Suc (Suc (length list)) \<longrightarrow> tl l \<noteq> []"  
proof (rule_tac list = l in list.induct, simp+, force)
qed

lemma or_empty: "\<turnstile> [] \<oplus>\<^sub>\<or>\<^bsup>({}, s)\<^esup>" 
proof (simp add: att_or)
qed

(* for any l not valid     
    lemma or_empty_list: "\<turnstile> l \<oplus>\<^sub>\<or>\<^bsup>({}, s)\<^esup>" 
*)

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
          (\<forall>i<length x2. \<turnstile>l ! i \<and> attack (l ! i) = ({x2 ! i}, s)) \<longrightarrow> \<turnstile>l \<oplus>\<^sub>\<or>\<^bsup>(set x2, s)\<^esup> \<Longrightarrow>
       x1 # x2 \<noteq> [] \<Longrightarrow>
       length l = length (x1 # x2) \<Longrightarrow>
       nodup_all (x1 # x2) \<Longrightarrow>
       \<forall>i<length (x1 # x2). \<turnstile>l ! i \<and> attack (l ! i) = ({(x1 # x2) ! i}, s) \<Longrightarrow> \<turnstile>l \<oplus>\<^sub>\<or>\<^bsup>(set (x1 # x2), s)\<^esup>"
     apply (case_tac x2)
     apply simp
     apply (subst att_or)
     apply (case_tac l)
     apply simp+
     apply (subst att_or)
     apply (case_tac l)
     apply simp
     apply clarify
     apply simp
     apply (case_tac lista)
     apply simp+
     apply (rule conjI)
     apply (drule_tac x = 0 in spec)
     apply (drule mp)
     apply simp
     apply (erule conjE)+
     apply simp
     apply (rule conjI)
     apply (drule_tac x = 0 in spec)
     apply (drule mp)
     apply simp
     apply (erule conjE)
     apply simp
     apply (rotate_tac -1)
     apply (erule ssubst)
     apply simp
     apply (rule conjI)
     apply (drule_tac x = 0 in spec)
     apply (drule mp)
     apply simp
     apply (erule conjE)
     apply simp
    (* tl instance !*)
     apply (drule_tac x  = "ab # listb" in spec)
     apply (drule mp)
     apply simp
     apply (drule mp)
     apply (erule nodup_all_tl)
     apply (drule mp)
     apply (rule allI)
     apply (rule impI)
     apply (drule_tac x = "Suc i" in spec)
     apply (drule mp)
     apply arith
     apply (rule conjI)
     apply (erule conjE)
     apply (subgoal_tac "(aa # ab # listb) ! Suc i = tl (aa # ab # listb) ! i")
     apply simp+
     apply (frule_tac x = 0 in spec)
     apply (drule mp)
     apply simp
    (* additional assumption nodup (x1 # a # list) to show that
       (insert x1 (insert a (set list)) - fst (attack (l ! (0::nat))) = insert a (set list)
       given that fst(attack (l ! 0)) = {x1} *)
     apply (subgoal_tac "fst (attack aa) = {x1}")
     apply (rotate_tac -1)
     apply (erule ssubst)
     apply (subst nodup_all_lem,assumption,assumption)
     by simp
qed

lemma app_tl_empty_hd[rule_format]: "tl (l @ [a]) = [] \<longrightarrow> hd (l @ [a]) = a"
proof (rule_tac list = l in list.induct, simp+)
qed
       
lemma tl_hd_empty[rule_format]: "tl (l @ [a]) = [] \<longrightarrow> l = []"
proof (rule_tac list = l in list.induct, simp+)
qed

lemma tl_hd_not_empty[rule_format]: "tl (l @ [a]) \<noteq> [] \<longrightarrow> l \<noteq> []"
proof (rule_tac list = l in list.induct, simp+)
qed
  
lemma app_tl_empty_length[rule_format]: "tl (map f [0::nat..<length l] @ [a]) = []  
                                        \<Longrightarrow> l = []"
proof (drule tl_hd_empty, simp)
qed

lemma not_empty_hd_fst[rule_format]: "l \<noteq> [] \<longrightarrow> hd(l @ [a]) = l ! 0"
proof (rule_tac list = l in list.induct, simp+)
qed
  
lemma app_tl_hd_list[rule_format]: "tl (map f [0::nat..<length l] @ [a]) \<noteq> []  
                             \<Longrightarrow> hd(map f [0::nat..<length l] @ [a]) = (map f [0::nat..<length l]) ! 0"
proof (drule tl_hd_not_empty, erule not_empty_hd_fst)
qed

lemma tl_app_in[rule_format]: "l \<noteq> [] \<longrightarrow>
   map f [0::nat..<(length l - (Suc 0:: nat))] @ [f(length l - (Suc 0 :: nat))] = map f [0::nat..<length l]"    
proof (rule_tac list = l in list.induct, simp+)
qed

lemma map_fst[rule_format]: "n > 0 \<longrightarrow> map f [0::nat..<n] = f 0 # (map f [1..<n])"
proof (induct_tac n, simp, case_tac n, simp+)
qed

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
        apply (rule map_fst)
        apply simp
        by (rule l)
      thus "map (\<lambda>i::nat. f ((x1 # a # l) ! i) ((a # l) ! i)) [0::nat..<length l] =
             f x1 a # map (\<lambda>i::nat. f ((a # l) ! i) (l ! i)) [0::nat..<length l - (1::nat)]"
         apply (subst b)
         apply simp
         apply (subgoal_tac "map (\<lambda>i::nat. f ((x1 # a # l) ! i) ((a # l) ! i)) [Suc (0::nat)..<length l] =
                map (\<lambda>i::nat. f ((x1 # a # l) ! Suc i) ((a # l) ! Suc i)) [(0::nat)..<(length l - 1)]")
         apply simp
         apply (subgoal_tac "[Suc (0::nat)..<length l] = map Suc [0..<(length l - 1)]")
         apply (erule ssubst)
         apply simp
     by (simp add: map_Suc_upt l)
    qed
    thus "l \<noteq> [] \<Longrightarrow>
    tl (map (\<lambda>i::nat. f ((x1 # a # l) ! i) ((a # l) ! i)) [0::nat..<length l]) =
    map (\<lambda>i::nat. f ((a # l) ! i) (l ! i)) [0::nat..<length l - Suc (0::nat)]" 
      apply (subst a)
      by simp
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
    apply (rule_tac list = list in step_lem2a)
    apply simp
    by assumption
qed

lemma base_list_and[rule_format]: "Sji \<noteq> [] \<longrightarrow> tl Sji \<noteq> [] \<longrightarrow>
         (\<forall> li.  Sji ! (0::nat) = li \<longrightarrow>
        Sji! (length (Sji) - 1) = s \<longrightarrow>
       (\<forall>i<length (Sji) - 1. \<turnstile>\<N>\<^bsub>(Sji ! i, Sji ! Suc i)\<^esub>) \<longrightarrow>
       \<turnstile>map (\<lambda>i::nat. \<N>\<^bsub>(Sji ! i, Sji ! Suc i)\<^esub>)
          [0::nat..<length (Sji) - Suc (0::nat)] \<oplus>\<^sub>\<and>\<^bsup>(li, s)\<^esup>)"
proof (rule_tac list = Sji in list.induct, simp)
  show "\<And>(x1::'a set) x2::'a set list.
       x2 \<noteq> [] \<longrightarrow>
       tl x2 \<noteq> [] \<longrightarrow>
       (\<forall>li::'a set.
           x2 ! (0::nat) = li \<longrightarrow>
           x2 ! (length x2 - (1::nat)) = s \<longrightarrow>
           (\<forall>i<length x2 - (1::nat). \<turnstile>\<N>\<^bsub>(x2 ! i, x2 ! Suc i)\<^esub>) \<longrightarrow>
           \<turnstile>map (\<lambda>i::nat. \<N>\<^bsub>(x2 ! i, x2 ! Suc i)\<^esub>) [0::nat..<length x2 - Suc (0::nat)] \<oplus>\<^sub>\<and>\<^bsup>(li, s)\<^esup>) \<Longrightarrow>
       x1 # x2 \<noteq> [] \<longrightarrow>
       tl (x1 # x2) \<noteq> [] \<longrightarrow>
       (\<forall>li::'a set.
           (x1 # x2) ! (0::nat) = li \<longrightarrow>
           (x1 # x2) ! (length (x1 # x2) - (1::nat)) = s \<longrightarrow>
           (\<forall>i<length (x1 # x2) - (1::nat). \<turnstile>\<N>\<^bsub>((x1 # x2) ! i, (x1 # x2) ! Suc i)\<^esub>) \<longrightarrow>
           \<turnstile>map (\<lambda>i::nat. \<N>\<^bsub>((x1 # x2) ! i, (x1 # x2) ! Suc i)\<^esub>)
              [0::nat..<length (x1 # x2) - Suc (0::nat)] \<oplus>\<^sub>\<and>\<^bsup>(li, s)\<^esup>)"
         apply (subst att_and)
         apply (case_tac x2)
         apply simp
         apply simp
         apply (rule impI)+
         apply (case_tac "map (\<lambda>i::nat. \<N>\<^bsub>((x1 # a # list) ! i, (a # list) ! i)\<^esub>)
                         [0::nat..<length list] @
                         [\<N>\<^bsub>((x1 # a # list) ! length list, s)\<^esub>]")
         apply simp
         apply clarify
         apply simp
         apply (case_tac lista)
         apply simp
         apply (rule conjI)
         apply force
         apply (erule conjE)
         apply (subgoal_tac "length list = 0")
         apply force
         apply simp+
         apply (rule conjI)
         apply (drule_tac x = 0 in spec) 
         apply (subgoal_tac " (0::nat) < Suc (length list) ")
         prefer 2
         apply simp
         apply simp
         apply (subgoal_tac "\<N>\<^bsub>(x1, a)\<^esub> = aa")
         apply simp 
         apply (rule step_lem2, assumption)
         (* *)
         apply (rule conjI)
         apply (subgoal_tac "\<N>\<^bsub>(x1, a)\<^esub> = aa")
         apply (rotate_tac -1)
         apply (erule subst)
         apply simp
         apply (rule step_lem2, assumption)
         apply (drule mp)
         apply force
         apply (drule mp)
         apply force
         apply (subgoal_tac "\<N>\<^bsub>(x1, a)\<^esub> = aa")
         apply (rotate_tac -1)
         apply (erule subst)
         apply simp
         prefer 2
         apply (rule step_lem2, assumption)
         apply (subgoal_tac "map (\<lambda>i::nat. \<N>\<^bsub>((a # list) ! i, list ! i)\<^esub>)
                             [0::nat..<length list] = ab # listb")
         apply (rotate_tac -1)
         apply (erule subst)
         apply (subgoal_tac "(a # list) ! length list = list ! (length list - Suc (0::nat))")
         apply (rotate_tac -1)
         apply (erule ssubst)
         apply assumption
         apply (subgoal_tac "list \<noteq> []")
         apply simp
         apply force
         (* *)
         apply (subgoal_tac "map (\<lambda>i::nat. \<N>\<^bsub>((a # list) ! i, list ! i)\<^esub>) [0::nat..<length list] =
              tl (map (\<lambda>i::nat. \<N>\<^bsub>((x1 # a # list) ! i, (a # list) ! i)\<^esub>) [0::nat..<length list] @
             [\<N>\<^bsub>((x1 # a # list) ! length list, (a # list) ! length list)\<^esub>] )")
         apply (rotate_tac -1)
         apply (erule ssubst)
         apply (erule ssubst)
         apply simp
         apply (subgoal_tac "list \<noteq> []")
         apply (subgoal_tac "tl (map (\<lambda>i::nat. \<N>\<^bsub>((x1 # a # list) ! i, (a # list) ! i)\<^esub>) [0::nat..<length list])
                     =  (map (\<lambda>i::nat. \<N>\<^bsub>((a # list) ! i, (list) ! i)\<^esub>) [0::nat..<(length list - 1)])")
         apply (thin_tac "map (\<lambda>i::nat. \<N>\<^bsub>((x1 # a # list) ! i, (a # list) ! i)\<^esub>) [0::nat..<length list] @
                          [\<N>\<^bsub>((x1 # a # list) ! length list, (a # list) ! length list)\<^esub>] =
                          aa # ab # listb")
         apply simp 
         apply (rule sym)
         apply (erule tl_app_in)
         apply (erule step_lem)
         by force    
qed

lemma Compl_step3b: "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow> \<not> I \<subseteq> s \<Longrightarrow>
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
    apply (rule conjI)
  proof -
    show  "\<turnstile>[[] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<in> s}, s)\<^esup>,
       map (\<lambda>j::nat.
               map (\<lambda>i::nat. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1::nat)))\<^esub>)
                [0::nat..<length (Sj ! j) - (1::nat)] \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>)
       [0::nat..<length Sj] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<notin> s}, s)\<^esup>] \<oplus>\<^sub>\<or>\<^bsup>(I, s)\<^esup>"
    proof -
      have g: "I - {x::'s \<in> I. x \<in> s} = {x::'s \<in> I. x \<notin> s}" by blast
      thus "\<turnstile>[[] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<in> s}, s)\<^esup>,
       map (\<lambda>j::nat.
               map (\<lambda>i::nat. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1::nat)))\<^esub>)
                [0::nat..<length (Sj ! j) - (1::nat)] \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>)
       [0::nat..<length Sj] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<notin> s}, s)\<^esup>] \<oplus>\<^sub>\<or>\<^bsup>(I, s)\<^esup>"
       apply (subst att_or)
       apply simp
       apply (rule conjI)
       apply (subst att_or)
       apply simp
       apply (rule subsetI)
       apply (drule CollectD)
       apply (erule conjE, assumption)
       apply (rule conjI)
       apply (rule subsetI)
       apply (drule CollectD)
       apply (erule conjE, assumption)
       apply (rotate_tac -1)
       apply (erule ssubst)
       apply (subst att_or)
       apply simp
       apply (rule subst, rule d)
     (* induction over list lI *)
      proof (rule_tac lI = lI in list_or_upt)
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
      next show "length
                 (map (\<lambda>j::nat.
                     map (\<lambda>i::nat. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! Suc i)\<^esub>)
                   [0::nat..<length (Sj ! j) - Suc (0::nat)] \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>)
                 [0::nat..<length Sj]) =  length lI" by (simp add: e)
      next show "nodup_all lI" by (simp add: f)
      next show "\<And>i::nat.
       i < length lI \<Longrightarrow>
       \<turnstile>map (\<lambda>j::nat.
                 map (\<lambda>i::nat. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! Suc i)\<^esub>)
                  [0::nat..<length (Sj ! j) - Suc (0::nat)] \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>)
          [0::nat..<length Sj] !
         i \<and>
       attack
        (map (\<lambda>j::nat.
                 map (\<lambda>i::nat. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! Suc i)\<^esub>)
                  [0::nat..<length (Sj ! j) - Suc (0::nat)] \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>)
          [0::nat..<length Sj] !
         i) =
       ({lI ! i}, s)"
      apply (rule conjI)
      prefer 2
      apply (simp add: a b c d e f)
    proof (simp add: a b c d e f)
      show "\<And>i::nat.
       i < length lI \<Longrightarrow>
       \<turnstile>map (\<lambda>ia::nat. \<N>\<^bsub>(Sj ! i ! ia, Sj ! i ! Suc ia)\<^esub>)
          [0::nat..<length (Sj ! i) - Suc (0::nat)] \<oplus>\<^sub>\<and>\<^bsup>({lI ! i}, s)\<^esup>"
      proof -
        have ff: "(\<forall>j<length Sj. Sj ! j \<noteq> [] \<and>
                             tl (Sj ! j) \<noteq> [] \<and>
           (Sj ! j ! (0::nat), Sj ! j ! (length (Sj ! j) - (1::nat))) = ({lI ! j}, s) \<and>
           (\<forall>i<length (Sj ! j) - (1::nat). \<turnstile>\<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1::nat)))\<^esub>))" 
          apply (rule conjunct2)
          by (rule f)
        thus "\<And>i::nat.
       i < length lI \<Longrightarrow>
       \<turnstile>map (\<lambda>ia::nat. \<N>\<^bsub>(Sj ! i ! ia, Sj ! i ! Suc ia)\<^esub>)
          [0::nat..<length (Sj ! i) - Suc (0::nat)] \<oplus>\<^sub>\<and>\<^bsup>({lI ! i}, s)\<^esup>"          
       apply (drule_tac x = i in spec)
       apply (drule mp)
       apply (simp add: e)
       apply (rule base_list_and)
       apply (erule conjE)+
       apply assumption
       apply (erule conjE)+
       apply assumption
       apply (erule conjE)+
       apply simp
       apply (erule conjE)+
       apply simp
       apply (erule conjE)+
       apply (drule spec)
       apply (drule mp)
       apply simp
       by simp
    qed
  qed
qed
qed
next show "attack
     ([[] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<in> s}, s)\<^esup>,
       map (\<lambda>j::nat.
               map (\<lambda>i::nat. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1::nat)))\<^esub>)
                [0::nat..<length (Sj ! j) - (1::nat)] \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>)
        [0::nat..<length Sj] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<notin> s}, s)\<^esup>] \<oplus>\<^sub>\<or>\<^bsup>(I, s)\<^esup>) =
    (I, s)"
   by simp
qed
qed

theorem Completeness: "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow> 
Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s 
\<Longrightarrow> \<exists> (A :: ('s :: state) attree). \<turnstile> A \<and> attack A = (I,s)"
proof (case_tac "I \<subseteq> s")
  show "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow>
    Kripke {s::'s. \<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* s} I \<turnstile> EF s \<Longrightarrow> I \<subseteq> s \<Longrightarrow> \<exists>A::'s attree. \<turnstile>A \<and> attack A = (I, s)"
  apply (rule_tac x = "((([] :: ((('s :: state) attree) list)) \<oplus>\<^sub>\<and>\<^bsup>(I,s)\<^esup>))" in exI)
  by (subst att_and, simp)
next show "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow>
    Kripke {s::'s. \<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* s} I \<turnstile> EF s \<Longrightarrow> \<not> I \<subseteq> s \<Longrightarrow> \<exists>A::'s attree. \<turnstile>A \<and> attack A = (I, s)"
     apply (rule Compl_step3b, assumption+)
     apply (rule Compl_step3a', assumption+)
     apply (rule Compl_step2)
     by (erule Compl_step1)
 qed

(* Contrapositions of Correctness and Completeness *)    
lemma contrapos_compl: 
  "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow> 
  (\<not> (\<exists> (A :: ('s :: state) attree). \<turnstile> A \<and> attack A = (I, - s))) \<Longrightarrow>
  \<not>(Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF (- s))"
proof (rotate_tac 1, erule contrapos_nn)
  show " finite I \<Longrightarrow>
    I \<noteq> {} \<Longrightarrow> Kripke {s::'s. \<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* s} I \<turnstile> EF (- s) \<Longrightarrow> \<exists>A::'s attree. \<turnstile>A \<and> attack A = (I, - s)"
  by (erule Completeness,assumption+)
qed

lemma contrapos_corr:   
"(\<not>(Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s))
\<Longrightarrow> attack A = (I::'s::state set, s::'s::state set) 
\<Longrightarrow> \<not> (\<turnstile> A::'s::state attree) "
proof (erule contrapos_nn)
  show "attack A = (I, s) \<Longrightarrow> \<turnstile>A \<Longrightarrow> Kripke {s::'s. \<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* s} I \<turnstile> EF s"
by (erule AT_EF, assumption)  
qed

end