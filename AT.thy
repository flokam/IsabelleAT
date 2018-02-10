theory AT
imports MC 
begin

(* Attack vectors with a Kripke semantics;
   version updated from has_hcii17 paper; as in TASE submission (rejected)
   but now with polymorphic type for attack goal instead of just a string.
   Thus, this finally closes the cycle (already pre-meditated in the
   invalidation idea): the goal can be a state; attack is
   a sequence of actions that leads from the initial state to this
   attack state (where the policy is violated) 
   November 2017: Generalize over baseattack to make AT (as already MC)
   independent of Insider theory *)  
(* Omit this concrete datatype here and postpone it to Insider.thy
datatype baseattack = Goto "location" | Perform "action" | Credential "location"
*)

(* Generalised attacktree structure with only one generic base_attack type 'a
  that encompasses all of abstract attack annotation 'a (could be string but also
  the type of predicates for representing the actual attack predicate
  inside the attack tree explicitly rather than just its name) as
  well as the type of base attacks.
   For the example Insider framework 'a would contain the actor and the action
     *)
datatype ('s :: state) attree = BaseAttack "('s set) * ('s set)" ("\<N>\<^bsub>(_)\<^esub>") |
                  AndAttack "('s attree) list" "('s set) * ('s set)" ("_ \<oplus>\<^sub>\<and>\<^bsup>(_)\<^esup>" 50) | 
                  OrAttack  "('s attree) list" "('s set) * ('s set)" ("_ \<oplus>\<^sub>\<or>\<^bsup>(_)\<^esup>" 51)

             
primrec attack :: "('s :: state) attree \<Rightarrow> ('s set) * ('s set)"
  where 
"attack (BaseAttack b) = b"|
"attack (AndAttack as s) = s"  | 
"attack (OrAttack as s) = s"


(* sublist_replacement: sublist_rep l a l':
    in list l' replace first occurrence of element a  with list l 
   (the result flattens l into l') *)
(*
primrec sublist_rep :: "['a list, 'a, 'a list] \<Rightarrow> 'a list"
where 
sl_nil : "sublist_rep l a [] = []" |
sl_step: "sublist_rep l a (b # l') = (if a = b then l @ l' else (b # (sublist_rep l a l')))"
*)

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
(* ref_base: "\<lbrakk> \<N>\<^bsub>attack A\<^esub> \<sqsubseteq> A \<rbrakk> \<Longrightarrow> A \<sqsubseteq> \<N>\<^bsub>attack A\<^esub>" | *)
ref_trans: "\<lbrakk> A \<sqsubseteq> A'; A' \<sqsubseteq> A'' \<rbrakk> \<Longrightarrow> A \<sqsubseteq> A''"|
ref_refl : "A \<sqsubseteq> A"

(* The following inductive definition defines the proof rule for and attack trees, 
  i.e., it introduces refinement as a way to prove that an attack is possible and 
  also provides the leaves in an attack tree that correspond to verifying the 
  base cases in the model (with the enables relation) and mapping the proof 
  relation to lists of attacks in a sequence. --
It turns out that if the refinement is integrated into the following predicate
is_attack_tree by rule att_ref: "\<lbrakk> A \<sqsubseteq> A'; \<turnstile> A'; attack A = attack A' \<rbrakk> \<Longrightarrow> \<turnstile> A" 
then it is not possible to prove
"\<turnstile>\<N>\<^bsub>(s,s')\<^esub>  \<Longrightarrow> (\<forall> y \<in> s'. \<exists> x \<in> s. x  \<rightarrow>\<^sub>i y \<and> (\<forall> x \<in> s. \<exists> y \<in> s'. x  \<rightarrow>\<^sub>i y))
because precisely the att_ref case in proving this via case analysis strikes back
\<N>\<^bsub>(s, s')\<^esub> = A \<Longrightarrow>
       A \<sqsubseteq> A' \<Longrightarrow>
       \<turnstile>A' \<Longrightarrow> attack A = attack A' \<Longrightarrow> \<forall>y::'a\<in>s'. (\<exists>x::'a\<in>s. x \<rightarrow>\<^sub>i y) \<and> (\<forall>x::'a\<in>s. \<exists>xa::'a\<in>s'. x \<rightarrow>\<^sub>i xa)
We need to be able to judge the validity first independent of refinement.
I.e., delete the att_ref rule. Then facts about validity can be proved for fully
elaborated ATs. We can define the above rule after the definition of 
refinement and is_attack_tree by a definition valid_refinement using a new operator
We also don't need the Abstract_tree field any more and can use the 
base_attack as a placeholder for "longer" attacksteps within and-ATs
is_attack_tree as inductive definition does not allow to prove
\<not> ( \<turnstile> [] \<oplus>\<^sub>\<and>\<^bsup>s)
needed for the list inductions to take off the ground.
Now, the definition of \<turnstile> should be doable by a primrec. Try
that next:
*)
primrec fold_but_one :: "[bool list] \<Rightarrow> bool"
where
  fbo_empty: "fold_but_one [] = False" |
  fbo_nempty: "fold_but_one (a#l) = (a \<and> (if l = [] then True 
                                     else fold_but_one l))" 

lemma "fold_but_one [True, True] = True"
  by simp

lemma "fold_but_one [] = False"
  by (rule fbo_empty)
  thm map_def

(* fbo bringt auch nichts, weil man das \<turnstile> hineinmappen muss *)    
    (* Das geht nicht, weil man da schon \<turnstile> voraussetzt:
primrec prep_als :: "('s :: state) attree \<Rightarrow> bool list"
  where
    prep_als_base : "prep_als [] = []" |
    prep_als_step : "prep_als (a # l) = 
           (if (l = []) then [( \<turnstile> a)] 
            else ((snd (attack a) = (fst(attack(hd l)))) \<and> ( \<turnstile> a)) # (prep_als l))"
*)
  thm attree.induct

(*    
lemma attree_induct2 [rule_format]: 
"(\<And>x::'s::state set \<times> 's::state set. (P::'s::state attree \<Rightarrow> bool) \<N>\<^bsub>x\<^esub>) \<Longrightarrow>
(\<And>(x1a::'s::state attree list) x2::'s::state set \<times> 's::state set.
    (\<And>x1aa::'s::state attree. x1aa \<in> set x1a \<Longrightarrow> P x1aa) \<Longrightarrow> P (x1a \<oplus>\<^sub>\<and>\<^bsup>x2\<^esup>)) \<Longrightarrow>
(\<And>(x1a::'s::state attree list) x2::'s::state set \<times> 's::state set.
    (\<And>x1aa::'s::state attree. x1aa \<in> set x1a \<Longrightarrow> P x1aa) \<Longrightarrow> P (x1a \<oplus>\<^sub>\<or>\<^bsup>x2\<^esup>)) \<Longrightarrow>
P (attree::'s::state attree)"   
oops
*)
  thm list.induct
    
lemma non_empty_list_induction[rule_format] : "(\<forall> a . (P::'a::type list \<Rightarrow> bool) [a]) \<longrightarrow>
(\<forall> (x1::'a::type) x2::'a::type list. P x2 \<longrightarrow> P (x1 # x2)) \<longrightarrow>
(list \<noteq> [] \<longrightarrow> P (list::'a::type list))"    
  apply (rule list.induct) 
    apply simp
    apply clarify
  apply (case_tac x2)
by simp+
  
lemma non_empty_list_induction2: "(\<And> a . (P::'a::type list \<Rightarrow> bool) [a]) \<Longrightarrow>
(\<And> (x1::'a::type) x2::'a::type list. P x2 \<Longrightarrow> P (x1 # x2)) \<Longrightarrow>
(list \<noteq> [] \<longrightarrow> P (list::'a::type list))"    
  apply (rule impI)
    apply (rule non_empty_list_induction)
  by simp+
    
function (domintros) is_attack_tree :: "[('s :: state) attree] \<Rightarrow> bool"  ("\<turnstile>_" 50) 
where 
att_base:  "(\<turnstile> \<N>\<^bsub>s\<^esub>) = ( (\<forall> x \<in> (fst s). (\<exists> y \<in> (snd s). x  \<rightarrow>\<^sub>i y )))" |
att_and: " (\<turnstile> (As :: ('s :: state attree list)) \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>) = 
               (if As = [] then (fst s = snd s)
               else (if (tl As = []) then ( \<turnstile> (hd As) \<and> attack (hd As) = s) 
                     else ((( \<turnstile> (hd As)) \<and>  (fst(attack(hd As)) = fst s) \<and> ( \<turnstile> (tl As) \<oplus>\<^sub>\<and>\<^bsup>(snd(attack (hd As)),snd(s))\<^esup>)))))" |
att_or: " (\<turnstile> (As :: ('s :: state attree list)) \<oplus>\<^sub>\<or>\<^bsup>s\<^esup>) = 
               (if As = [] then (fst s = snd s) 
               else (if (tl As = []) then ( \<turnstile> (hd As) \<and> attack (hd As) = s) 
                     else ((( \<turnstile> (hd As)) \<and> attack (hd As) = s \<and> ( \<turnstile> (tl As) \<oplus>\<^sub>\<or>\<^bsup>s\<^esup>)))))" 

        apply auto
  apply (insert AT.attree.nchotomy)
  apply (drule_tac x = x in spec)
  apply (erule disjE)
   apply (erule exE)
   apply (drule_tac x = "fst x1" in meta_spec)
   apply (rotate_tac -1)
  apply (drule_tac x = "snd x1" in meta_spec)
   apply (drule meta_mp)
    apply simp
   apply assumption
   apply (erule disjE) 
   apply (erule exE)+
    apply (rotate_tac 1)
   apply (drule_tac x = "x21" in meta_spec)
   apply (rotate_tac -1)
   apply (drule_tac x = "fst x22" in meta_spec)
   apply (rotate_tac -1)
   apply (drule_tac x = "snd x22" in meta_spec)
   apply (drule meta_mp)
    apply simp
  apply assumption
    apply (erule exE)+
    apply (rotate_tac 2)
   apply (drule_tac x = "x31" in meta_spec)
   apply (rotate_tac -1)
   apply (drule_tac x = "fst x32" in meta_spec)
   apply (rotate_tac -1)
   apply (drule_tac x = "snd x32" in meta_spec)
   apply (drule meta_mp)
    apply simp
  by assumption    
termination
  apply clarify
  thm is_attack_tree.domintros
    apply (rule attree.induct)
    apply (simp add: is_attack_tree.domintros)
   prefer 2   
    apply (rule is_attack_tree.domintros(3))
     apply (simp add: is_attack_tree.domintros)+
        apply (subgoal_tac "(\<forall> x1aa::'a attree. x1aa \<in> set (tl x1a) \<longrightarrow> is_attack_tree_dom x1aa)")
  apply (rule mp)
    prefer 2
     apply (rotate_tac 4)
     apply assumption    
    apply (rule mp)
     prefer 2
     apply (rotate_tac 2)
     apply assumption
  apply (subgoal_tac "
       \<forall> x11. x11 \<noteq> [] \<longrightarrow>
       (\<forall>x1aa::'a attree. x1aa \<in> set (x11) \<longrightarrow> is_attack_tree_dom x1aa) \<longrightarrow>
       is_attack_tree_dom (x11 \<oplus>\<^sub>\<or>\<^bsup>(a, b)\<^esup>)")
      apply (erule_tac x = "tl x1a" in spec)
    apply (rule allI)
    thm non_empty_list_induction2
      apply (rule non_empty_list_induction2)
       apply (rule impI)+
     apply (rule is_attack_tree.domintros(3))   
   apply (simp add: is_attack_tree.domintros)+
apply (rule impI)    
     apply (rule is_attack_tree.domintros(3))
        apply (simp add: is_attack_tree.domintros)+
     apply clarify
     apply (drule_tac x = x1aa in meta_spec)
     apply (erule meta_mp)
      apply (subgoal_tac "\<forall> x1a. tl x1a \<noteq> [] \<longrightarrow> x1aa \<in> set (tl x1a) \<longrightarrow> x1aa \<in> set x1a")
      apply simp
     apply (rule allI)
     apply (rule list.induct)
      apply simp+
      (* Huh *)
    apply (rule is_attack_tree.domintros(2))
     apply (simp add: is_attack_tree.domintros)+
        apply (subgoal_tac "(\<forall> x1aa::'a attree. x1aa \<in> set (tl x1a) \<longrightarrow> is_attack_tree_dom x1aa)")
        apply (rule mp)
    prefer 2
     apply (rotate_tac 4)
     apply assumption    
    apply (rule mp)
     prefer 2
     apply (rotate_tac 2)
     apply assumption
  apply (subgoal_tac "
       \<forall> x11. \<forall> a. x11 \<noteq> [] \<longrightarrow>
       (\<forall>x1aa::'a attree. x1aa \<in> set (x11) \<longrightarrow> is_attack_tree_dom x1aa) \<longrightarrow>
       is_attack_tree_dom (x11 \<oplus>\<^sub>\<and>\<^bsup>(a, b)\<^esup>)")
        apply (rotate_tac -1)
      apply (drule_tac x = "tl x1a" in spec)
      apply (erule_tac x = "snd (attack (hd x1a))" in spec)
     apply (rule allI)+
     apply (rule impI)
     apply (rule_tac x = aa in spec)
     apply (rule_tac mp)
      prefer 2
      apply (rotate_tac -1)
      apply assumption
     apply (rule non_empty_list_induction2)
      apply (rule allI)
       apply (rule impI)+
     apply (rule is_attack_tree.domintros(2))   
   apply (simp add: is_attack_tree.domintros)+
     apply (rule impI)    
      apply (rule allI)
     apply (rule is_attack_tree.domintros(2))
        apply (simp add: is_attack_tree.domintros)+
     apply clarify
     apply (drule_tac x = x1aa in meta_spec)
     apply (erule meta_mp)
      apply (subgoal_tac "\<forall> x1a. tl x1a \<noteq> [] \<longrightarrow> x1aa \<in> set (tl x1a) \<longrightarrow> x1aa \<in> set x1a")
     apply simp
      apply (rule allI)
    apply (rule list.induct)
by simp+
(* Wow *)

    
lemma att_and_one: "\<lbrakk> \<turnstile> a; attack a = s \<rbrakk>  \<Longrightarrow> \<turnstile>[a] \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> "
  apply (subst att_and)
by simp

  
declare is_attack_tree.simps[simp del]

lemma att_and_empty[rule_format] : " \<turnstile>[] \<oplus>\<^sub>\<and>\<^bsup>(s', s'')\<^esup> \<longrightarrow> s' = s''"
apply (subst att_and)  
  by simp
    
lemma att_and_empty2: " \<turnstile>[] \<oplus>\<^sub>\<and>\<^bsup>(s, s)\<^esup>"
  apply (subst att_and)  
by simp

lemma att_or_empty[rule_format] : " \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>(s', s'')\<^esup> \<longrightarrow> s' = s''"
apply (subst att_or)  
  by simp

lemma att_or_empty_rev: "\<lbrakk> \<turnstile> l \<oplus>\<^sub>\<or>\<^bsup>(s, s')\<^esup> ; s \<noteq> s' \<rbrakk> \<Longrightarrow> l \<noteq> []"    
    apply (erule contrapos_nn)
  apply (rule att_or_empty)
  by simp
    
lemma att_or_empty2: " \<turnstile>[] \<oplus>\<^sub>\<or>\<^bsup>(s, s)\<^esup>"
  apply (subst att_or)  
by simp
  
  lemma att_comp_and_cons[rule_format]:  "\<forall> a s s'. \<turnstile>  a \<longrightarrow> attack  a = (s,s') \<longrightarrow>  \<turnstile> As \<oplus>\<^sub>\<and>\<^bsup>(s',s'')\<^esup>
                            \<longrightarrow>  \<turnstile> (a # As) \<oplus>\<^sub>\<and>\<^bsup>(s,s'')\<^esup>" 
    apply (rule_tac list = As in list.induct)
      apply clarify
    apply (subst att_and)
     apply simp
     apply (erule att_and_empty)
    apply clarify
      apply (subst att_and)
by simp

lemma att_andD1: " \<turnstile>x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> \<Longrightarrow> \<turnstile> x1"
  apply (case_tac x2)
   by (simp add: att_and)+

     
lemma att_and_nonemptyD2[rule_format] : "(x2 \<noteq> [] \<longrightarrow> \<turnstile>x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> 
                            \<longrightarrow> \<turnstile> x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>)" 
apply (rule non_empty_list_induction2)  
          apply (subst att_and)
        apply simp
         apply (subst att_and)
by simp
 
lemma att_and_emptyD2[rule_format] : "(x2 = [] \<longrightarrow> \<turnstile>x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> 
                            \<longrightarrow> \<turnstile> x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>)" 
  apply clarify
    apply (subgoal_tac "snd(attack x1) = snd s")
   apply simp
   apply (subst att_and)
   apply simp
by (simp add: att_and)
  
  lemma att_andD2 : " \<turnstile>x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> \<Longrightarrow> \<turnstile> x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>" 
apply (case_tac x2)
    apply (erule att_and_emptyD2, assumption)
    apply (rule att_and_nonemptyD2)
      apply simp
by assumption

(* weaker   
lemma att_andD2[rule_format]: "( \<turnstile>x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> \<longrightarrow> (\<exists> s'. \<turnstile> x2 \<oplus>\<^sub>\<and>\<^bsup>(s',snd s)\<^esup>))"
  apply (case_tac x2)
   apply (subst att_and)
   apply simp
    apply (rule impI)
    apply (rule_tac x = "snd s" in exI)
   apply (subst att_and)
   apply simp
  apply (rule impI)
    apply (rule_tac x = "snd(attack x1)" in exI)
  apply (rule att_and_nonemptyD2)
   apply simp
    by assumption
*)

  
(* not needed here   
lemma att_comp_and: "\<forall> As' s s' s''. \<turnstile>  As \<oplus>\<^sub>\<and>\<^bsup>s\<^esup> \<longrightarrow> \<turnstile> As' \<oplus>\<^sub>\<and>\<^bsup>s'\<^esup>  
                     \<longrightarrow> snd s = fst s' \<longrightarrow> s'' = (fst s,snd s')  \<longrightarrow>
                      \<turnstile> (As @  As') \<oplus>\<^sub>\<and>\<^bsup>s''\<^esup>" 
  apply (rule_tac list = As in list.induct)
   apply (rule allI)
   apply (rule_tac list = As' in list.induct)
    apply (subst att_and)
    apply simp+
   apply clarify
   apply (subgoal_tac "a = b")
    apply simp
   apply (erule att_and_empty)
  apply (rule allI)
  apply (rule_tac list = As' in list.induct)
   apply clarify
   apply (subgoal_tac "aa = ba")
    apply simp
    apply (erule att_and_empty)
  apply clarify
  apply simp
  apply (subst att_and)
  apply simp
apply (rule conjI)    
apply (erule att_andD1)
 *)
    
(* other lemmas not needed here but potentially useful in future applications
att_and_distr_left: "\<lbrakk> \<turnstile> ( [a,(as \<oplus>\<^sub>\<or>\<^bsup>(s',s'')\<^esup>)] \<oplus>\<^sub>\<and>\<^bsup>(s,s'')\<^esup>)  ;
                        attack a = (s,s') \<rbrakk>
              \<Longrightarrow>  \<turnstile> ((map (\<lambda> x. [a, x]\<oplus>\<^sub>\<and>\<^bsup>(s,s'')\<^esup>) as) \<oplus>\<^sub>\<or>\<^bsup>(s,s'')\<^esup>)" |
att_and_distr_right: "\<lbrakk> \<turnstile> ( [(as \<oplus>\<^sub>\<or>\<^bsup>(s,s')\<^esup>),a] \<oplus>\<^sub>\<and>\<^bsup>(s,s'')\<^esup>)  ;
                       attack a = (s',s'') \<rbrakk>
              \<Longrightarrow>   \<turnstile> ((map (\<lambda> x. [x, a]\<oplus>\<^sub>\<and>\<^bsup>(s,s'')\<^esup>) as) \<oplus>\<^sub>\<or>\<^bsup>(s,s'')\<^esup>)" |
att_or_distr_left: "\<lbrakk> \<turnstile> ((map (\<lambda> x. [a, x]\<oplus>\<^sub>\<and>\<^bsup>(s,s'')\<^esup>) as) \<oplus>\<^sub>\<or>\<^bsup>(s,s'')\<^esup>);
                      attack a = (s,s') \<rbrakk>
              \<Longrightarrow>  \<turnstile> ( [a,(as \<oplus>\<^sub>\<or>\<^bsup>(s',s'')\<^esup>)] \<oplus>\<^sub>\<and>\<^bsup>(s,s')\<^esup>)" |
att_or_assoc_right: "\<lbrakk> \<turnstile> ((map (\<lambda> x. [x, a]\<oplus>\<^sub>\<and>\<^bsup>(s,s'')\<^esup>) as) \<oplus>\<^sub>\<or>\<^bsup>(s,s'')\<^esup>);
                      attack a = (s',s'') \<rbrakk>
              \<Longrightarrow>  \<turnstile> ( [(as \<oplus>\<^sub>\<or>\<^bsup>(s,s')\<^esup>),a] \<oplus>\<^sub>\<and>\<^bsup>(s',s'')\<^esup>)"
*)
 
definition valid_ref :: "[('s :: state) attree, 's attree] \<Rightarrow> bool" ("_ \<sqsubseteq>\<^sub>V _" 50)
  where
"A \<sqsubseteq>\<^sub>V A' \<equiv>  ( A \<sqsubseteq> A' \<and>  \<turnstile> A')"

(* This is not true, since the abstract AT is not valid now any more 
theorem att_ref: "\<lbrakk> A \<sqsubseteq>\<^sub>V A'; \<turnstile> A'; attack A = attack A' \<rbrakk> \<Longrightarrow> \<turnstile> A" 
but we can introduce a refinement validity based on the valid refinement
*)
definition ref_validity :: "[('s :: state) attree] \<Rightarrow> bool" ("\<turnstile>\<^sub>V _" 50)
  where
"\<turnstile>\<^sub>V A  \<equiv>  (\<exists> A'. A \<sqsubseteq>\<^sub>V A')"

     
(* Further general theorems -- resulting algebraic properties of AT
   but also relationship AT and Kripke, e.g.  \<turnstile> (init K, p) \<Longrightarrow>  K \<turnstile> EF p *) 
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
(* More precisely: at the outermost level we need to assume an OrAttack.
   Inside the OrAttack there are pure AndAttack sequences. To prove this
   will involve a lot of AC-reasoning but the above rules for |- for
   distributivity can be used to prove first AC equalities (from the 
   |- in two directions) *)
    

lemma or_attD[rule_format]: " \<turnstile> ((x1 :: (('s :: state) attree)list)  \<oplus>\<^sub>\<or>\<^bsup>a\<^esup>) \<longrightarrow> (\<forall> x \<in> (set x1). \<turnstile> x) "
   apply (rule list.induct)
   apply simp
  apply (rule impI)
    apply (rule ballI)    
  apply (erule disjE)
    apply (rule att_or_hdE)
   apply simp
  apply (drule att_or_tlE)
    apply (drule mp)
   apply assumption
  apply (erule bspec)
  by assumption


lemma and_attD[rule_format] : "\<forall> a. \<turnstile> ((x1 :: (('s :: state) attree)list)  \<oplus>\<^sub>\<and>\<^bsup>a\<^esup>) \<longrightarrow> (\<forall> x \<in> (set x1). \<turnstile> x) "
   apply (rule list.induct)
   apply simp
  apply simp
  apply (rule impI)
  apply (rule conjI)
    apply (erule exE)+
   apply (erule att_and_hdE)
    apply (erule exE)+
  apply (drule att_and_tlE)
  apply (drule mp)
   apply (rule_tac x = "snd (attack x1)" in exI)
   apply (rule_tac x = "snd(a,b)" in exI)
  by assumption+


lemma att_eq1 [rule_format]:  "\<turnstile>x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup> \<longrightarrow> fst x = fst (attack x1)"
  apply (subst att_and)
by simp

lemma zeroth_app_eq[rule_format]: "\<forall> l' a. l \<noteq> [] \<longrightarrow> l ! 0 = a \<longrightarrow> (l @ l') ! 0 = a"
  apply (rule_tac list = l in list.induct)
  by simp+

lemma zeroth_app_eq_rev[rule_format]: "\<forall> l' a. l \<noteq> [] \<longrightarrow> (l @ l') ! 0 = a \<longrightarrow> l ! 0 = a "
  apply (rule_tac list = l in list.induct)
  by simp+
    
    
lemma list_nth_suc[rule_format] : "l \<noteq> [] \<longrightarrow> (x1 # l) ! (length l) = l ! (length l - 1)"
  apply (induct_tac l)
by simp+
    
lemma nth_app_eq[rule_format]: "\<forall> sl x. sl \<noteq> [] \<longrightarrow> sl ! (length sl - Suc (0::nat)) = x \<longrightarrow> 
                    (l @ sl) ! (length l + length sl - Suc (0::nat)) = x"    
  apply (rule_tac list = l in list.induct)
   apply simp
by simp
(*  
lemma nth_app_eq_rev[rule_format]:"\<forall> xa. xs \<noteq> [] \<longrightarrow> 
               (xs @ [xa]) ! (length (xs @ [xa]) - Suc (0::nat)) = s \<longrightarrow>
               (xs) ! (length xs - Suc (0::nat)) = s"  
    apply (rule_tac list = xs in list.induct)
   apply simp
  apply clarify
  apply (case_tac "x2 = []")
    apply simp
  by simp
*)
  
    
lemma nth_app_eq1[rule_format]: "\<forall> sl i.  i < length sla 
                                 \<longrightarrow> (sla @ sl) ! i = sla ! i"
    apply (induct_tac sla)
   apply simp
  apply clarify
    apply (drule_tac x = "sl" in spec)
  apply (drule_tac x = "i - 1" in spec)
  apply (case_tac i)
by simp+

lemma nth_app_eq1_rev:   "i < length sla \<Longrightarrow>  sla ! i = (sla @ sl) ! i"
  apply (subst nth_app_eq1)
   apply assumption
    by (rule refl)
  
lemma nth_app_eq2[rule_format]: "\<forall> sl i. length sla \<le> i \<and> i < length (sla @ sl) 
                     \<longrightarrow> (sla @ sl) ! i = sl ! (i - (length sla))"
    apply (induct_tac sla)
   apply simp
  apply clarify
    apply simp
    apply (drule_tac x = "sl" in spec)
  apply (drule_tac x = "i - 1" in spec)
  apply (case_tac i)
by simp+

lemma tl_lem1[rule_format]: "l \<noteq> [] \<longrightarrow> tl l = [] \<longrightarrow> length l = 1"
  apply (induct_tac l)
by simp+
  
lemma nth_tl_length[rule_format]: "tl sl \<noteq> [] \<longrightarrow>
      tl sl ! (length (tl sl) - Suc (0::nat)) = sl ! (length sl - Suc (0::nat))" 
  apply (rule_tac list = sl in list.induct)
by simp+

  lemma nth_tl_length1[rule_format]: "tl sl \<noteq> [] \<longrightarrow>
      tl sl ! n = sl ! (n + 1)" 
  apply (rule_tac list = sl in list.induct)
by simp+
 
  
lemma ineq1: "i < length sla - n  \<Longrightarrow>
       (0::nat) \<le> n \<Longrightarrow> i < length sla"  
by simp  
  

lemma ineq2[rule_format]: "length sla \<le> i \<longrightarrow> i + (1::nat) - length sla = i - length sla + 1"
  by arith
    
lemma ineq3: "tl sl \<noteq> []  \<Longrightarrow> length sla \<le> i \<Longrightarrow> i < length (sla @ tl sl) - (1::nat)
              \<Longrightarrow> i - length sla + (1::nat) < length sl - (1::nat)"    
by simp

  
lemma tl_eq1[rule_format]: "sl \<noteq> [] \<longrightarrow> tl sl ! (0::nat) = sl ! Suc (0::nat)"  
  apply (rule_tac list = sl in list.induct)
by simp+
  
lemma not_empty_ex: "A \<noteq> {} \<Longrightarrow> ? x. x \<in> A"
by force

lemma first_step[rule_format]:" \<turnstile> (A :: ('s :: state) attree) \<longrightarrow> 
       ((A = \<N>\<^bsub>attack A\<^esub>) \<or>
       (\<exists> al. (A  = (al \<oplus>\<^sub>\<and>\<^bsup>(attack A)\<^esup>)) \<and> 
              (\<exists> (sl :: ((('s :: state) set)list)). (sl \<noteq> []) \<and>
                 (sl ! 0, sl ! (length sl - 1)) = attack A \<and>
                 (\<forall> i < (length sl - 1).  \<turnstile> \<N>\<^bsub>(sl ! i,sl ! (i+1) )\<^esub>
                         ))) \<or>
        (\<exists> oal. (A = (oal \<oplus>\<^sub>\<or>\<^bsup>(attack A)\<^esup>) ) \<and> 
          (\<forall> a \<in> (set oal). (\<exists> al. (a = (al \<oplus>\<^sub>\<and>\<^bsup>(attack A)\<^esup>)) \<and>
              (\<exists> (sl :: ((('s :: state) set)list)). (sl \<noteq> []) \<and>
                 (sl ! 0, sl ! (length sl - 1)) = attack A \<and>
                 (\<forall> i < (length sl - 1).  \<turnstile> \<N>\<^bsub>(sl ! i,sl ! (i+1) )\<^esub>
                         ))))))"
  apply (induct_tac A)
(* first case *)
    apply (rule impI)
    apply (rule disjI1)
    apply (simp add:ref_refl)
(* snd case \<and> *)
    apply (rule impI)
   apply (rule disjI2)
    apply (rule disjI1)
   apply (rule exI)
   apply (rule conjI)
    apply simp
   apply (rule mp)
    prefer 2
    apply (rotate_tac -1)
    apply assumption
   apply (rule_tac x = x2 in spec)
apply (subgoal_tac  "(\<forall> x1aa::'s attree.
           x1aa \<in> set x1a \<longrightarrow>
           \<turnstile>x1aa \<longrightarrow>
           x1aa = \<N>\<^bsub>attack x1aa\<^esub> \<or>
           (\<exists>al::'s attree list.
               x1aa = (al \<oplus>\<^sub>\<and>\<^bsup>attack x1aa\<^esup>) \<and>
               (\<exists>sl::'s set list. (sl \<noteq> []) \<and>
                   (sl ! (0::nat), sl ! (length sl - (1::nat))) = attack x1aa \<and>
                   (\<forall>i<length sl - (1::nat). \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1::nat)))\<^esub>))) \<or>
           (\<exists>oal::'s attree list.
               x1aa = oal \<oplus>\<^sub>\<or>\<^bsup>attack x1aa\<^esup> \<and>
               (\<forall>a::'s attree\<in>set oal.
                   \<exists>al::'s attree list.
                      a = (al \<oplus>\<^sub>\<and>\<^bsup>attack x1aa\<^esup>) \<and>
                      (\<exists>sl::'s set list. (sl \<noteq> []) \<and>
                          (sl ! (0::nat), sl ! (length sl - (1::nat))) = attack x1aa \<and>
                          (\<forall>i<length sl - (1::nat).
                              \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1::nat)))\<^esub>)))))")   
    apply (rule mp)
    prefer 2
     apply (rotate_tac -1)
    apply assumption
    thm list.induct
     apply (rule_tac list = "x1a" in list.induct)
      (* \<and> induction empty case *)
      apply clarify
      apply (rule_tac x = "[aa]" in exI)
      apply (rule_tac conjI)
        apply simp
       apply (rule conjI)
      apply simp
       apply (erule att_and_empty)
      apply simp
(* \<and> induction case nonempty  *)
      apply (rule impI, rule allI, rule impI)
      (* free IH *)
      apply (subgoal_tac "(\<forall>x::'s set \<times> 's set.
           \<turnstile>x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup> \<longrightarrow>
           (\<exists>sl::'s set list. (sl \<noteq> []) \<and>
               (sl ! (0::nat), sl ! (length sl - (1::nat))) = attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<and>
               (\<forall>i<length sl - (1::nat). \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1::nat)))\<^esub>))) ")
       prefer 2
      apply simp
      apply (drule_tac x = "(snd(attack x1), snd x)" in spec)
      apply (rotate_tac -1)
      apply (erule impE)
       apply (erule att_andD2)
      apply (erule exE)
      (* unleash the 3 cases for x1 *)
      apply (frule att_andD1)
      apply (rotate_tac -4)
      apply (drule_tac x = x1 in spec)
      apply (rotate_tac -1)
      apply (erule impE)
       apply simp
    apply (rotate_tac -1)
      apply (erule impE)
       apply assumption
      (* first case of x1 as base *)
      apply (erule disjE)
      apply (rotate_tac 2)
      apply (rule_tac x = "(fst x) # sl" in exI)
      apply (rule conjI)
       apply (erule conjE)
       apply simp
      apply (erule conjE)
      apply (rule conjI)
       apply simp
(* from freeing the IH *)      
      prefer 3
      apply simp
(* the actual sl property *)
     apply simp
apply (rule allI, rule impI)      
      apply (case_tac i)
      apply (subgoal_tac "fst x = fst(attack x1)")
        apply simp
       apply (erule att_eq1)
      apply simp
      (* second case of x1 as \<and> attack *)
      apply (erule disjE)
      apply (erule exE)
      apply (erule conjE)+
      apply (erule exE)
      apply (erule conjE)+
      apply (rule_tac x = "sla @ (tl sl)" in exI)
      apply (rule conjI)
       apply simp
      apply (rule conjI)
       apply simp
       apply (subgoal_tac "x = (fst(attack x1), snd x)")
        apply (rotate_tac -1)
      apply (erule ssubst)
        apply simp
        apply (rule conjI)
         apply (subgoal_tac "sla ! 0 = fst(attack x1)")
          apply (erule zeroth_app_eq)
          apply assumption
         apply (subgoal_tac "\<forall> (a:: 's set) b (c :: 's set) d. (a, c) = (b, d) \<longrightarrow> a = b")
          apply (rotate_tac -1)
          apply (drule_tac x = "sla ! 0" in spec)
    apply (rotate_tac -1)
          apply (drule_tac x = "fst(attack x1)" in spec)
    apply (rotate_tac -1)
          apply (drule_tac x = "sla ! (length sla - 1)" in spec)
    apply (rotate_tac -1)
          apply (drule_tac x = "snd(attack x1)" in spec)
          apply (erule mp)
          apply simp
         apply simp
      (* so far same *)
        apply (erule conjE)
        apply (subgoal_tac "length (tl sl) = (length sl - Suc (0::nat))")
    apply (rotate_tac -1)
         apply (erule subst)
         apply (subgoal_tac "sla ! (length sla - 1) = sl ! 0")
         prefer 2
          apply (rotate_tac -2)
          apply (erule ssubst)      
      apply (subgoal_tac "\<forall> (a:: 's set) b (c :: 's set) d. (a, c) = (b, d) \<longrightarrow> c = d")
          apply (rotate_tac -1)
          apply (drule_tac x = "sla ! 0" in spec)
    apply (rotate_tac -1)
          apply (drule_tac x = "fst(attack x1)" in spec)
    apply (rotate_tac -1)
          apply (drule_tac x = "sla ! (length sla - 1)" in spec)
    apply (rotate_tac -1)
           apply (drule_tac x = "snd(attack x1)" in spec)
      apply (erule mp)
      apply simp
          apply simp
      (* *)
         apply (case_tac "tl sl = []")
      apply (rotate_tac -3)
          apply (erule subst)
          apply (subgoal_tac "length sl = 1")
           apply simp
          apply (erule tl_lem1)
          apply assumption
      (* tl sl = [] finished *)
      apply (rule nth_app_eq)
          apply assumption
         apply (rotate_tac -3)
         apply (erule subst)
         apply (rule nth_tl_length)
      apply assumption
      apply simp
       apply (drule att_eq1)
       apply (rotate_tac -1)
       apply (erule subst)
       apply simp
      (* so far ...*)
      (* again tl sl = []*)
      apply (case_tac "tl sl = []")
      apply simp
      (* tl sl \<noteq> [] *)
      apply (rule allI)
      apply (rule impI)
      apply (subgoal_tac "(i < length sla - 1) \<or>  (i = length sla - 1) \<or>(((length sla) \<le> i) \<and> (i < length (sla @ (tl sl)) - (1::nat)))")
       apply (erule disjE)
        prefer 3
        apply (subgoal_tac "length (sla @ (tl sl)) = length sla + (length sl - 1)")
         apply arith
      apply simp
       apply (subst nth_app_eq1)
        apply arith
       apply (subst nth_app_eq1)
        apply arith
       apply (rotate_tac -4)
       apply (drule_tac x = i in spec)
       apply (erule mp)
       apply assumption
      (* i = length sla - 1 *)
      apply (erule disjE)
       apply (subst nth_app_eq1)
        apply simp
       apply (subst nth_app_eq2)
        apply simp
       apply (subgoal_tac "sla ! i = sl ! 0")
        apply (rotate_tac -1)
      apply (erule ssubst)
        apply (subgoal_tac "tl sl ! (i + (1::nat) - length sla) = sl ! 1")
         apply (rotate_tac -1)
         apply (erule ssubst)
         apply (rotate_tac -7)
         apply (drule_tac x = 0 in spec)
      apply (rotate_tac -1)
         apply (drule mp)
          apply simp
         apply simp
        apply simp
      apply (rule tl_eq1)
        apply assumption
       apply simp
  apply (subgoal_tac "\<forall> (a:: 's set) b (c :: 's set) d. (a, c) = (b, d) \<longrightarrow> c = d")
        apply (rotate_tac -1)
          apply (drule_tac x = "sla ! 0" in spec)
    apply (rotate_tac -1)
          apply (drule_tac x = "fst(attack x1)" in spec)
    apply (rotate_tac -1)
          apply (drule_tac x = "sla ! (length sla - 1)" in spec)
    apply (rotate_tac -1)
        apply (drule_tac x = "snd(attack x1)" in spec)
      apply (rotate_tac -1)
      apply (drule mp)
      apply simp
          apply simp
       apply simp
      (* length sla \<le> i \<and> i < length (sla @ tl sl) - (1::nat) *)
      apply (subst nth_app_eq2)
       apply arith
      apply (subst nth_app_eq2)
       apply arith
      apply (subst ineq2)
       apply (erule conjE,assumption)
      apply (subst nth_tl_length1)
       apply assumption
      apply (subst nth_tl_length1)
       apply assumption
      apply (rotate_tac -7)
      apply (drule_tac x = " (i - length sla + (1::nat))" in spec)
      apply (rotate_tac -1)
      apply (drule mp)
       prefer 2
       apply simp
      (* so far *)
      apply (rule ineq3)
        apply assumption+
       apply simp+
 (* third case \<or> of the overall second \<and> case *)
     apply (erule exE)
     apply (erule conjE)+
     apply (rotate_tac -4)
      (* an empty list of or attacks in the first \<and> element *is possible *)
     apply (case_tac "oal = []") 
      (* in this case fst(attack x1) = snd(attack x1) = fst x and we can use
         the existing sl *)
      (* otherwise oa \<noteq> [] pick one random element and perform the same
         proof with that as in the previous case for \<and> *)
apply force      
(* finally the third case \<or> *)      
by auto     



(* First need lemmas for showing that if \<turnstile> (oal \<oplus>\<^sub>\<or>\<^bsup>(attack A)\<^esup>) then for all
   xa in oal we have \<turnstile> xa. Same for \<and>. They are needed to invoke the IH.
   For each xa in oal we need to prove three cases (disj in premise): xa is base,
   and, or or-attack. 
   The use of this single element threefold IH seems quite complex with lots of 
   associativity restructuring needed to transfer to the goal-list oal .
   But for oal we only need to show that there is another list sl with base attack pairs 
   lined up. So even if we have from the assumption one small attack xa in the and-chain 
   oal which is again an or-attack with various alternatives (from IH) then we can pick one
   of the sl-sub chains and "implant" it into the result chain sl for oal. 
   How to set up the induction for the xla/ola is difficult maybe -- separate inductions
   for each case?
   Now, without the refinement, it should be a little easier. We
   simplify the conclusion (there is not necessarily a one-one structural 
   correspondance.
   The induction can be set up over lists on oal.
   *)


lemma ref_pres_att: "A \<sqsubseteq> A' \<Longrightarrow> attack A = attack A'"
  apply (erule refines_to.induct)
     apply simp
    defer
     apply simp
   apply (rule refl)
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
(* Same goes clearly for \<sqsubseteq>\<^sub>V *)
   
(* Not generally true: a \<and> refinement does not automatically guarantee that 
   the refined AT is valid even if the initial was: the refinmenet can insert a 
   new subtree that isn't valid. To achieve this prerequisite needed in the 
   below theorem, we need additional assumptions in the intermediate lemmas. 
lemma att_ref_rev [rule_format]: "A \<sqsubseteq> A' \<Longrightarrow> \<turnstile> (A :: ('s :: state) attree) \<longrightarrow>  \<turnstile> A'"

Even the specialisation to just base attacks is not valid for the same reasons as above   
lemma att_ref_rev [rule_format]: " \<turnstile> (A :: ('s :: state) attree) \<Longrightarrow> A \<sqsubseteq> \<N>\<^bsub>attack A\<^esub> \<longrightarrow>  \<turnstile> \<N>\<^bsub>attack A\<^esub>"
*)    

   (* obsolete now in the definition of \<turnstile> as  att_base
lemma base_att_rel_step: 
     "\<turnstile>\<N>\<^bsub>(s,s')\<^esub>  \<Longrightarrow> ((\<forall> y \<in> s'. \<exists> x \<in> s. x  \<rightarrow>\<^sub>i y) \<and> (\<forall> x \<in> s. \<exists> y \<in> s'. x  \<rightarrow>\<^sub>i y))" 
   apply (erule is_attack_tree.cases)
by simp+
  
lemma base_att_eq: "\<turnstile>\<N>\<^bsub>(s,s')\<^esub>  = ((\<forall> y \<in> s'. \<exists> x \<in> s. x  \<rightarrow>\<^sub>i y) \<and> (\<forall> x \<in> s. \<exists> y \<in> s'. x  \<rightarrow>\<^sub>i y))" 
  apply (rule iffI)  
   apply (erule base_att_rel_step)
    by (erule conjE, erule att_base, assumption)
*)    

lemma second_stepA: "\<lbrakk> \<turnstile>  \<N>\<^bsub>(I,s)\<^esub> \<rbrakk>
    \<Longrightarrow> Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s"
           apply (simp add:check_def)
           apply (rule subsetI)
    apply (rule CollectI)
           apply (rule conjI)
    apply (simp add: state_transition_refl_def)
            apply (rule_tac x = x in bexI)
             apply simp
   apply assumption
  apply (simp add: att_base)
(*    apply (erule conjE) *)
    apply (rotate_tac -1)
  apply (drule_tac x = x in bspec)
   apply assumption
  apply (erule bexE)
  apply (erule EF_step)
    by assumption

lemma second_stepB: "\<lbrakk> \<turnstile> (A :: ('s :: state) attree);  
                      (A :: ('s :: state) attree) =  (al \<oplus>\<^sub>\<and>\<^bsup>((I,s))\<^esup>);
              (\<exists> (sl :: ((('s :: state) set)list)). (sl \<noteq> []) \<and>
                 (sl ! 0, sl ! (length sl - 1)) = attack A \<and>
                 (\<forall> i < (length sl - 1).  \<turnstile> \<N>\<^bsub>(sl ! i,sl ! (i+1) )\<^esub>
                         )) \<rbrakk>
    \<Longrightarrow> Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s"    
  apply (simp add:check_def)
           apply (rule subsetI)
    apply (rule CollectI)
           apply (rule conjI)
    apply (simp add: state_transition_refl_def)
            apply (rule_tac x = x in bexI)
             apply simp
   apply assumption
  apply (subgoal_tac "\<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y")
   apply (drule_tac x = x in bspec)
    apply assumption
    apply (rotate_tac -1)
   apply (erule bexE)
   apply (erule EF_step_star, assumption)
    (* \<forall>x::'s\<in>I. \<exists>y::'s\<in>s. x \<rightarrow>\<^sub>i* y; try elim "\<exists> sl ..." quantifier and then
       list induction over sl (after integrating assumptions before a \<longrightarrow>)*)
  apply (erule exE)
  apply (rule mp)
   prefer 2
   apply (rotate_tac -1)
   apply assumption
  apply (rule mp)
   prefer 2
   apply (rotate_tac 2)
   apply assumption
  apply (rule_tac x = s in spec)
    apply (rule_tac x = I in spec)
  apply (rule_tac xs = sl in rev_nonempty_induct)
   apply simp
   apply clarify
apply (rule_tac x = xd in bexI)
    apply (simp add: state_transition_refl_def)
   apply simp
    apply (rule allI)+
  apply (rule impI)+
  apply (rotate_tac -1)
  apply (drule_tac x = xb in spec)
  apply (rotate_tac -1)
    apply (drule_tac x = "xs ! (length xs - Suc (0::nat))" in spec)
  apply (drule mp)
   apply assumption
  apply (drule mp)
  apply (rule conjI)  
   apply assumption
  apply (rule conjI)
    apply (rule zeroth_app_eq_rev)
    apply assumption
   apply (erule conjE)+
   apply assumption
  apply (erule conjE)+
   apply (rule conjI)
    apply (rule refl)
   apply (rule allI)
    apply (rule impI)
   apply (rotate_tac -4)
   apply (drule_tac x = i in spec)
  apply (rotate_tac -1)
   apply (drule mp)
  apply simp
   apply (rule_tac t = "xs ! i" and s = "(xs @ [xa]) ! i" in subst)
  apply (rule nth_app_eq1)
    apply simp
    apply (rule_tac t = "xs ! (Suc i)" and s = "(xs @ [xa]) ! Suc i" in subst)
   apply (subst nth_app_eq1)
     apply simp
    apply (rule refl)
   apply assumption
  apply (rule ballI)
    apply (rotate_tac -2)
  apply (drule_tac x = xd in bspec)
   apply assumption
    apply (erule bexE)
  apply (subgoal_tac "\<forall> y \<in> xs ! (length xs - Suc (0::nat)). \<exists> z \<in> xc. y  \<rightarrow>\<^sub>i z")
   apply (drule_tac x = y in bspec)
    apply assumption
   apply (erule bexE)
   apply (rule_tac x = z in bexI)
    apply (simp add : state_transition_refl_def)
    apply (erule rtrancl.intros(2))
    apply simp
   apply assumption
  apply (subgoal_tac "\<turnstile>\<N>\<^bsub>(xs ! (length xs - Suc (0::nat)), xc)\<^esub>")
   apply (simp add: att_base)    
   apply (erule conjE)+
   apply (rotate_tac -4)
  apply (erule subst)
  apply (subgoal_tac 
"xs ! (length xs - Suc (0::nat)) = ((xs @ [xa]) ! (length (xs @ [xa]) - Suc (1::nat)))")
   apply (rotate_tac -1)
   apply (erule ssubst)
   apply (drule_tac x = " (length (xs @ [xa]) - Suc (1::nat))" in spec)
   apply (drule mp)
    apply simp+
  apply (rule nth_app_eq1_rev)
    by simp

  
lemma second_stepC: "\<lbrakk> \<turnstile> (A :: ('s :: state) attree); 
                      (A :: ('s :: state) attree) =  (oal \<oplus>\<^sub>\<or>\<^bsup>((I,s))\<^esup>);
      (\<forall> a \<in> (set oal). (\<exists> al. (a = (al \<oplus>\<^sub>\<and>\<^bsup>(attack A)\<^esup>)) \<and>
              (\<exists> (sl :: ((('s :: state) set)list)). (sl \<noteq> []) \<and>
                (sl ! 0, sl ! (length sl - 1)) = attack A \<and>
                 (\<forall> i < (length sl - 1).  \<turnstile> \<N>\<^bsub>(sl ! i,sl ! (i+1) )\<^esub>
                         )))) \<rbrakk>
    \<Longrightarrow> Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s"   
  apply (case_tac "I = s")
    apply (simp add:check_def)
           apply (rule subsetI)
    apply (rule CollectI)
           apply (rule conjI)
    apply (simp add: state_transition_refl_def)
            apply (rule_tac x = x in bexI)
             apply simp
    apply assumption
   apply (erule EF_lem2a)
     apply (simp add:check_def)
           apply (rule subsetI)
    apply (rule CollectI)
           apply (rule conjI)
    apply (simp add: state_transition_refl_def)
            apply (rule_tac x = x in bexI)
             apply simp
    apply assumption
  apply (subgoal_tac "oal \<noteq> []")
    prefer 2
   apply (erule att_or_empty_rev)
   apply assumption
(* *)    
      apply (subgoal_tac "\<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y")
   apply (drule_tac x = x in bspec)
    apply assumption
    apply (rotate_tac -1)
   apply (erule bexE)
   apply (erule EF_step_star, assumption)
    (* \<forall>x::'s\<in>I. \<exists>y::'s\<in>s. x \<rightarrow>\<^sub>i* y; try elim "\<exists> sl ..." quantifier and then
       list induction over sl (after integrating assumptions before a \<longrightarrow>)*)
  apply (subgoal_tac "set oal \<noteq> {}")
   apply (drule not_empty_ex)
   apply (erule exE)
   apply (drule_tac x = xa in bspec, assumption)
   apply (erule conjE)
    apply (thin_tac "\<exists>al::'s attree list. xa = (al \<oplus>\<^sub>\<and>\<^bsup>(I, s)\<^esup>)")
  apply (erule exE)
  apply (rule mp)
   prefer 2
   apply (rotate_tac -1)
   apply assumption
  apply (rule mp)
   prefer 2
   apply (rotate_tac 3)
   apply assumption
  apply (rule_tac x = s in spec)
    apply (rule_tac x = I in spec)
  apply (rule_tac xs = sl in rev_nonempty_induct)
   apply simp
   apply clarify
apply (rule_tac x = xe in bexI)
    apply (simp add: state_transition_refl_def)
   apply simp
    apply (rule allI)+
  apply (rule impI)+
  apply (rotate_tac -1)
  apply (drule_tac x = xc in spec)
  apply (rotate_tac -1)
    apply (drule_tac x = "xs ! (length xs - Suc (0::nat))" in spec)
  apply (drule mp)
   apply assumption
  apply (drule mp)
  apply (rule conjI)  
   apply assumption
  apply (rule conjI)
    apply (rule zeroth_app_eq_rev)
    apply assumption
   apply (erule conjE)+
   apply assumption
  apply (erule conjE)+
   apply (rule conjI)
    apply (rule refl)
   apply (rule allI)
    apply (rule impI)
   apply (rotate_tac -4)
   apply (drule_tac x = i in spec)
  apply (rotate_tac -1)
   apply (drule mp)
  apply simp
   apply (rule_tac t = "xs ! i" and s = "(xs @ [xb]) ! i" in subst)
  apply (rule nth_app_eq1)
    apply simp
    apply (rule_tac t = "xs ! (Suc i)" and s = "(xs @ [xb]) ! Suc i" in subst)
   apply (subst nth_app_eq1)
     apply simp
    apply (rule refl)
   apply assumption
  apply (rule ballI)
    apply (rotate_tac -2)
  apply (drule_tac x = xe in bspec)
   apply assumption
    apply (erule bexE)
  apply (subgoal_tac "\<forall> y \<in> xs ! (length xs - Suc (0::nat)). \<exists> z \<in> xd. y  \<rightarrow>\<^sub>i z")
   apply (drule_tac x = y in bspec)
    apply assumption
   apply (erule bexE)
   apply (rule_tac x = z in bexI)
    apply (simp add : state_transition_refl_def)
    apply (erule rtrancl.intros(2))
    apply simp
   apply assumption
  apply (subgoal_tac "\<turnstile>\<N>\<^bsub>(xs ! (length xs - Suc (0::nat)), xd)\<^esub>")
   apply (simp add: att_base)    
   apply (erule conjE)+
   apply (rotate_tac -4)
  apply (erule subst)
  apply (subgoal_tac 
"xs ! (length xs - Suc (0::nat)) = ((xs @ [xb]) ! (length (xs @ [xb]) - Suc (1::nat)))")
   apply (rotate_tac -1)
   apply (erule ssubst)
   apply (drule_tac x = " (length (xs @ [xb]) - Suc (1::nat))" in spec)
   apply (drule mp)
    apply simp+
   apply (rule nth_app_eq1_rev)
    apply simp
by simp
 
      
  
theorem AT_EF: "\<lbrakk> \<turnstile> (A :: ('s :: state) attree); (I,s) = attack A \<rbrakk> \<Longrightarrow>
 (Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s) } (I :: ('s :: state)set)  \<turnstile> EF s)" 
  apply (frule first_step)
  apply (erule disjE)
   apply (rule second_stepA)
    apply simp
  apply (erule disjE)
  apply (erule exE)
  apply (erule conjE)+
  apply (rule second_stepB, assumption)
     apply (erule ssubst, assumption)+
    apply simp
  apply (erule exE)
  apply (erule conjE)+
  apply (rule second_stepC, assumption)
by simp+

theorem ATV_EF: "\<lbrakk> \<turnstile>\<^sub>V (A :: ('s :: state) attree); (I,s) = attack A \<rbrakk> \<Longrightarrow>
 (Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s) } (I :: ('s :: state)set)  \<turnstile> EF s)"   
    apply (simp add: ref_validity_def)
  apply (erule exE)
  apply (simp add: valid_ref_def)
    apply (erule conjE)
  apply (erule AT_EF)
  by (simp add: ref_pres_att)
    
    
(* Completeness *)
    
lemma Compl_step1: 
"Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s 
\<Longrightarrow> \<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y"
  apply (simp add:check_def)
         apply clarify
apply (drule subsetD)
   apply assumption
  apply (drule CollectD)
  apply (erule conjE)
  by (erule EF_step_star_rev)
    
  
   
lemma Compl_step2: "I \<noteq> {} \<Longrightarrow>  \<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y \<Longrightarrow> 
                     I = s \<or>
                     (\<exists> (sl :: ((('s :: state) set)list)). (sl \<noteq> []) \<and>
                 (sl ! 0, sl ! (length sl - 1)) = (I,s) \<and>
                 (\<forall> i < (length sl - 1).  \<turnstile> \<N>\<^bsub>(sl ! i,sl ! (i+1) )\<^esub>
                         ))"
  apply clarify
  apply (rule notnotD)
    apply (rotate_tac 1)
  apply (erule contrapos_nn)
      apply (rule mp)
   defer
   apply assumption
  apply (rotate_tac 1)
  apply (rule mp)
   defer
   apply assumption
  apply (rotate_tac 1)
  apply (rule mp)
  defer
   apply assumption
  apply (thin_tac "I \<noteq> s")
  apply (drule not_empty_ex)
  apply (erule exE)
  apply (drule_tac x = x in bspec)
   apply assumption
  apply (erule bexE)
  apply (rule_tac x = I in spec)
    apply (rule_tac x = s in spec)
    apply (unfold state_transition_refl_def)
    apply (erule rtrancl.induct)
  apply (thin_tac "y \<in> s")
  apply (thin_tac "x \<in> I")
   apply clarify    
  apply (rule mp)
  defer
   apply assumption
  apply (rotate_tac 1)
  apply (rule mp)
   defer
   apply assumption
  apply (rotate_tac 1)
  apply (rule mp)
  defer
   apply assumption
  apply (thin_tac "y \<in> s")
  apply (thin_tac "x \<in> I")
  apply (rule_tac x = I in spec)
    apply (rule_tac x = s in spec)
    apply (erule rtrancl.induct)
by auto
  
lemma map_hd_lem[rule_format] : "n > 0 \<longrightarrow> (f 0 #  map (\<lambda>i::nat. f i) [1::nat..<n]) = map  (\<lambda>i::nat. f i) [0..<n]"    
  by (simp add : hd_map upt_rec)
    
lemma map_Suc_lem[rule_format] : "n > 0 \<longrightarrow> map (\<lambda> i:: nat. f i)[1..<n] =
                                  map (\<lambda> i:: nat. f(Suc i))[0..<(n - 1)]"
  apply (case_tac n)
   apply simp+
  apply (induct_tac nat)
by simp+
     
lemma Compl_step3: "I = s \<or>
                     (\<exists> (sl :: ((('s :: state) set)list)). (sl \<noteq> []) \<and>
                 (sl ! 0, sl ! (length sl - 1)) = (I,s) \<and>
                 (\<forall> i < (length sl - 1).  \<turnstile> \<N>\<^bsub>(sl ! i,sl ! (i+1) )\<^esub>
                         )) \<Longrightarrow> \<exists> (A :: ('s :: state) attree).
                                   \<turnstile> A \<and> attack A = (I,s)"
  apply (erule disjE)
  apply (rule_tac x = "([] \<oplus>\<^sub>\<and>\<^bsup>((s,s))\<^esup>)" in exI)  
   apply simp
   apply (subst att_and)
   apply simp
    apply (erule exE)
  apply (rule_tac x = 
"[ \<N>\<^bsub>(sl ! i, sl ! (i + (1::nat)))\<^esub>. i \<leftarrow> [0..<(length sl-(1::nat))]] \<oplus>\<^sub>\<and>\<^bsup>((I,s))\<^esup>" in exI)
  apply (rule conjI)
  prefer 2
   apply simp
    (*  *) 
    apply (rule mp)
    prefer 2
   apply assumption
  apply (rule_tac x = I in spec)
    apply (rule_tac x = s in spec)
  apply (rule_tac list = sl in list.induct)
   apply simp
  apply clarify
  apply simp
  apply (case_tac "x2 = []")
   apply simp
   apply (rule att_and_empty2)
  apply (drule mp)
   apply (rule conjI)
    apply assumption
   apply (rule allI)
   apply (rule impI)
   apply (rotate_tac -3)
   apply (drule_tac x = "i + 1" in spec)
   apply (drule mp)
    apply arith
   apply simp
  apply simp
  apply (subgoal_tac "(map (\<lambda>i::nat. \<N>\<^bsub>((x1 # x2) ! i, x2 ! i)\<^esub>) [0::nat..<length x2]) = 
                      \<N>\<^bsub>(x1, x2 ! 0)\<^esub> # (map (\<lambda>i::nat. \<N>\<^bsub>(x2 ! i, x2 ! Suc i)\<^esub>)[0::nat..<length x2 - Suc (0::nat)])")
  apply (rotate_tac -1)
   apply (erule ssubst)
   apply (rule att_comp_and_cons)
     apply (rotate_tac -3)
     apply (drule_tac x = 0 in spec)
     apply simp
    apply simp
   apply assumption
  apply (subgoal_tac " map (\<lambda>i::nat. \<N>\<^bsub>((x1 # x2) ! i, x2 ! i)\<^esub>) [0::nat..<length x2] =
                       \<N>\<^bsub>(x1, x2 ! (0::nat))\<^esub> #
                        map (\<lambda>i::nat. \<N>\<^bsub>((x1 # x2) ! Suc i, x2 ! Suc i)\<^esub>) [0::nat..<length x2 - 1]")
   apply simp
  apply (subgoal_tac "map (\<lambda>i::nat. \<N>\<^bsub>((x1 # x2) ! Suc i, x2 ! Suc i)\<^esub>) [0::nat..<length x2 - (1::nat)]
                   = map (\<lambda>i::nat. \<N>\<^bsub>((x1 # x2) ! i, x2 ! i)\<^esub>) [1::nat..<length x2]")
   apply (rotate_tac -1)
   apply (erule ssubst)
   apply (subgoal_tac "x1 = (x1 # x2) ! 0")
    apply (rotate_tac -1)
    apply (rule_tac P = "(\<lambda> y. map (\<lambda>i::nat. \<N>\<^bsub>((x1 # x2) ! i, x2 ! i)\<^esub>) [0::nat..<length x2] =
       \<N>\<^bsub>(y, x2 ! (0::nat))\<^esub> # map (\<lambda>i::nat. \<N>\<^bsub>((x1 # x2) ! i, x2 ! i)\<^esub>) [1::nat..<length x2])" 
      in ssubst)
     apply assumption
    apply (rule sym)
    apply (rule map_hd_lem)
    apply simp
   apply simp
  apply (rule sym)
  apply (rule map_Suc_lem)
    by simp

theorem Completeness: "I \<noteq> {} \<Longrightarrow> Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s 
\<Longrightarrow> \<exists> (A :: ('s :: state) attree).
                                   \<turnstile> A \<and> attack A = (I,s)"
  apply (rule Compl_step3)
  apply (erule Compl_step2)
  by (erule Compl_step1)
    
end