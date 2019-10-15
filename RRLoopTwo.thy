theory RRLoopTwo
(* Second instance of the RRLoop: note that here the infrastructure type gets re-defined.
   Corresponding definitions are defined again for the new type. They co-exist with
   the previous definitions. This is possible thanks to Isabelle's overloading and 
   theory name spacing possibilities! *)
imports hcKripkeOne FMap (* "/Applications/Isabelle2018.app/Isabelle/src/HOL/Hoare/Hoare_Logic" *)
begin
(* a simple definition of data and instantiating 
the generic types of the Hoare logic to pairs of owner and data as 
basic data type for specification. This enables the unique marking
(modulo insider impersonation) of data within the system. 
The manipulation of the data (using simple while language) can thus 
be modelled but additionally taking the ownership into account. We use 
eval below and anchor the access control in restricing base functions
for the basic com type *)
(* taken over from previous level:
datatype action = get | move | eval |put
typedecl actor 
type_synonym identity = string
consts Actor :: "string => actor"
type_synonym policy = "((actor => bool) * action set)"

definition ID :: "[actor, string] \<Rightarrow> bool"
where "ID a s \<equiv> (a = Actor s)"

datatype location = Location nat
*)

type_synonym data = string
  (* Inspired by Myers DLM mode: first is the owner of a data item, second is the
     set of all actors that may access the data item *)
type_synonym dlm = "actor * actor set"
  (* the following type constructors are from Hoare_logic:
     bexp and assn are just synonyms for set, and
     com is a simple datatype repesenting while command language
     over some basic 'a \<Rightarrow> 'a functions, while 'a sem is
     just the type of relations 'a \<Rightarrow> 'a \<Rightarrow> bool representing relational
     semantics *)

type_synonym acond = "(dlm * data) set"
(*
type_synonym aassn = "(dlm * data) assn"
type_synonym acom = "(dlm * data) com"
type_synonym asem = "(dlm * data) sem"
*)

datatype igraph = Lgraph "(location * location)set" "location \<Rightarrow> identity set"
                         "actor \<Rightarrow> (string set * string set)"  "location \<Rightarrow> acond"
datatype infrastructure = 
         Infrastructure "igraph" 
                        "[igraph ,location] \<Rightarrow> policy set" 
primrec loc :: "location \<Rightarrow> nat"
where  "loc(Location n) = n"
primrec gra :: "igraph \<Rightarrow> (location * location)set"
where  "gra(Lgraph g a c l) = g"
primrec agra :: "igraph \<Rightarrow> (location \<Rightarrow> identity set)"
where  "agra(Lgraph g a c l) = a"
primrec cgra :: "igraph \<Rightarrow> (actor \<Rightarrow> string set * string set)"
where  "cgra(Lgraph g a c l) = c"
primrec lgra :: "igraph \<Rightarrow> (location \<Rightarrow> acond)"
where  "lgra(Lgraph g a c l) = l"

definition nodes :: "igraph \<Rightarrow> location set" 
where "nodes g == { x. (? y. ((x,y): gra g) | ((y,x): gra g))}"

definition actors_graph :: "igraph \<Rightarrow> identity set"  
where  "actors_graph g == {x. ? y. y : nodes g \<and> x \<in> (agra g y)}"

primrec graphI :: "infrastructure \<Rightarrow> igraph"
where "graphI (Infrastructure g d) = g"
primrec delta :: "[infrastructure, igraph, location] \<Rightarrow> policy set"
where "delta (Infrastructure g d) = d"
primrec tspace :: "[infrastructure, actor ] \<Rightarrow> string set * string set"
  where "tspace (Infrastructure g d) = cgra g"
primrec lspace :: "[infrastructure, location ] \<Rightarrow> acond"
where "lspace (Infrastructure g d) = lgra g"
definition credentials :: "string set * string set \<Rightarrow> string set"
  where  "credentials lxl \<equiv> (fst lxl)"
definition has :: "[igraph, actor * string] \<Rightarrow> bool"
  where "has G ac \<equiv> snd ac \<in> credentials(cgra G (fst ac))"
definition roles :: "string set * string set \<Rightarrow> string set"
  where  "roles lxl \<equiv> (snd lxl)"
definition role :: "[igraph, actor * string] \<Rightarrow> bool"
  where "role G ac \<equiv> snd ac \<in> roles(cgra G (fst ac))"


definition owner :: "dlm * data \<Rightarrow> actor" where "owner d \<equiv> fst(fst d)"
    
definition owns :: "[igraph, location, actor, dlm * data] \<Rightarrow> bool"    
  where "owns G l a d \<equiv> owner d = a"
    
definition readers :: "dlm * data \<Rightarrow> actor set"
  where "readers d \<equiv> snd (fst d)"

definition has_access :: "[igraph, location, actor, dlm * data] \<Rightarrow> bool"    
where "has_access G l a d \<equiv> owns G l a d \<or> a \<in> readers d"
  
definition actor_can_delete ::   "[infrastructure, actor, location] \<Rightarrow> bool"
where actor_can_delete_def: "actor_can_delete I h l \<equiv>  
                   (\<forall> as n. ((h, as), n) \<notin> (lgra (graphI I) l))"
        

definition atI :: "[identity, igraph, location] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> (agra G l)"

definition enables :: "[infrastructure, location, actor, action] \<Rightarrow> bool"
where
"enables I l a a' \<equiv>  (\<exists> (p,e) \<in> delta I (graphI I) l. a' \<in> e \<and> p a)"

definition move_graph_a :: "[identity, location, location, igraph] \<Rightarrow> igraph"
where "move_graph_a n l l' g \<equiv> Lgraph (gra g) 
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then 
                     ((agra g)(l := (agra g l) - {n}))(l' := (insert n (agra g l')))
                     else (agra g))(cgra g)(lgra g)"
inductive state_transition_in :: "[infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
  move: "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          (a) \<in> actors_graph(graphI I); enables I l' (Actor a) move;
         I' = Infrastructure (move_graph_a a l l' (graphI I))(delta I) \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 
| get_data : "G = graphI I \<Longrightarrow> h @\<^bsub>G\<^esub> l \<Longrightarrow>  l \<in> nodes G \<Longrightarrow> l' \<in> nodes G \<Longrightarrow> 
        enables I l (Actor h) get \<Longrightarrow> 
       ((Actor h', hs), n) \<in> lgra G l' \<Longrightarrow> Actor h \<in> hs \<or> h = h' \<Longrightarrow> 
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)
                   ((lgra G)(l := (lgra G l)  \<union> {((Actor h', hs), n)})))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| process : "G = graphI I \<Longrightarrow> h @\<^bsub>G\<^esub> l \<Longrightarrow> l \<in> nodes G \<Longrightarrow> 
        enables I l (Actor h) eval \<Longrightarrow> 
       ((Actor h', hs), n) \<in> lgra G l \<Longrightarrow> Actor h \<in> hs \<or> h = h' \<Longrightarrow>
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)
                   ((lgra G)(l := ((lgra G l)  - {(y, x). x = n}
                    \<union> {f ((Actor h', hs), n)}))))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"  
| del_data : "G = graphI I \<Longrightarrow> h \<in> actors_graph G \<Longrightarrow> l \<in> nodes G \<Longrightarrow>
       ((Actor h, hs), n) \<in> lgra G l \<Longrightarrow> 
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)
                   ((lgra G)(l := (lgra G l) - {(y, x). x = n })))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| put : "G = graphI I \<Longrightarrow> h @\<^bsub>G\<^esub> l \<Longrightarrow> l \<in> nodes G \<Longrightarrow> 
        enables I l (Actor h) put \<Longrightarrow>
        I' = Infrastructure 
                  (Lgraph (gra G)(agra G)(cgra G)
                          ((lgra G)(l := (lgra G l) \<union> {((Actor h, hs), n)})))
                   (delta I)
          \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
instantiation "infrastructure" :: state
begin

definition 
   state_transition_infra_def: "(i \<rightarrow>\<^sub>i i') =  (i \<rightarrow>\<^sub>n (i' :: infrastructure))"

instance
  by (rule MC.class.MC.state.of_class.intro)

definition state_transition_in_refl ("(_ \<rightarrow>\<^sub>n* _)" 50)
where "s \<rightarrow>\<^sub>n* s' \<equiv> ((s,s') \<in> {(x,y). state_transition_in x y}\<^sup>*)"

end
      
lemma move_graph_eq: "move_graph_a a l l g = g"  
proof (simp add: move_graph_a_def, case_tac g, force)
qed     


(* general scheme for map over finite sets.
   This would be a useful provision for the Finite_Set library: everyone needs
   a simple map on Finite Sets all the time! 
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

thm finite_induct

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
*)

definition ref_map :: "[RRLoopTwo.infrastructure, 
                        [RRLoopOne.igraph, RRLoopOne.location] \<Rightarrow> policy set]
                        \<Rightarrow> RRLoopOne.infrastructure"
  where "ref_map I lp = RRLoopOne.Infrastructure 
                                 (RRLoopOne.Lgraph
                                        (RRLoopTwo.gra (graphI I))(RRLoopTwo.agra (graphI I))
                                        (RRLoopTwo.cgra (graphI I))
                                        (\<lambda> l. fmap snd (RRLoopTwo.lgra (graphI I) l)))
                                                                         lp"
(* archive, older approaches that are similar:
 (\<lambda> l. Finite_Set.fold (\<lambda> x y. insert (snd x) y){}(RRLoopTwo.lgra (graphI I) l)))
(\<lambda> l. {x. ? y. (y,x) \<in> (RRLoopTwo.lgra (graphI I) l)}))
*)

lemma delta_invariant: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  delta(z) = delta(z')"    
  apply clarify
  apply (erule state_transition_in.cases)
  by simp+
end
