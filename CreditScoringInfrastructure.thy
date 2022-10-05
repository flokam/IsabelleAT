section \<open>Infrastructures for Credit Scoring\<close>
text \<open>The Isabelle Infrastructure framework supports the representation of infrastructures 
as graphs with actors and policies attached to nodes. These infrastructures 
are the {\it states} of the Kripke structure. 
The transition between states is triggered by non-parametrized
actions @{text \<open>get, move, eval, put\<close>} executed by actors. 
Actors are given by an abstract type @{text \<open>actor\<close>} and a function 
@{text \<open>Actor\<close>} that creates elements of that type from identities 
(of type @{text \<open>string\<close>}). Policies are given by pairs of predicates 
(conditions) and sets of (enabled) actions.\<close>
subsection \<open>Actors, actions, and data labels\<close>
theory CreditScoringInfrastructure
  imports Refinement
begin
datatype action = get | move | eval | put

typedecl actor 
type_synonym identity = string
consts Actor :: "string \<Rightarrow> actor"
type_synonym policy = "((actor \<Rightarrow> bool) * action set)"

definition ID :: "[actor, string] \<Rightarrow> bool"
  where "ID a s \<equiv> (a = Actor s)"

subsection \<open>Infrastructure graphs and policies\<close>
text\<open>Actors are contained in an infrastructure graph. An @{text \<open>igraph\<close>} contains
a set of location pairs representing the topology of the infrastructure
as a graph of nodes and a list of actor identities associated to each node 
(location) in the graph. \<close>
datatype location = Location nat

text \<open>The Decentralised Label Model (DLM) \cite{ml:98} introduced the idea to
label data by owners and readers. We pick up this idea and formalize
a new type to encode the owner and the set of readers as a pair.
The first element is the owner of a data item, the second one is the
set of all actors that may access the data item.
This enables the unique security 
labelling of data within the system additionally taking the ownership into 
account.\<close>
type_synonym dob = nat
datatype ethnicity = black |  white | asian
type_synonym data = \<open>location \<times> nat \<times> dob \<times> ethnicity\<close>
type_synonym dlm = \<open>actor \<times> actor set\<close>

datatype igraph = Lgraph 
                    (gra: \<open>(location \<times> location)set\<close>)
                    (agra: \<open>location \<Rightarrow> identity set\<close>)
                    (dgra: \<open> identity \<Rightarrow> dlm \<times> data\<close>)
                    (bb: \<open> data \<Rightarrow> bool\<close>)
                    (requests: \<open>(identity \<times> bool option)set\<close>)


datatype infrastructure = 
         Infrastructure (graphI: \<open>igraph\<close>)
                        (delta: \<open>[igraph, location] \<Rightarrow> policy set\<close>)
                       
primrec loc :: \<open>location \<Rightarrow> nat\<close>
where  \<open>loc(Location n) = n\<close>

lemma agra_simps: \<open>agra (Lgraph g a d b e) = a\<close>
 by (rule CreditScoringInfrastructure.igraph.sel(2))

definition nodes :: \<open>igraph \<Rightarrow> location set\<close>
where \<open>nodes g == { x. (? y. ((x,y): gra g) | ((y,x): gra g))}\<close>

definition actors_graph :: "igraph \<Rightarrow> identity set"  
where  "actors_graph g == {x. ? y. y : nodes g \<and> x \<in> (agra g y)}"

text \<open>There are projection functions text{@ \<open>graphI\<close>} and text{@ \<open>delta\<close>} when applied
to an infrastructure return the graph and the policy, respectively.\<close>

lemma graphI_simps[simp]: \<open>graphI (Infrastructure g d) = g\<close>
  by (rule infrastructure.sel(1))

lemma delta_simps[simp]: \<open>delta (Infrastructure g d) = d\<close>
  by (rule infrastructure.sel(2))

text \<open>Predicates and projections for the labels to encode their meaning.\<close>
definition owner :: "dlm * data \<Rightarrow> actor" where "owner d \<equiv> fst(fst d)"
definition owns :: "[igraph, location, actor, dlm * data] \<Rightarrow> bool"
  where "owns G l a d \<equiv> owner d = a"
definition readers :: "dlm * data \<Rightarrow> actor set"
  where "readers d \<equiv> snd (fst d)"

text \<open>The predicate @{text \<open>has_access\<close>} is true for owners or readers.\<close> 
definition has_access :: "[igraph, location, actor, dlm * data] \<Rightarrow> bool"    
where "has_access G l a d \<equiv> owns G l a d \<or> a \<in> readers d"

text \<open>We define a type of functions that preserves the security labeling and a 
   corresponding function application  operator.\<close>  
typedef label_fun = "{f :: dlm * data \<Rightarrow> dlm * data. 
                        \<forall> x:: dlm * data. fst x = fst (f x)}"  
  by (fastforce)

definition secure_process :: "label_fun \<Rightarrow> dlm * data \<Rightarrow> dlm * data" (infixr "\<Updown>" 50)
  where "f  \<Updown> d \<equiv> (Rep_label_fun f) d" 

text \<open>The predicate atI -- mixfix syntax @{text \<open>@\<^bsub>G\<^esub>\<close>} -- expresses that an actor (identity) 
      is at a certain location in an igraph.\<close>
definition atI :: "[identity, igraph, location] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> (agra G l)"

text \<open>Policies specify the expected behaviour of actors of an infrastructure. 
They are defined by the @{text \<open>enables\<close>} predicate:
an actor @{text \<open>h\<close>} is enabled to perform an action @{text \<open>a\<close>} 
in infrastructure @{text \<open>I\<close>}, at location @{text \<open>l\<close>}
if there exists a pair @{text \<open>(p,e)\<close>} in the local policy of @{text \<open>l\<close>}
(@{text \<open>delta I l\<close>} projects to the local policy) such that the action 
@{text \<open>a\<close>} is a member of the action set @{text \<open>e\<close>} and the policy 
predicate @{text \<open>p\<close>} holds for actor @{text \<open>h\<close>}.\<close>
definition enables :: "[infrastructure, location, actor, action] \<Rightarrow> bool"
where
"enables I l a a' \<equiv>  (\<exists> (p,e) \<in> delta I (graphI I) l. a' \<in> e \<and> p a)"

text \<open>The behaviour is the good behaviour, i.e. everything allowed by the policy of infrastructure I.\<close>
definition behaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "behaviour I \<equiv> {(t,a,a'). enables I t a a'}"

text \<open>The misbehaviour is the complement of the behaviour of an infrastructure I.\<close>
definition misbehaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "misbehaviour I \<equiv> -(behaviour I)"

subsection "State transition on infrastructures"
text \<open>The state transition defines how actors may act on infrastructures through actions
    within the boundaries of the policy. It is given as an inductive definition over the 
    states which are infrastructures.  This state transition relation is dependent on actions but also on
    enabledness and the current state of the infrastructure.\<close>

text \<open>The @{text \<open>move_graph_a\<close>} function encapsulates the infrastructure state change for a 
      move action used in the subsequent rule move. It relocates the actor from a location l
      to a new location l' if the actor is actually at l and is not at l'. Additionally, 
      here for the CreditScoring application, the new location l' needs to be updated in the 
      actors data by adapting the dgra component of the infrastructure state graph.\<close>
definition move_graph_a :: "[identity, location, location, igraph] \<Rightarrow> igraph"
where "move_graph_a n l l' G \<equiv> Lgraph (gra G) 
                                 (if n \<in> ((agra G) l) &  n \<notin> ((agra G) l') then 
                                      ((agra G)(l := (agra G l) - {n}))(l' := (insert n (agra G l')))
                                      else (agra G))
                               ((dgra G)(n := (fst (dgra G n),(l',snd(snd(dgra G n)))))) 
                    (bb G)(requests G)"

definition put_graph_a 
  where "put_graph_a a l G \<equiv> (Lgraph (gra G)(agra G)(dgra G)(bb G)
                                      (insert (a, None)(requests G)))"

definition eval_graph_a
  where "eval_graph_a a l G \<equiv> (Lgraph (gra G)(agra G)(dgra G)(bb G)
                          (insert (a, Some (bb G (snd (dgra G a))))(requests G - {(a, None)})))"

definition get_graph_a
  where \<open>get_graph_a a l m G \<equiv> (Lgraph (gra G)(agra G)
                         ((dgra G)(a := (fst (dgra G a),(fst(snd (dgra G a)),m,snd(snd(snd(dgra G a)))))))
                         (bb G)(requests G))\<close>

text \<open>The state transition relation defines the semantics for the actions. We concentrate
     only on two: move and get. Move models the moving of actors from one locations to another
     automatically posting the ephemeral ids at the new location (and stop posting them at the 
     old location, i.e. deleting them there) -- this is implemented in @{text \<open>move_graph_a\<close>}
     above.
     For get, an actor a at a location can use get, if he's entitled to do that by the policy, 
     to extend hos knowledge set. He adds all combinations of the actors a sees at the location 
     with all ephemeral ids she measures, i.e. which are in the set @{text \<open>egra G l\<close>}. If a
     already has a nonempty knowledge set @{text \<open>kgra G (Actor a)\<close>} she can already improve
     her knowledge by building an intersection with the previous knowledge set.\<close>
inductive state_transition_in :: "[infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
  where
  put : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow> l \<in> nodes G \<Longrightarrow> 
          enables I l (Actor a) put \<Longrightarrow>
          I' = Infrastructure 
                  (put_graph_a a l G)
                  (delta I) \<Longrightarrow>
          I \<rightarrow>\<^sub>n I'"
|   eval : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow> l \<in> nodes G \<Longrightarrow>
           c \<in> actors_graph G \<Longrightarrow> (a, None) \<in> requests G \<Longrightarrow>
           Actor c \<in> readers (dgra G a) \<or> Actor c = owner (dgra G a) \<Longrightarrow> 
           enables I l (Actor c) eval \<Longrightarrow>
          I' = Infrastructure 
                  (eval_graph_a a l G)
                  (delta I) \<Longrightarrow>
          I \<rightarrow>\<^sub>n I'"
|   move: "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          a \<in> actors_graph(graphI I); enables I l' (Actor a) move;
         I' = Infrastructure (move_graph_a a l l' G)(delta I) \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 
| get: "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow> l \<in> nodes G \<Longrightarrow>
          enables I l (Actor a) get \<Longrightarrow>
          I' = Infrastructure
                 (get_graph_a a l m G)
                 (delta I) \<Longrightarrow>
          I \<rightarrow>\<^sub>n I'"

text \<open>Note that the type infrastructure can now be instantiated to the axiomatic type class 
      @{text\<open>state\<close>} which enables the use of the underlying Kripke structures and CTL.\<close>
instantiation "infrastructure" :: state
begin
definition 
   state_transition_infra_def: "(i \<rightarrow>\<^sub>i i') =  (i \<rightarrow>\<^sub>n (i' :: infrastructure))"

instance
  by (rule MC.class.MC.state.of_class.intro)

definition state_transition_in_refl ("(_ \<rightarrow>\<^sub>n* _)" 50)
where "s \<rightarrow>\<^sub>n* s' \<equiv> ((s,s') \<in> {(x,y). state_transition_in x y}\<^sup>*)"

end

text \<open>PCR algorithm\<close>
text \<open>The definition of closest gives a unique predecessor s wrt @{text \<open>\<rightarrow>\<^sub>n*\<close>} for two points s' s''.\<close>
definition \<open>closest s s' s'' \<equiv> ((s \<rightarrow>\<^sub>n*  s') \<and> (s \<rightarrow>\<^sub>n* s'') \<and>
               (\<forall> s0. s0 \<rightarrow>\<^sub>n* s' \<and> s0 \<rightarrow>\<^sub>n* s'' \<longrightarrow> s0 \<rightarrow>\<^sub>n* s))\<close>

text \<open>Using the definition of closest we can define counterfactuals for a state s wrt a desirable property
      P as states s'' with common predecessor s' if these exist. \<close>
definition \<open>counterfactuals s P \<equiv> {s''. P s'' \<and> (\<exists> s'. (s' \<rightarrow>\<^sub>n* s'') \<and> closest s' s s'')}\<close>

(* standard invariants *)
lemma delta_invariant: "\<forall> z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>  delta(z) = delta(z')"    
  by (clarify, erule state_transition_in.cases, simp+)

lemma init_state_policy0: 
  assumes "\<forall> z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>  delta(z) = delta(z')"
      and "(x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    shows "delta(x) = delta(y)"
proof -
  have ind: "(x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
             \<longrightarrow> delta(x) = delta(y)"
  proof (insert assms, erule rtrancl.induct)
    show "(\<And> a::infrastructure.
       (\<forall>(z::infrastructure)(z'::infrastructure). (z \<rightarrow>\<^sub>n z') \<longrightarrow> (delta z = delta z')) \<Longrightarrow>
       (((a, a) \<in> {(x ::infrastructure, y :: infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*) \<longrightarrow>
       (delta a = delta a)))"
    by (rule impI, rule refl)
next fix a b c
  assume a0: "\<forall>(z::infrastructure) z'::infrastructure. z \<rightarrow>\<^sub>n z' \<longrightarrow> delta z = delta z'"
     and a1: "(a, b) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
     and a2: "(a, b) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
         delta a = delta b"
     and a3: "(b, c) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}"
     show "(a, c) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       delta a = delta c"
  proof -
    have a4: "delta b = delta c" using a0 a1 a2 a3 by simp
    show ?thesis using a0 a1 a2 a3 by simp
  qed
qed
show ?thesis 
  by (insert ind, insert assms(2), simp)
qed

lemma init_state_policy: "\<lbrakk> (x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<rbrakk> \<Longrightarrow> 
                          delta(x) = delta(y)"  
  by (rule init_state_policy0, rule delta_invariant)

lemma same_nodes0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> nodes(graphI z) = nodes(graphI z')"   
  by (clarify, erule state_transition_in.cases, 
       (simp add: move_graph_a_def get_graph_a_def put_graph_a_def eval_graph_a_def atI_def actors_graph_def nodes_def)+)

lemma same_nodes: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
                   \<Longrightarrow> nodes(graphI y) = nodes(graphI I)"  
  by (erule rtrancl_induct, rule refl, drule CollectD, simp, drule same_nodes0, simp)  

lemma same_actors0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> actors_graph(graphI z) = actors_graph(graphI z')"   
proof (clarify, erule state_transition_in.cases)
  show \<open>\<And>z z' G I a l I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (put_graph_a a l G) (delta I) \<Longrightarrow> actors_graph (graphI z) = actors_graph (graphI z')\<close>
    by (simp add: actors_graph_def nodes_def put_graph_a_def)
next show \<open>\<And>z z' G I a l c I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       c \<in> actors_graph G \<Longrightarrow>
       (a, None) \<in> requests G \<Longrightarrow>
       Actor c \<in> readers (dgra G a) \<or> Actor c = owner (dgra G a) \<Longrightarrow>
       enables I l (Actor c) eval \<Longrightarrow>
       I' = Infrastructure (eval_graph_a a l G) (delta I) \<Longrightarrow> actors_graph (graphI z) = actors_graph (graphI z')\<close>
    by (simp add: actors_graph_def eval_graph_a_def nodes_def)
next show \<open>\<And>z z' G I a l l' I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       l' \<in> nodes G \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l l' G) (delta I) \<Longrightarrow> actors_graph (graphI z) = actors_graph (graphI z')\<close>
    apply (simp add: actors_graph_def nodes_def move_graph_a_def atI_def, rule impI, rule equalityI)
    prefer 2
     apply blast
    apply (rule subsetI, simp)
    by metis
next show \<open>\<And>z z' G I a l I' m.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       enables I l (Actor a) get \<Longrightarrow>
       I' = Infrastructure (get_graph_a a l m G) (delta I) \<Longrightarrow> actors_graph (graphI z) = actors_graph (graphI z')\<close>
    by (simp add: actors_graph_def get_graph_a_def nodes_def)
qed

lemma same_actors: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> actors_graph(graphI I) = actors_graph(graphI y)"
proof (erule rtrancl_induct)
  show "actors_graph (graphI I) = actors_graph (graphI I)"
    by (rule refl)
next show "\<And>(y::infrastructure) z::infrastructure.
       (I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       actors_graph (graphI I) = actors_graph (graphI y) \<Longrightarrow>
       actors_graph (graphI I) = actors_graph (graphI z)"
    by (drule CollectD, simp, drule same_actors0, simp)  
qed

lemma actor_has_location[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> (\<forall> a \<in> actors_graph (graphI I). 
              (\<forall> l \<in> nodes (graphI I). (a  @\<^bsub>graphI I\<^esub> l) \<longrightarrow> (\<exists> l' \<in> nodes (graphI y). (a @\<^bsub> graphI y\<^esub> l'))))"
  using actors_graph_def atI_def same_actors by auto

lemma same_bb0[rule_format]: \<open>\<forall> z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow> bb (graphI z) = bb (graphI z')\<close>
proof (clarify, erule state_transition_in.cases)
  show \<open>\<And>z z' G I a l I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (put_graph_a a l G) (delta I) \<Longrightarrow> bb (graphI z) = bb (graphI z')\<close>
    by (simp add: put_graph_a_def)
next show \<open>\<And>z z' G I a l c I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       c \<in> actors_graph G \<Longrightarrow>
       (a, None) \<in> requests G \<Longrightarrow>
       Actor c \<in> readers (dgra G a) \<or> Actor c = owner (dgra G a) \<Longrightarrow>
       enables I l (Actor c) eval \<Longrightarrow>
       I' = Infrastructure (eval_graph_a a l G) (delta I) \<Longrightarrow> bb (graphI z) = bb (graphI z')\<close>
    by (simp add: eval_graph_a_def)
next show \<open>\<And>z z' G I a l l' I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       l' \<in> nodes G \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l l' G) (delta I) \<Longrightarrow> bb (graphI z) = bb (graphI z')\<close>
    using move_graph_a_def by force
next show \<open>\<And>z z' G I a l I' m.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       enables I l (Actor a) get \<Longrightarrow>
       I' = Infrastructure (get_graph_a a l m G) (delta I) \<Longrightarrow> bb (graphI z) = bb (graphI z') \<close>
    by (simp add: get_graph_a_def)
qed


lemma same_bb: \<open>(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
                   \<Longrightarrow> bb (graphI I) = bb (graphI y)\<close>
proof (erule rtrancl_induct)
  show \<open>bb (graphI I) = bb (graphI I)\<close> by (rule refl)
next show \<open>\<And>y z. (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow> bb (graphI I) = bb (graphI y) \<Longrightarrow> bb (graphI I) = bb (graphI z)\<close>
    by (simp add: same_bb0)
qed

end


