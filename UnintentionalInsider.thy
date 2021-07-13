section "Insider Framework"
text \<open>In the Isabelle/HOL theory for Insiders, one expresses policies over
actions @{text \<open>get, move, eval\<close>}, and @{text \<open>put\<close>}.\<close>
subsection \<open>Actors and actions\<close>
text \<open>The theory Airinsider is an instance of the Insider framework for the case study
     of airplane insiders. Although the Isabelle Insider framework is a generic framework
     the actual semantics of the actions is specific to applications. Therefore we use here
     an "instance" of the framework in the form of a theory "Airinsider" but the main part of 
     definitions and declarations is the same.\<close>
theory UnintentionalInsider
  imports AT
begin
text \<open>An actor may be enabled to 
\begin{itemize}
\item @{text \<open>get\<close>} data or physical items, like keys,
\item @{text \<open>move\<close>} to a location,
\item @{text \<open>eval\<close>} a program,
\item @{text \<open>put\<close>} data at locations or physical items -- like airplanes --
``to the ground''.
\end{itemize}
The precise semantics of these actions is refined in the state transition 
rules for the concrete infrastructure.
The framework abstracts from concrete data -- actions have no parameters:\<close>
datatype action = get | move | eval | put

text \<open>The human component is the {\it Actor} which is represented by an abstract
type @{text \<open>actor\<close>} and a function @{text \<open>Actor\<close>}
that creates elements of that type from identities (of type @{text \<open>string\<close>}):

We use an abstract type declaration actor that can later be instantiated by a more
      concrete type.\<close>
typedecl actor 
type_synonym identity = string
consts Actor :: "identity \<Rightarrow> actor" 
text \<open>Note that it would seem more natural and simpler to just 
define @{text \<open>actor\<close>} as a datatype over identities with a constructor @{text \<open>Actor\<close>}
instead of a simple constant together with a type declaration like, for example,
in the Isabelle inductive approach to security protocol verification \cite{pau:97, pau:98}. 
This would, however, make the constructor @{text \<open>Actor\<close>} an injective function
by the underlying foundation of datatypes therefore excluding the fine
grained modelling that is at the core of the insider definition:
In fact, it defines the function @{text \<open>Actor\<close>} to be injective
for all except insiders and explicitly enables insiders to have
different roles by identifying @{text \<open>Actor\<close>} images.

Alternatives to the type declaration do not work.

@{text \<open>context

  fixes Abs Rep actor

  assumes td: "type_definition Abs Rep actor"

begin

definition Actor where "Actor = Abs"
\<close>}
...doesn't work as an alternative to the actor @{term \<open>typedecl\<close>} because 
in @{text \<open>type_definition\<close>} above the @{text \<open>actor\<close>} is a set not a type!
So can't be used for our purposes. 

Trying a locale instead for polymorphic type Actor is a suggested alternative 
\cite{mw:09}.

@{text 
\<open>locale ACT =
  fixes Actor :: "string \<Rightarrow> 'actor"
begin ...\<close>
}
That is a nice idea and works quite far but clashes with the generic
@{text \<open>state_transition\<close>} later (it's not possible to instantiate within a locale
and outside of it we cannot instantiate @{text \<open>'a infrastructure\<close>} to state (clearly 
an abstract thing as an instance is strange).\<close>

definition ID :: "[actor, string] \<Rightarrow> bool"
where "ID a s \<equiv> (a = Actor s)"

subsection \<open>Insider predicate\<close>
text \<open>The human actor's level is modelled in the Isabelle Insider framework by assigning
the individual actor's psychological disposition\footnote{Note that the determination of 
the psychological state of an actor is not done using the formal system. It is up to a 
psychologist to determine this. However, if for instance, an actor is classified as 
@{text \<open>disgruntled\<close>} then this may have an influence on what they are allowed to do according 
to a company policy and this can be formally described and reasoned about in Isabelle.} 
@{text \<open>actor_state\<close>} to each actor's identity.\<close>
datatype psy_states = happy | depressed | disgruntled | angry | stressed | suspicious
datatype motivations = financial | political | revenge | curious | competitive_advantage | power | 
                       peer_recognition | approval_hungry | zen

text \<open>The values used for the definition of the types
@{text \<open>motivations\<close>} and @{text \<open>psy_state\<close>}
are based on a taxonomy from psychological insider research \cite{nblgcww:14}.
The transition to become an insider is represented by a {\it Catalyst} that tips the insider 
over the edge so he acts as an insider formalized as a ``tipping point'' 
predicate.\<close>
datatype actor_state = Actor_state "psy_states" "motivations set"
primrec motivation :: "actor_state \<Rightarrow> motivations set" 
where "motivation  (Actor_state p m) =  m"
primrec psy_state :: "actor_state \<Rightarrow> psy_states" 
where "psy_state  (Actor_state p m) = p"

definition unaware :: "actor_state \<Rightarrow> bool"
  where "unaware a \<equiv> motivation a = {approval_hungry} \<and> happy = psy_state a"


definition tipping_point :: "actor_state \<Rightarrow> bool" where
  "tipping_point a \<equiv> ((motivation a \<noteq> {}) \<and> (motivation a \<noteq> {approval_hungry}) \<and> (happy \<noteq> psy_state a))"

text \<open>To embed the fact that the attacker is an insider, the actor can then
impersonate other actors. In the Isabelle Insider framework, the 
predicate @{text \<open>Insider\<close>} must be used as a {\it locale} assumption
to enable impersonation for the insider:
this assumption entails that an insider @{text \<open>Actor ''Eve''\<close>} can act like 
their alter ego, say @{text \<open>Actor ''Charly''\<close>} within the context of the locale.
This is realized by the predicate  @{text \<open>UasI\<close>}:
@{text \<open>UasI\<close>} and @{text \<open>UasI'\<close>} are the central predicates allowing to specify Insiders.
They define which identities can be mapped to the same role by the @{text \<open>Actor\<close>} function
(an impersonation predicate "@{text \<open>a\<close>} can act as @{text \<open>b\<close>}").
For all other identities, @{text \<open>Actor\<close>} is defined as injective on those identities.
The first one is stronger and allows substitution of the insider in any context; the second 
one is parameterized over a context predicate to describe this.\<close>
definition UasI ::  "[identity, identity] \<Rightarrow> bool " 
where "UasI a b \<equiv> (Actor a = Actor b) \<and> (\<forall> x y. x \<noteq> a \<and> y \<noteq> a \<and> Actor x = Actor y \<longrightarrow> x = y)"
definition UasI' ::  "[actor \<Rightarrow> bool, identity, identity] \<Rightarrow> bool " 
where "UasI' P a b \<equiv> P (Actor b) \<longrightarrow> P (Actor a)"

text \<open>Two versions of Insider predicate corresponding to @{text \<open>UasI\<close>} and @{text \<open>UasI'\<close>}
exist. Under the assumption that the tipping point has been reached for a person @{text \<open>a\<close>}
then @{text \<open>a\<close>} can impersonate all @{text \<open>b\<close>} (take all of @{text \<open>b\<close>}'s "roles") where
the @{text \<open>b\<close>}'s are specified by a given set of identities.\<close>
definition Insider :: "[identity, identity set, identity \<Rightarrow> actor_state] \<Rightarrow> bool" 
where "Insider a C as \<equiv> (tipping_point (as a) \<or> unaware (as a) \<longrightarrow> (\<forall> b\<in>C. UasI a b))"
definition Insider' :: "[actor \<Rightarrow> bool, identity, identity set, identity \<Rightarrow> actor_state] \<Rightarrow> bool" 
where "Insider' P a C as \<equiv> (tipping_point (as a) \<longrightarrow> (\<forall> b\<in>C. UasI' P a b \<and> inj_on Actor C))"
text \<open>The predicate @{text \<open>atI\<close>} -- mixfix syntax @{text \<open>@\<^bsub>G\<^esub>\<close>} -- expresses that an actor (identity) 
      is at a certain location in an igraph.\<close>


subsection \<open>Infrastructure graphs and policies\<close>
text\<open>Actors are contained in an infrastructure graph. An @{text \<open>igraph\<close>} contains
a set of location pairs representing the topology of the infrastructure
as a graph of nodes and a list of actor identities associated to each node 
(location) in the graph.
Also an @{text \<open>igraph\<close>} associates actors to a pair of string sets by
a pair-valued function whose first range component is a set describing
the credentials in the possession of an actor and the second component
is a set defining the roles the actor can take on. Finally, an  @{text \<open>igraph\<close>} 
assigns locations to a pair of a string that defines
the state of the component. 
Corresponding projection functions for each of these components of an 
@{text \<open>igraph\<close>} are provided; they are named @{text \<open>gra\<close>} for the actual set of pairs of
locations, @{text \<open>agra\<close>} for the actor map, @{text \<open>cgra\<close>} for the credentials,
and @{text \<open>lgra\<close>} for the state of a location and the data at that location.\<close>
datatype location = Location nat
text\<open>Distributed Label Model to introduce access control labels for privacy\<close>
type_synonym data = string

text\<open>Inspired by Myers DLM mode: first is the owner of a data item, second is the
     set of all actors that may access the data item.\<close>
type_synonym dlm = "actor * actor set"

datatype igraph = Lgraph "(location * location)set" "location \<Rightarrow> identity set"
                         "actor \<Rightarrow> (string set * string set)"  "actor \<Rightarrow> actor_state" 
                         "location \<Rightarrow> (dlm * data)set"
text \<open>Atomic policies of type @{text \<open>apolicy\<close>}
describe prerequisites for actions to be granted to actors given by
pairs of predicates (conditions) and sets of (enabled) actions:\<close>
type_synonym  apolicy = "((actor \<Rightarrow> bool) * action set)"

datatype infrastructure = 
         Infrastructure "igraph" 
                        "[igraph, location] \<Rightarrow> apolicy set" 
                       
primrec loc :: "location \<Rightarrow> nat"
where  "loc(Location n) = n"
primrec gra :: "igraph \<Rightarrow> (location * location)set"
where  "gra(Lgraph g a c p l) = g"
primrec agra :: "igraph \<Rightarrow> (location \<Rightarrow> identity set)"
where  "agra(Lgraph g a c p l) = a"
primrec cgra :: "igraph \<Rightarrow> (actor \<Rightarrow> string set * string set)"
where  "cgra(Lgraph g a c p l) = c"
primrec pgra :: "igraph \<Rightarrow> (actor \<Rightarrow> actor_state)"
where  "pgra(Lgraph g a c p l) = p"
primrec lgra :: "igraph \<Rightarrow> (location \<Rightarrow> (dlm * data)set)"
where  "lgra(Lgraph g a c p l) = l"

definition nodes :: "igraph \<Rightarrow> location set" 
where "nodes g == { x. (? y. ((x,y): gra g) | ((y,x): gra g))}"
definition actors_graph :: "igraph \<Rightarrow> identity set"  
where  "actors_graph g == {x. ? y. y : nodes g \<and> x \<in> agra g y}"
primrec graphI :: "infrastructure \<Rightarrow> igraph"
where "graphI (Infrastructure g d) = g"
primrec delta :: "[infrastructure, igraph, location] \<Rightarrow> apolicy set"
where "delta (Infrastructure g d) = d"
primrec tspace :: "[infrastructure, actor ] \<Rightarrow> string set * string set"
  where "tspace (Infrastructure g d) = cgra g"
primrec lspace :: "[infrastructure, location ] \<Rightarrow> (dlm * data)set"
where "lspace (Infrastructure g d) = lgra g"
definition credentials :: "string set * string set \<Rightarrow> string set"
  where  "credentials lxl \<equiv> (fst lxl)"
definition has :: "[igraph, actor * string] \<Rightarrow> bool"
  where "has G ac \<equiv> snd ac \<in> credentials(cgra G (fst ac))"
definition roles :: "string set * string set \<Rightarrow> string set"
  where  "roles lxl \<equiv> snd lxl"
definition role :: "[igraph, actor * string] \<Rightarrow> bool"
  where "role G ac \<equiv> snd ac \<in> roles(cgra G (fst ac))"
definition psy_state' :: "[igraph, actor] \<Rightarrow> psy_states"
  where "psy_state' G a \<equiv> psy_state (pgra G a)"
definition motivation' :: "[igraph, actor] \<Rightarrow> motivations set"
  where "motivation' G a \<equiv> motivation (pgra G a)"

(*
definition isin :: "[igraph,location, string] \<Rightarrow> bool"
  where "isin G l s \<equiv> s \<in> set(lgra G l)"
*)

definition atI :: "[identity, igraph, location] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> (agra G l)"
text \<open>The enables predicate is the central definition of the behaviour as given by a policy
that specifies what actions are allowed in a certain location for what actors.
Policies specify the expected behaviour of actors of an infrastructure. 
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
text \<open>For example, the @{text \<open>apolicy\<close>} pair @{text \<open>(\<lambda> x. True, {move})\<close>}
specifies that all actors are enabled to perform action @{text \<open>move\<close>}.\<close>

text \<open>The behaviour is the good behaviour, i.e. everything allowed by the policy of 
Infrastructure @{text \<open>I\<close>}.\<close>
definition behaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "behaviour I \<equiv> {(t,a,a'). enables I t a a'}"

text \<open>The misbehaviour is the complement of behaviour of an Infrastructure @{text \<open>I\<close>}.\<close>
definition misbehaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
  where "misbehaviour I \<equiv> -(behaviour I)"


text \<open>We prove some basic lemmas for the predicate @{text \<open>enable\<close>}.\<close>
lemma not_enableI: "(\<forall> (p,e) \<in> delta I (graphI I) l. (\<not>(h : e) | (\<not>(p(a))))) 
                     \<Longrightarrow> \<not>(enables I l a h)"
  by (simp add: enables_def, blast)

lemma not_enableI2: "\<lbrakk>\<And> p e. (p,e) \<in> delta I (graphI I) l \<Longrightarrow>
                 (\<not>(t : e) |  (\<not>(p(a)))) \<rbrakk> \<Longrightarrow> \<not>(enables I l a t)"
 by (rule not_enableI, rule ballI, auto)

lemma not_enableE: "\<lbrakk> \<not>(enables I l a t); (p,e) \<in> delta I (graphI I) l \<rbrakk>
                 \<Longrightarrow> (\<not>(t : e) |  (\<not>(p(a))))"
  by (simp add: enables_def, rule impI, force)

lemma not_enableE2: "\<lbrakk> \<not>(enables I l a t); (p,e) \<in> delta I (graphI I) l;
                     t : e \<rbrakk> \<Longrightarrow> (\<not>(p(a)))"
  by (simp add: enables_def, force)

subsection "State transition on infrastructures"
text \<open>The state transition defines how actors may act on infrastructures through actions
    within the boundaries of the policy. It is given as an inductive definition over the 
    states which are infrastructures.  This state transition relation is dependent on actions but also on
    enabledness and the current state of the infrastructure.

    First we introduce some auxiliary functions dealing
    with repetitions in lists and actors moving in an @{text \<open>igraph\<close>} and some 
    constructions to deal with lists of actors in locations for the semantics of action 
    @{text \<open>move\<close>}.\<close>
primrec del :: "['a, 'a list] \<Rightarrow> 'a list"
where 
del_nil: "del a [] = []" |
del_cons: "del a (x#ls) = (if x = a then ls else x # (del a ls))"

primrec jonce :: "['a, 'a list] \<Rightarrow> bool"
where
jonce_nil: "jonce a [] = False" |
jonce_cons: "jonce a (x#ls) = (if x = a then (a \<notin> (set ls)) else jonce a ls)"

primrec nodup :: "['a, 'a list] \<Rightarrow> bool"
  where 
    nodup_nil: "nodup a [] = True" |
    nodup_step: "nodup a (x # ls) = (if x = a then (a \<notin> (set ls)) else nodup a ls)"

definition move_graph_a :: "[identity, location, location, igraph] \<Rightarrow> igraph"
where "move_graph_a n l l' g \<equiv> Lgraph (gra g) 
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then 
                     ((agra g)(l := (agra g l) - {n}))(l' := (insert n (agra g l')))
                     else (agra g))(cgra g)(pgra  g)(lgra g)"

text \<open>State transition relation over infrastructures (the states) defining the 
   semantics of actions in systems with humans and potentially insiders.\<close>
inductive state_transition_in :: "[infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
  move: "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          (a) \<in> actors_graph(graphI I); enables I l' (Actor a) move;
         I' = Infrastructure (move_graph_a a l l' (graphI I))(delta I) \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 
| get_data : "G = graphI I \<Longrightarrow> h @\<^bsub>G\<^esub> l \<Longrightarrow>  l \<in> nodes G \<Longrightarrow> l' \<in> nodes G \<Longrightarrow> 
        enables I l' (Actor h) get \<Longrightarrow> unaware (pgra G (Actor h)) \<Longrightarrow>
       ((Actor h', hs), n) \<in> lgra G l' \<Longrightarrow> Actor h \<in> hs \<or> h = h' \<Longrightarrow> 
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(pgra G)
                   ((lgra G)(l := (lgra G l)  \<union> {((Actor h', hs), n)})))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| process : "G = graphI I \<Longrightarrow> h @\<^bsub>G\<^esub> l \<Longrightarrow> l \<in> nodes G \<Longrightarrow> 
        enables I l (Actor h) eval \<Longrightarrow> unaware (pgra G (Actor h)) \<Longrightarrow>
       ((Actor h', hs), n) \<in> lgra G l \<Longrightarrow> Actor h \<in> hs \<or> h = h' \<Longrightarrow>
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(pgra G)
                   ((lgra G)(l := ((lgra G l)  - {(y, x). x = n}
                    \<union> {f ((Actor h', hs), n)}))))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"  
| put : "G = graphI I \<Longrightarrow> h @\<^bsub>G\<^esub> l \<Longrightarrow> l \<in> nodes G \<Longrightarrow> 
        enables I l (Actor h) put \<Longrightarrow>
        I' = Infrastructure 
                  (Lgraph (gra G)(agra G)(cgra G)(pgra G)
                          ((lgra G)(l := (lgra G l) \<union> {((Actor h, hs), n)})))
                   (delta I)
          \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
  
text \<open>Note that the type infrastructure can now be instantiated to the axiomatic type class 
      @{text\<open>state\<close>} which enables the use of the underlying Kripke structures and CTL.
      We need to show that this infrastructure is a state as given in MC.thy\<close>
instantiation "infrastructure" :: state
begin
definition 
   state_transition_infra_def: "(i \<rightarrow>\<^sub>i i') =  (i \<rightarrow>\<^sub>n (i' :: infrastructure))"

instance
  by (rule MC.class.MC.state.of_class.intro)

definition state_transition_in_refl ("(_ \<rightarrow>\<^sub>n* _)" 50)
where "s \<rightarrow>\<^sub>n* s' \<equiv> ((s,s') \<in> {(x,y). state_transition_in x y}\<^sup>*)"

end
end