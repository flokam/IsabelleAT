theory Infrastructure
imports AT "/Applications/Isabelle2016-1.app/Isabelle/src/HOL/Hoare/Hoare_Logic"
begin
datatype action = get | move | eval |put
typedecl actor 
type_synonym identity = string
consts Actor :: "string => actor"
type_synonym policy = "((actor => bool) * action set)"

definition ID :: "[actor, string] \<Rightarrow> bool"
where "ID a s \<equiv> (a = Actor s)"

(* a simple definition of data and instantiating 
the generic types of the Hoare logic to pairs of owner and data as 
basic data type for specification. This enables the unique marking
(module insider impersonation) of data within the system. 
The manipulation of the data (using simple while language) can thus 
be modelled but additionally taking the ownership into account. We use 
eval below and anchor the access control in restricing base functions
for the Basic com type *)
type_synonym data = nat  
  (* Inspired by Myers DLM mode: first is the owner of a data item, second is the
     set of all actors that may access the data item *)
type_synonym dlm = "actor * actor set"
  (* the following type constructors are from Hoare_logic:
     bexp and assn are just synonyms for set, and
     com is a simple datatype repesenting while command language
     over some Basic 'a \<Rightarrow> 'a functions, while 'a sem is
     just the type of relations 'a \<Rightarrow> 'a \<Rightarrow> bool representing relational
     semantics *)
type_synonym acond = "(dlm * data) bexp"
type_synonym aassn = "(dlm * data) assn"
type_synonym acom = "(dlm * data) com"
type_synonym asem = "(dlm * data) sem"
  
datatype location = Location nat
  datatype igraph = Lgraph "(location * location)set" "location \<Rightarrow> identity set"
                         "actor \<Rightarrow> (string set * string set)"  "location \<Rightarrow> string * acond"
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
primrec lgra :: "igraph \<Rightarrow> (location \<Rightarrow> string * acond)"
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
primrec lspace :: "[infrastructure, location ] \<Rightarrow> string * acond"
where "lspace (Infrastructure g d) = lgra g"

definition credentials :: "string set * string set \<Rightarrow> string set"
  where  "credentials lxl \<equiv> (fst lxl)"
definition has :: "[igraph, actor * string] \<Rightarrow> bool"
  where "has G ac \<equiv> snd ac \<in> credentials(cgra G (fst ac))"
definition roles :: "string set * string set \<Rightarrow> string set"
  where  "roles lxl \<equiv> (snd lxl)"
definition role :: "[igraph, actor * string] \<Rightarrow> bool"
  where "role G ac \<equiv> snd ac \<in> roles(cgra G (fst ac))"

definition isin :: "[igraph,location, string] \<Rightarrow> bool" 
  where "isin G l s \<equiv> s = fst (lgra G l)"

definition owner :: "dlm * data \<Rightarrow> actor" where "owner d \<equiv> fst(fst d)"
    
definition owns :: "[igraph, location, actor, dlm * data] \<Rightarrow> bool"    
  where "owns G l a d \<equiv> owner d = a"
    
    
(*    
definition has_access :: "[igraph, location, actor, data] \<Rightarrow> bool"    
  where "has_access G l a d \<equiv> (\<exists> as a'. ((a',as),d) \<in> snd(lgra G l) \<and> a \<in> as)"
*)
definition readers :: "dlm * data \<Rightarrow> actor set"
  where "readers d \<equiv> snd (fst d)"

definition has_access :: "[igraph, location, actor, dlm * data] \<Rightarrow> bool"    
where "has_access G l a d \<equiv> owns G l a d \<or> a \<in> readers d"
  
definition actor_can_delete ::   "[infrastructure, actor, location] \<Rightarrow> bool"
where actor_can_delete_def: "actor_can_delete I h l \<equiv>  
                   (\<forall> as n. ((h, as), n) \<notin> (snd (lgra (graphI I) l)))"
    
    
(* type of functions that preserves the security labeling *)    
typedef label_fun = "{f :: dlm * data \<Rightarrow> dlm * data. 
                        \<forall> x:: dlm * data. fst x = fst (f x)}"  
  apply auto
  apply (rule_tac x = id in exI)
  by simp
    
definition secure_process :: "label_fun \<Rightarrow> dlm * data \<Rightarrow> dlm * data" ("_ \<Updown> _" 50)
  where "f  \<Updown> d \<equiv> (Rep_label_fun f) d" 
    
definition valid_proc :: "acond \<Rightarrow> label_fun \<Rightarrow> acond \<Rightarrow> bool"    
  where "valid_proc a f b \<equiv> Valid a (Basic (Rep_label_fun f)) b"
    
datatype psy_states = happy | depressed | disgruntled | angry | stressed
datatype motivations = financial | political | revenge | curious | competitive_advantage | power | peer_recognition

datatype actor_state = Actor_state "psy_states" "motivations set"
primrec motivation :: "actor_state \<Rightarrow> motivations set" 
where "motivation  (Actor_state p m) =  m"
primrec psy_state :: "actor_state \<Rightarrow> psy_states" 
where "psy_state  (Actor_state p m) = p"


definition tipping_point :: "actor_state \<Rightarrow> bool" where
  "tipping_point a \<equiv> ((motivation a \<noteq> {}) \<and> (happy \<noteq> psy_state a))"

(* idea:: predicate to flag that an actor is isolated *)
consts Isolation :: "[actor_state, (identity * identity) set ] \<Rightarrow> bool"


(* use above to redefine infrastructure -- adapt policies in nodes
   so that layed off workers cannot access any more *)
definition lay_off :: "[infrastructure,actor set] \<Rightarrow> infrastructure"
where "lay_off G A \<equiv> G"

(* idea: social graph is derived from activities in infrastructure.
   Since actors are nodes in the infrastructure graph, we need to 
   have a second graph only on actors reflecting their interaction. *)
consts social_graph :: "(identity * identity) set"
(* This social graph is a parameter to the theory. It depends on
   actual measured activities. We will use it to derive meta-theorems. *)

definition UasI ::  "[identity, identity] \<Rightarrow> bool " 
where "UasI a b \<equiv> (Actor a = Actor b) \<and> (\<forall> x y. x \<noteq> a \<and> y \<noteq> a \<and> Actor x = Actor y \<longrightarrow> x = y)"

definition UasI' ::  "[actor => bool, identity, identity] \<Rightarrow> bool " 
where "UasI' P a b \<equiv> P (Actor b) \<longrightarrow> P (Actor a)"

(* derive theorems about UasI being a equivalence relation *)

consts astate :: "identity \<Rightarrow> actor_state"

definition Insider :: "[identity, identity set] \<Rightarrow> bool" 
where "Insider a C \<equiv> (tipping_point (astate a) \<longrightarrow> (\<forall> b\<in>C. UasI a b))"


definition Insider' :: "[actor \<Rightarrow> bool, identity, identity set] \<Rightarrow> bool" 
where "Insider' P a C \<equiv> (tipping_point (astate a) \<longrightarrow> (\<forall> b\<in>C. UasI' P a b \<and> inj_on Actor C))"

definition atI :: "[identity, igraph, location] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> (agra G l)"

definition enables :: "[infrastructure, location, actor, action] \<Rightarrow> bool"
where
"enables I l a a' \<equiv>  (\<exists> (p,e) \<in> delta I (graphI I) l. a' \<in> e \<and> p a)"


(* behaviour is the good behaviour, i.e. everything allowed by policy *)
definition behaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "behaviour I \<equiv> {(t,a,a'). enables I t a a'}"

(* Most general: misbehaviour is the complement of behaviour *)
definition misbehaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "misbehaviour I \<equiv> -(behaviour I)"

(* state transition on infrastructures *)
declare [[show_types]]


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
                     else (agra g))(cgra g)(lgra g)"

inductive state_transition_in :: "[infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
  move: "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          (a) \<in> actors_graph(graphI I); enables I l' (Actor a) move;
         I' = Infrastructure (move_graph_a a l l' (graphI I))(delta I) \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 
| get : "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; a' @\<^bsub>G\<^esub> l; has G (Actor a, z);
        enables I l (Actor a) get;
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)
                           ((cgra G)(Actor a' := 
                                (insert z (fst(cgra G (Actor a'))), snd(cgra G (Actor a')))))
                           (lgra G))
                   (delta I)
         \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| get_data : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow>
        enables I l' (Actor a) get \<Longrightarrow> 
(* naive version omits the following two checks of the DLM labels *)
       ((Actor a', as), n) \<in> snd (lgra G l') \<Longrightarrow> Actor a \<in> as \<Longrightarrow> 
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)
                   ((lgra G)(l := (fst (lgra G l), 
                                   snd (lgra G l)  \<union> {((Actor a', as), n)}))))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| process : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow>
        enables I l (Actor a) eval \<Longrightarrow> 
       ((Actor a', as), n) \<in> snd (lgra G l) \<Longrightarrow> Actor a \<in> as \<Longrightarrow>
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)
                   ((lgra G)(l := (fst (lgra G l), 
                    snd (lgra G l)  - {((Actor a', as), n)}
                    \<union> {(f :: label_fun) \<Updown> ((Actor a', as), n)}))))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"  
| del_data : "G = graphI I \<Longrightarrow> a \<in> actors G \<Longrightarrow> l \<in> nodes G \<Longrightarrow>
       ((Actor a, as), n) \<in> snd (lgra G l) \<Longrightarrow> 
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)
                   ((lgra G)(l := (fst (lgra G l), snd (lgra G l) - {((Actor a, as), n)}))))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| put : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow> enables I l (Actor a) put \<Longrightarrow>
        I' = Infrastructure 
                  (Lgraph (gra G)(agra G)(cgra G)
                          ((lgra G)(l := (s, snd (lgra G l) \<union> {((Actor a, as), n)}))))
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

(* instantiation should give that for free -- this is a bug
  in the Isabelle classes implementation version 2016-1 to be fixed in 2018 *)    
lemma state_trans_inst_eq : "((s :: infrastructure) \<rightarrow>\<^sub>i s') = (s \<rightarrow>\<^sub>n s')"
  by (rule state_transition_infra_def)
(*  apply (unfold state_transition_in.simps)
  apply (rule iffI)
   apply auto
  sorry  
*)  
end
  
    
lemma move_graph_eq: "move_graph_a a l l g = g"  
  apply (simp add: move_graph_a_def)
  apply (case_tac g)
  by force
     
   
end

  