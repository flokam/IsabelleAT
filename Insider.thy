theory Insider
imports AT
begin
datatype action = get | move | eval |put
typedecl actor 
type_synonym identity = string
consts Actor :: "string => actor"
type_synonym policy = "((actor => bool) * action set)"

definition ID :: "[actor, string] \<Rightarrow> bool"
where "ID a s \<equiv> (a = Actor s)"

datatype location = Location nat
  datatype igraph = Lgraph "(location * location)set" "location \<Rightarrow> identity set"
                         "actor \<Rightarrow> (string set * string set)"  "location \<Rightarrow> string set"
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
primrec lgra :: "igraph \<Rightarrow> (location \<Rightarrow> string set)"
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
primrec lspace :: "[infrastructure, location ] \<Rightarrow> string set"
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
  where "isin G l s \<equiv> s \<in> (lgra G l)"
  
  
  
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
(*
primrec del :: "['a, 'a list] \<Rightarrow> 'a list"
where 
del_nil: "del a [] = []" |
del_cons: "del a (x#ls) = (if x = a then ls else x # (del a ls))"
*)

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
| put : "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; enables I l (Actor a) put;
        I' = Infrastructure 
                  (Lgraph (gra G)(agra G)(cgra G)
                          ((lgra G)(l := {z})))
                   (delta I)
         \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
  
definition state_transition_in_refl ("(_ \<rightarrow>\<^sub>n* _)" 50)
where "s \<rightarrow>\<^sub>n* s' \<equiv> ((s,s') \<in> {(x,y). state_transition_in x y}\<^sup>*)"
  
  
(* del related results not needed since we use sets here for credentials etc  
lemma del_del[rule_format]: "n \<in> set (del a S) \<longrightarrow> n \<in> set S"
  apply (induct_tac S)
  by auto
*)
(* Not true in the current formulation of del since copies are not 
   deleted. But changing that causes extra complxity also elsewhere 
   (see jonce) 
lemma del_del_elim[rule_format]: "n \<in> set (S) \<longrightarrow> n \<notin> set (del n S)" *)
    
(*    
lemma del_dec[rule_format]: "a \<in> set S \<longrightarrow> length (del a S) < length S"  
  apply (induct_tac S)
    by auto

lemma del_sort[rule_format]: "\<forall> n. (Suc n ::nat) \<le> length (l) \<longrightarrow> n \<le> length (del a (l))"   
  apply (induct_tac l)
   apply simp
  apply clarify
  apply (case_tac n)
   apply simp
    by simp
    
lemma del_jonce: "jonce a l \<longrightarrow> a \<notin> set (del a l)"
  apply (induct_tac l)
  by auto
    
lemma del_nodup[rule_format]: "nodup a l \<longrightarrow> a \<notin> set(del a l)"
  apply (induct_tac l)
  by auto
    
lemma nodup_up[rule_format]: "a \<in> set (del a l) \<longrightarrow> a \<in> set l"
  apply (induct_tac l)
  by auto
    
    lemma del_up [rule_format]: "a \<in> set (del aa l) \<longrightarrow> a \<in> set l"
   apply (induct_tac l)
  by auto

lemma nodup_notin[rule_format]:   "a \<notin> set list \<longrightarrow> nodup a list"
  apply (induct_tac list)
  by auto
    
    lemma nodup_down[rule_format]: "nodup a l \<longrightarrow> nodup a (del a l)"
      apply (induct_tac l)
       apply simp+
      apply (clarify)
    by (erule nodup_notin)

lemma del_notin_down[rule_format]: "a \<notin> set list \<longrightarrow> a \<notin> set (del aa list) "
  apply (induct_tac list)
  by auto

lemma del_not_a[rule_format]: " x \<noteq> a \<longrightarrow> x \<in> set l \<longrightarrow> x \<in> set (del a l)"
  apply (induct_tac l)
    by auto
      
lemma nodup_down_notin[rule_format]: "nodup a l \<longrightarrow> nodup a (del aa l)"
  apply (induct_tac l)
   apply simp+
    apply (rule conjI)
  apply (clarify)
   apply (erule nodup_notin)
  apply (rule impI)+
 by (erule del_notin_down)
*)
    
lemma move_graph_eq: "move_graph_a a l l g = g"  
  apply (simp add: move_graph_a_def)
  apply (case_tac g)
  by force
     
    
(* show that this infrastructure is a state as given in MC.thy *)
instantiation "infrastructure" :: state
begin
instance 
  by (rule MC.class.MC.state.of_class.intro)
    
(*
instance   "infrastructure" :: state
  by (rule MC.class.MC.state.of_class.intro)
*)    
end
end
  