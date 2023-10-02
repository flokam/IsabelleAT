theory RRLoopThree
(* Third instance of the RRLoop: here we add the type label_fun
   to the model to avoid the attack that Eve can change labels using eval *)
  imports hcKripkeTwo
begin
(*
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


(* type of functions that preserves the security labeling *)    
typedef label_fun = "{f :: dlm * data \<Rightarrow> dlm * data. 
                        \<forall> x:: dlm * data. fst x = fst (f x)}"  
proof (auto)
  show "\<exists>x::(actor \<times> actor set) \<times> string \<Rightarrow> (actor \<times> actor set) \<times> string.
       \<forall>(a::actor) (b::actor set) ba::string. (a, b) = fst (x ((a, b), ba))"
  by (rule_tac x = id in exI, simp)
qed

definition secure_process :: "label_fun \<Rightarrow> dlm * data \<Rightarrow> dlm * data" ("_ \<Updown> _" 50)
  where "f  \<Updown> d \<equiv> (Rep_label_fun f) d" 

(* from the earlier use of Hoare triples - now obsolete 
definition valid_proc :: "acond \<Rightarrow> label_fun \<Rightarrow> acond \<Rightarrow> bool"    
  where "valid_proc a f b \<equiv> Valid a (Basic (Rep_label_fun f)) b"
*)

lemma move_graph_eq: "move_graph_a a l l g = g"  
proof (simp add: move_graph_a_def, case_tac g, force)
qed

inductive state_transition_in :: "[infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
  move: "\<lbrakk> G = graphI I; h @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          h \<in> actors_graph(graphI I); enables I l' (Actor h) move;
         I' = Infrastructure (move_graph_a h l l' (graphI I))(delta I) \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 
| get_data : "G = graphI I \<Longrightarrow> h @\<^bsub>G\<^esub> l \<Longrightarrow> l \<in> nodes G \<Longrightarrow> l' \<in> nodes G \<Longrightarrow> 
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
                    \<union> {(f :: label_fun) \<Updown> ((Actor h', hs), n)}))))
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


definition ref_map :: "[RRLoopThree.infrastructure, 
                        [RRLoopTwo.igraph, location] \<Rightarrow> policy set]
                        \<Rightarrow> RRLoopTwo.infrastructure"
  where "ref_map I lp = RRLoopTwo.Infrastructure 
                                 (RRLoopTwo.Lgraph
                                        (RRLoopThree.gra (RRLoopThree.graphI I))(RRLoopThree.agra (graphI I))
                                        (RRLoopThree.cgra (graphI I))
                                        (RRLoopThree.lgra (graphI I)))
                                 lp"
                   
lemma delta_invariant: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  delta(z) = delta(z')"    
  apply clarify
  apply (erule state_transition_in.cases)
  by simp+

(* locations invariants *)
 lemma same_nodes0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> nodes(graphI z) = nodes(graphI z')"   
    apply clarify
  apply (erule RRLoopThree.state_transition_in.cases)
  by (simp add: move_graph_a_def atI_def actors_graph_def nodes_def)+

lemma same_nodes: "(c, s) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
\<Longrightarrow> RRLoopThree.nodes (graphI c) = RRLoopThree.nodes (graphI s)"
  apply (erule rtrancl_induct)
   apply (rule refl)
  apply (drule CollectD)
    apply simp
    apply (drule same_nodes0)
  by simp  

lemma init_state_policy0: "\<lbrakk> \<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  delta(z) = delta(z'); 
                          (x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<rbrakk> \<Longrightarrow> 
                          delta(x) = delta(y)"  
  apply (rule mp)
  prefer 2
   apply (rotate_tac 1)
    apply assumption
  thm rtrancl_induct
  apply (erule rtrancl_induct)  
    apply (rule impI)
   apply (rule refl)
    apply (subgoal_tac "delta y = delta z")
   apply (erule impE)
    apply assumption
    apply (rule impI)
   apply (rule trans)
    apply assumption+
  apply (drule_tac x = y in spec)
  apply (drule_tac x = z in spec)
    apply (rotate_tac -1)
  apply (erule impE)
    apply simp
by assumption
 
lemma init_state_policy: "\<lbrakk> (x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<rbrakk> \<Longrightarrow> 
                          delta(x) = delta(y)"  
  apply (rule init_state_policy0)
    apply (rule delta_invariant)
  by assumption

lemma finite_nodes: \<open>(hc_scenarioR, s) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
\<Longrightarrow> finite(nodes (graphI hc_scenarioR)) \<Longrightarrow> finite(nodes (graphI s))\<close>
  by (simp add: same_nodes)
  



lemma same_actors0[rule_format]: "\<forall> z z'.  z \<rightarrow>\<^sub>n z' \<longrightarrow> actors_graph (graphI z) = actors_graph (graphI z')"
proof (clarify, erule state_transition_in.cases)
  show \<open>\<And>(z::RRLoopThree.infrastructure) (z'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (l'::location) I'::RRLoopThree.infrastructure.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = RRLoopThree.graphI I \<Longrightarrow>
       h @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> RRLoopThree.nodes G \<Longrightarrow>
       l' \<in> RRLoopThree.nodes G \<Longrightarrow>
       h \<in> RRLoopThree.actors_graph (RRLoopThree.graphI I) \<Longrightarrow>
       RRLoopThree.enables I l' (Actor h) move \<Longrightarrow>
       I' =
       RRLoopThree.infrastructure.Infrastructure (RRLoopThree.move_graph_a h l l' (RRLoopThree.graphI I))
        (RRLoopThree.delta I) \<Longrightarrow>
       RRLoopThree.actors_graph (RRLoopThree.graphI z) = RRLoopThree.actors_graph (RRLoopThree.graphI z')\<close>
    apply (simp add: actors_graph_def)
    apply (rule equalityI)
     apply (rule subsetI)
     apply (rule CollectI)
     apply (drule CollectD)
     apply (erule exE, erule conjE)+
    apply (simp add: move_graph_a_def)
     apply (smt (z3) RRLoopThree.gra.simps RRLoopThree.nodes_def mem_Collect_eq)
    by (smt (verit, ccfv_threshold) DiffE RRLoopThree.actors_graph_def RRLoopThree.agra.simps RRLoopThree.graphI.simps RRLoopThree.move_graph_a_def RRLoopThree.state_transition_in.move fun_upd_other fun_upd_same insert_iff mem_Collect_eq same_nodes0 subsetI)
  next show \<open>\<And>(z::RRLoopThree.infrastructure) (z'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (l'::location) (h'::char list) (hs::actor set)
       (n::char list) I'::RRLoopThree.infrastructure.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = RRLoopThree.graphI I \<Longrightarrow>
       h @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> RRLoopThree.nodes G \<Longrightarrow>
       l' \<in> RRLoopThree.nodes G \<Longrightarrow>
       RRLoopThree.enables I l (Actor h) get \<Longrightarrow>
       ((Actor h', hs), n) \<in> RRLoopThree.lgra G l' \<Longrightarrow>
       Actor h \<in> hs \<or> h = h' \<Longrightarrow>
       I' =
       RRLoopThree.infrastructure.Infrastructure
        (RRLoopThree.igraph.Lgraph (RRLoopThree.gra G) (RRLoopThree.agra G) (RRLoopThree.cgra G)
          ((RRLoopThree.lgra G)(l := RRLoopThree.lgra G l \<union> {((Actor h', hs), n)})))
        (RRLoopThree.delta I) \<Longrightarrow>
       RRLoopThree.actors_graph (RRLoopThree.graphI z) = RRLoopThree.actors_graph (RRLoopThree.graphI z')\<close>
      by (smt (z3) Collect_cong RRLoopThree.actors_graph_def RRLoopThree.agra.simps RRLoopThree.graphI.simps RRLoopThree.state_transition_in.intros(2) same_nodes0)
  next show \<open>\<And>(z::RRLoopThree.infrastructure) (z'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (h'::char list) (hs::actor set) (n::char list)
       (I'::RRLoopThree.infrastructure) f::label_fun.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = RRLoopThree.graphI I \<Longrightarrow>
       h @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> RRLoopThree.nodes G \<Longrightarrow>
       RRLoopThree.enables I l (Actor h) eval \<Longrightarrow>
       ((Actor h', hs), n) \<in> RRLoopThree.lgra G l \<Longrightarrow>
       Actor h \<in> hs \<or> h = h' \<Longrightarrow>
       I' =
       RRLoopThree.infrastructure.Infrastructure
        (RRLoopThree.igraph.Lgraph (RRLoopThree.gra G) (RRLoopThree.agra G) (RRLoopThree.cgra G)
          ((RRLoopThree.lgra G)
           (l := RRLoopThree.lgra G l - {(y::actor \<times> actor set, x::char list). x = n} \<union> {f \<Updown> ((Actor h', hs), n)})))
        (RRLoopThree.delta I) \<Longrightarrow>
       RRLoopThree.actors_graph (RRLoopThree.graphI z) = RRLoopThree.actors_graph (RRLoopThree.graphI z')\<close>
      by (smt (z3) Collect_cong RRLoopThree.actors_graph_def RRLoopThree.agra.simps RRLoopThree.graphI.simps RRLoopThree.state_transition_in.process case_prod_beta' same_nodes0)
  next show \<open>\<And>(z::RRLoopThree.infrastructure) (z'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (hs::actor set) (n::char list)
       I'::RRLoopThree.infrastructure.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = RRLoopThree.graphI I \<Longrightarrow>
       h \<in> RRLoopThree.actors_graph G \<Longrightarrow>
       l \<in> RRLoopThree.nodes G \<Longrightarrow>
       ((Actor h, hs), n) \<in> RRLoopThree.lgra G l \<Longrightarrow>
       I' =
       RRLoopThree.infrastructure.Infrastructure
        (RRLoopThree.igraph.Lgraph (RRLoopThree.gra G) (RRLoopThree.agra G) (RRLoopThree.cgra G)
          ((RRLoopThree.lgra G)(l := RRLoopThree.lgra G l - {(y::actor \<times> actor set, x::char list). x = n})))
        (RRLoopThree.delta I) \<Longrightarrow>
       RRLoopThree.actors_graph (RRLoopThree.graphI z) = RRLoopThree.actors_graph (RRLoopThree.graphI z')\<close>
        by (smt (verit, best) Collect_cong RRLoopThree.actors_graph_def RRLoopThree.agra.simps RRLoopThree.graphI.simps RRLoopThree.state_transition_in.del_data same_nodes0)
    next show \<open>\<And>(z::RRLoopThree.infrastructure) (z'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (I'::RRLoopThree.infrastructure) (hs::actor set)
       n::char list.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = RRLoopThree.graphI I \<Longrightarrow>
       h @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> RRLoopThree.nodes G \<Longrightarrow>
       RRLoopThree.enables I l (Actor h) put \<Longrightarrow>
       I' =
       RRLoopThree.infrastructure.Infrastructure
        (RRLoopThree.igraph.Lgraph (RRLoopThree.gra G) (RRLoopThree.agra G) (RRLoopThree.cgra G)
          ((RRLoopThree.lgra G)(l := RRLoopThree.lgra G l \<union> {((Actor h, hs), n)})))
        (RRLoopThree.delta I) \<Longrightarrow>
       RRLoopThree.actors_graph (RRLoopThree.graphI z) = RRLoopThree.actors_graph (RRLoopThree.graphI z')\<close>
        by (smt (verit, del_insts) Collect_cong RRLoopThree.actors_graph_def RRLoopThree.agra.simps RRLoopThree.graphI.simps RRLoopThree.state_transition_in.put same_nodes0)
    qed

lemma same_actors: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> actors_graph(graphI I) = actors_graph(graphI y)"
proof (erule rtrancl_induct)
  show \<open>RRLoopThree.actors_graph (RRLoopThree.graphI I) = RRLoopThree.actors_graph (RRLoopThree.graphI I)\<close>
    by simp
next show \<open>\<And>(y::RRLoopThree.infrastructure) z::RRLoopThree.infrastructure.
       (I, y) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       RRLoopThree.actors_graph (RRLoopThree.graphI I) = RRLoopThree.actors_graph (RRLoopThree.graphI y) \<Longrightarrow>
       RRLoopThree.actors_graph (RRLoopThree.graphI I) = RRLoopThree.actors_graph (RRLoopThree.graphI z)\<close>
    by (simp add: same_actors0)
qed

lemma init_data_policy: "\<lbrakk> (x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<rbrakk> \<Longrightarrow> 
            (\<forall> (l :: location). (\<forall> yx \<in> (lgra (graphI x) l).
                       (\<exists> h \<in> actors_graph (graphI x). (fst (fst yx) = Actor h))))
        \<longrightarrow> (\<forall> (l :: location). (\<forall> yx \<in> (lgra (graphI y) l).
                       (\<exists> h \<in> actors_graph (graphI y). (fst (fst yx) = Actor h))))"  
    apply (erule rtrancl_induct)
   apply blast  
  apply (rule impI)
  apply (frule mp)
  apply (assumption)
  apply clarify
  apply (erule state_transition_in.cases)
      apply (drule_tac x = l in spec)
  apply (drule_tac x = \<open>((a, b), ba)\<close> in bspec)
  apply (simp add: move_graph_a_def actors_graph_def)
  oops

thm finite_induct
thm rtrancl_induct
lemma del_data_set_finite: \<open>finite L \<Longrightarrow>
  L \<subseteq> (nodes (graphI I)) \<Longrightarrow> 
      (\<forall> l' \<in> L. (lgra (graphI I) l'  - {(y, x). x = n } = (lgra (graphI I) l'))) \<longrightarrow>
        (\<forall> l \<in> (nodes (graphI I)). l \<notin> L \<longrightarrow> (\<forall> h \<in> actors_graph (graphI I). 
       ((Actor h, hs), n) \<in> lgra (graphI I) l \<longrightarrow>
           (I  \<rightarrow>\<^sub>n (Infrastructure 
                   (Lgraph (gra (graphI I))(agra (graphI I))(cgra (graphI I))
                   ((lgra (graphI I))(l := (lgra (graphI I) l) - {(y, x). x = n })))
                   (delta I)))))\<close>
  apply (erule finite_induct)
  apply (metis RRLoopThree.state_transition_in.del_data)
  by simp

text\<open>Say what you want\<close>
lemma del_data_set: \<open>finite (nodes (graphI I)) \<Longrightarrow>
         (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<longrightarrow> 
            (\<forall> l \<in> (nodes (graphI I')). (lgra (graphI I') l  - {(y, x). x = n } = (lgra (graphI I') l))))\<close>
  apply (drule del_data_set_finite, rule subset_refl)

  apply (rule exI, rule impI, unfold state_transition_in_refl_def)
  apply (erule rtrancl_induct)
  oops

(* Difference between  ((lgra G)(l := (lgra G l) - {(y, x). x = n }))) and  ((lgra G) l - {(y, x). x = n }) *)
lemma f_update_eq: \<open>((f :: 'a \<Rightarrow> 'b set)(l := (f l) - S)) l = (f l - S)\<close>
  by (rule fun_upd_same)

(* Invariant about the owner labels being in the actors graph *)
(* Note, that interestingly here we need to add inj Actor which assumes that there are no insiders *)
lemma owner_actors_inv: \<open>inj Actor \<Longrightarrow> (x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI x) l \<longrightarrow>
       s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI x)) \<longrightarrow>
       (\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI y) l \<longrightarrow>
       s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI y))\<close>
  apply (erule rtrancl_induct)
   apply blast
  apply clarify
  apply (erule state_transition_in.cases)
      apply (simp add: actors_graph_def move_graph_a_def nodes_def)
      apply (rule conjI)
  apply (rule impI)
  apply metis
  apply metis
  apply (simp add: actors_graph_def nodes_def)
  apply (metis insertE)
  defer
    apply (simp add: actors_graph_def nodes_def)
    apply (metis DiffE)
  apply (case_tac \<open>s = h\<close>)
  apply (metis (mono_tags, lifting) CollectI RRLoopThree.actors_graph_def RRLoopThree.agra.simps RRLoopThree.atI_def RRLoopThree.graphI.simps RRLoopThree.state_transition_in.put same_nodes0)
   apply (subgoal_tac \<open> ((Actor s, hs), n) \<in> RRLoopThree.lgra (graphI I) l\<close>)
  using RRLoopThree.state_transition_in.put same_actors0 apply blast
  apply (subgoal_tac \<open>((Actor s, hs), n) \<noteq> ((Actor h, hs), n) \<close>)
  apply (smt (z3) RRLoopThree.graphI.simps RRLoopThree.lgra.simps UnE empty_def fst_conv fun_upd_other fun_upd_same insert_Collect mem_Collect_eq)
  apply (meson Pair_inject inj_eq)
(* *)
  apply (case_tac \<open>s = h'\<close>)
  apply (simp add: actors_graph_def)
  using RRLoopThree.atI_def RRLoopThree.nodes_def apply auto[1]
  apply blast
  apply blast
   apply (subgoal_tac \<open> ((Actor s, hs), n) \<in> RRLoopThree.lgra (graphI I) l\<close>)
   apply (metis RRLoopThree.state_transition_in.process same_actors0)
  apply (subgoal_tac \<open>((Actor s, hs), n) \<noteq> (f \<Updown> ((Actor h', hsa), na)) \<close>)
  apply (simp add: actors_graph_def)
  apply (metis DiffE insertE)
  apply (simp add: secure_process_def)
  by (metis (mono_tags, lifting) Rep_label_fun fst_conv injD mem_Collect_eq)

lemma owner_actors_invO: \<open>inj Actor \<Longrightarrow> (x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI x) l \<longrightarrow>
       s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI x)) ==>
       (\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI y) l \<longrightarrow>
       s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI y))\<close>
  using owner_actors_inv by blast


(* Wow this is it! Next steps (to not forget the ideas):
   - apply this to nodes (graphI I) for L then the second invariant conjoint will disappear.
   - then consider adding an invariant for l outside (nodes (graphI I ) being {}
   - thus derive version for lambda l. lgra G l - {(y,x). x = n}
  That should settle the case for del_data .
  Next, attack the secure_process case doing something similar.    
The following is the core lemma that settles the case for some L \<subseteq> (nodes (graphI I)) which
can later be instantiated to all ndoes. One important point is the invariant of this 
induction having in addition the case
(\<forall> l' \<in> (nodes (graphI I)) - L. (lgra (graphI I) l' = (lgra (graphI I') l')))
for those outside the set L!
*)
lemma del_data_setOOOO: \<open>inj Actor \<Longrightarrow>
(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI IO) l \<longrightarrow>
           s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI IO)) \<Longrightarrow>
          (IO  \<rightarrow>\<^sub>n* I) \<Longrightarrow>
          surj Actor \<Longrightarrow> finite L \<Longrightarrow>
          L \<subseteq> (nodes (graphI I)) \<longrightarrow> 
            (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and> 
            (\<forall> l \<in> L. (lgra (graphI I) l  - {(y, x). x = n } = (lgra (graphI I') l)))
          \<and> (\<forall> l' \<in> (nodes (graphI I)) - L. (lgra (graphI I) l' = (lgra (graphI I') l'))))\<close>
  apply (erule finite_induct)
   apply (simp add: state_transition_in_refl_def)
   apply (rule_tac x = I in exI)
  apply simp
  apply (rule impI)
  apply (drule mp)
  apply simp
  apply (erule exE)
(* first the case analysis *)
  apply (case_tac \<open>(\<exists> h. (\<exists> hs. ((h, hs), n) \<in> (lgra (graphI I)) x))\<close>)
(* case not exists *)
   prefer 2
  apply (subgoal_tac \<open> ((RRLoopThree.lgra (RRLoopThree.graphI I'))
               (x := RRLoopThree.lgra (RRLoopThree.graphI I') x - {(y::actor \<times> actor set, x::char list). x = n}))
                = (RRLoopThree.lgra (RRLoopThree.graphI I'))\<close>)
  prefer 2
  apply (simp add: state_transition_in_refl_def)
    apply (subgoal_tac \<open>RRLoopThree.lgra (RRLoopThree.graphI I') x - {(y::actor \<times> actor set, x::char list). x = n}
                       = RRLoopThree.lgra (RRLoopThree.graphI I') x\<close>)
     apply simp
    apply (subgoal_tac \<open>RRLoopThree.lgra (RRLoopThree.graphI I') x \<inter> {(y::actor \<times> actor set, x::char list). x = n} = {}\<close>)
  apply force
  apply auto[1]
   apply (simp add: state_transition_in_refl_def)
   apply (rule_tac x = I' in exI)
   apply fastforce
(* other case (\<exists> h. (\<exists> hs. ((h, hs), n) \<in> (lgra (graphI I')) x)) *)
  apply (erule exE)+
  apply (subgoal_tac \<open>\<exists> s. h = Actor s\<close>)
  prefer 2
   apply (simp add: surj_def)
  apply (erule exE, simp)
  apply (rule_tac x = \<open>Infrastructure 
                   (Lgraph (gra (graphI I'))(agra (graphI I'))(cgra (graphI I'))
                   ((lgra (graphI I'))(x := (lgra (graphI I') x) - {(y, x). x = n })))
                   (delta I')\<close> in exI)
  apply (erule conjE)+
  apply (rule conjI)
  apply (simp add: state_transition_in_refl_def)
  thm rtrancl_into_rtrancl
   apply (rule_tac b = I' in rtrancl_into_rtrancl, assumption)
  apply simp
  apply (rule_tac l = x and G = "graphI I'" and h = s and hs = hs in del_data)
      apply (rule refl)
     prefer 2
  using same_nodes apply auto[1]
    prefer 3
    apply (rule refl)
   prefer 2
   apply assumption
  apply (subgoal_tac \<open>(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI I') l \<longrightarrow>
       s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI I'))\<close>, blast)
  apply (rule owner_actors_invO, assumption, assumption)+
  apply simp
  by simp

lemma del_data_setOOOOall: \<open>inj Actor \<Longrightarrow>
(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI IO) l \<longrightarrow>
           s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI IO)) \<Longrightarrow>
          (IO  \<rightarrow>\<^sub>n* I) \<Longrightarrow>
          surj Actor \<Longrightarrow> finite L \<Longrightarrow>
          L \<subseteq> (nodes (graphI I)) \<longrightarrow> 
            (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and> 
            (RRLoopThree.gra (RRLoopThree.graphI I)) = (RRLoopThree.gra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.agra (RRLoopThree.graphI I)) = (RRLoopThree.agra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.cgra (RRLoopThree.graphI I)) = (RRLoopThree.cgra (RRLoopThree.graphI I')) \<and>
            (\<forall> l \<in> L. (lgra (graphI I) l  - {(y, x). x = n } = (lgra (graphI I') l)))
          \<and> (\<forall> l' \<in> (nodes (graphI I)) - L. (lgra (graphI I) l' = (lgra (graphI I') l'))))\<close>
  apply (erule finite_induct)
   apply (simp add: state_transition_in_refl_def)
   apply (rule_tac x = I in exI)
  apply simp
  apply (rule impI)
  apply (drule mp)
  apply simp
  apply (erule exE)
(* first the case analysis *)
  apply (case_tac \<open>(\<exists> h. (\<exists> hs. ((h, hs), n) \<in> (lgra (graphI I)) x))\<close>)
(* case not exists *)
   prefer 2
  apply (subgoal_tac \<open> ((RRLoopThree.lgra (RRLoopThree.graphI I'))
               (x := RRLoopThree.lgra (RRLoopThree.graphI I') x - {(y::actor \<times> actor set, x::char list). x = n}))
                = (RRLoopThree.lgra (RRLoopThree.graphI I'))\<close>)
  prefer 2
  apply (simp add: state_transition_in_refl_def)
    apply (subgoal_tac \<open>RRLoopThree.lgra (RRLoopThree.graphI I') x - {(y::actor \<times> actor set, x::char list). x = n}
                       = RRLoopThree.lgra (RRLoopThree.graphI I') x\<close>)
     apply simp
    apply (subgoal_tac \<open>RRLoopThree.lgra (RRLoopThree.graphI I') x \<inter> {(y::actor \<times> actor set, x::char list). x = n} = {}\<close>)
  apply force
  apply auto[1]
   apply (simp add: state_transition_in_refl_def)
   apply (rule_tac x = I' in exI)
   apply fastforce
(* other case (\<exists> h. (\<exists> hs. ((h, hs), n) \<in> (lgra (graphI I')) x)) *)
  apply (erule exE)+
  apply (subgoal_tac \<open>\<exists> s. h = Actor s\<close>)
  prefer 2
   apply (simp add: surj_def)
  apply (erule exE, simp)
  apply (rule_tac x = \<open>Infrastructure 
                   (Lgraph (gra (graphI I'))(agra (graphI I'))(cgra (graphI I'))
                   ((lgra (graphI I'))(x := (lgra (graphI I') x) - {(y, x). x = n })))
                   (delta I')\<close> in exI)
  apply (erule conjE)+
  apply (rule conjI)
  apply (simp add: state_transition_in_refl_def)
  thm rtrancl_into_rtrancl
   apply (rule_tac b = I' in rtrancl_into_rtrancl, assumption)
  apply simp
  apply (rule_tac l = x and G = "graphI I'" and h = s and hs = hs in del_data)
      apply (rule refl)
     prefer 2
  using same_nodes apply auto[1]
    prefer 3
    apply (rule refl)
   prefer 2
   apply assumption
  apply (subgoal_tac \<open>(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI I') l \<longrightarrow>
       s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI I'))\<close>, blast)
  apply (rule owner_actors_invO, assumption, assumption)+
  apply simp
  by simp


lemma del_data_setOOOOa: \<open>inj Actor \<Longrightarrow>
(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI IO) l \<longrightarrow>
           s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI IO)) \<Longrightarrow>
          (IO  \<rightarrow>\<^sub>n* I) \<Longrightarrow>
          surj Actor \<Longrightarrow> finite L \<Longrightarrow>
          L \<subseteq> (nodes (graphI I)) \<Longrightarrow> 
            (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and> 
            (\<forall> l \<in> L. (lgra (graphI I) l  - {(y, x). x = n } = (lgra (graphI I') l)))
          \<and> (\<forall> l' \<in> (nodes (graphI I)) - L. (lgra (graphI I) l' = (lgra (graphI I') l'))))\<close>
  using del_data_setOOOO by presburger


lemma del_data_setOOOOa_all: \<open>inj Actor \<Longrightarrow>
(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI IO) l \<longrightarrow>
           s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI IO)) \<Longrightarrow>
          (IO  \<rightarrow>\<^sub>n* I) \<Longrightarrow>
          surj Actor \<Longrightarrow> finite L \<Longrightarrow>
          L \<subseteq> (nodes (graphI I)) \<Longrightarrow> 
            (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and> 
            (RRLoopThree.gra (RRLoopThree.graphI I)) = (RRLoopThree.gra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.agra (RRLoopThree.graphI I)) = (RRLoopThree.agra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.cgra (RRLoopThree.graphI I)) = (RRLoopThree.cgra (RRLoopThree.graphI I')) \<and>
            (\<forall> l \<in> L. (lgra (graphI I) l  - {(y, x). x = n } = (lgra (graphI I') l)))
          \<and> (\<forall> l' \<in> (nodes (graphI I)) - L. (lgra (graphI I) l' = (lgra (graphI I') l'))))\<close>
  using del_data_setOOOOall by presburger

lemma del_data_setOOOOb: \<open>inj Actor \<Longrightarrow>
(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI IO) l \<longrightarrow>
           s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI IO)) \<Longrightarrow>
          (IO  \<rightarrow>\<^sub>n* I) \<Longrightarrow>
          surj Actor \<Longrightarrow> finite (nodes (graphI I)) \<Longrightarrow>
            (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and>
             (\<forall> l \<in> (nodes (graphI I)). (lgra (graphI I) l  - {(y, x). x = n } = (lgra (graphI I') l)))
          \<and> (\<forall> l' \<in> (nodes (graphI I)) - (nodes (graphI I)). (lgra (graphI I) l' = (lgra (graphI I') l'))))\<close>
  apply (rule del_data_setOOOOa)
       apply assumption+
  by (rule subset_refl)

lemma del_data_setOOOOb_all: \<open>inj Actor \<Longrightarrow>
(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI IO) l \<longrightarrow>
           s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI IO)) \<Longrightarrow>
          (IO  \<rightarrow>\<^sub>n* I) \<Longrightarrow>
          surj Actor \<Longrightarrow> finite (nodes (graphI I)) \<Longrightarrow>
            (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and> 
            (RRLoopThree.gra (RRLoopThree.graphI I)) = (RRLoopThree.gra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.agra (RRLoopThree.graphI I)) = (RRLoopThree.agra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.cgra (RRLoopThree.graphI I)) = (RRLoopThree.cgra (RRLoopThree.graphI I')) \<and>
            (\<forall> l \<in> (nodes (graphI I)). (lgra (graphI I) l  - {(y, x). x = n } = (lgra (graphI I') l)))
          \<and> (\<forall> l' \<in> (nodes (graphI I)) - (nodes (graphI I)). (lgra (graphI I) l' = (lgra (graphI I') l'))))\<close>
  apply (rule del_data_setOOOOa_all)
       apply assumption+
  by (rule subset_refl)

lemma del_data_setOOOOc: \<open>inj Actor \<Longrightarrow>
(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI IO) l \<longrightarrow>
           s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI IO)) \<Longrightarrow>
          (IO  \<rightarrow>\<^sub>n* I) \<Longrightarrow>
          surj Actor \<Longrightarrow> finite (nodes (graphI I)) \<Longrightarrow>
            (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and> 
            (\<forall> l \<in> (nodes (graphI I)). (lgra (graphI I) l - {(y, x). x = n } = (lgra (graphI I') l))))\<close>
  using del_data_setOOOOb by simp

lemma del_data_setOOOOc_all: \<open>inj Actor \<Longrightarrow>
(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI IO) l \<longrightarrow>
           s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI IO)) \<Longrightarrow>
          (IO  \<rightarrow>\<^sub>n* I) \<Longrightarrow>
          surj Actor \<Longrightarrow> finite (nodes (graphI I)) \<Longrightarrow>
            (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and>  
            (RRLoopThree.gra (RRLoopThree.graphI I)) = (RRLoopThree.gra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.agra (RRLoopThree.graphI I)) = (RRLoopThree.agra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.cgra (RRLoopThree.graphI I)) = (RRLoopThree.cgra (RRLoopThree.graphI I')) \<and>
            (\<forall> l \<in> (nodes (graphI I)). (lgra (graphI I) l - {(y, x). x = n } = (lgra (graphI I') l))))\<close>
  using del_data_setOOOOb_all by simp

(* Now add the bit with the invariant saying that outside the nodes (graphI I)
   we have that lgra (graphI I) = {}. That will then allow to combine 
   the lemma del_data_setOOOOc to show there exists I' with 
   (lgra (graphI I') = \<lambda> l. (lgra (graphI I) l - {(y, x). x = n } *)
lemma del_data_funOOOO_all: \<open>inj Actor \<Longrightarrow>
(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI IO) l \<longrightarrow>
           s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI IO)) \<Longrightarrow>
          (IO  \<rightarrow>\<^sub>n* I) \<Longrightarrow>
          surj Actor \<Longrightarrow> finite (nodes (graphI I)) \<Longrightarrow>
            (\<forall> I''. IO  \<rightarrow>\<^sub>n* I'' \<longrightarrow> 
                (\<forall> l. l \<notin> (nodes (graphI I'')) \<longrightarrow> (lgra (graphI I'') l) = {}))  \<Longrightarrow>
            (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and>   
            (RRLoopThree.gra (RRLoopThree.graphI I)) = (RRLoopThree.gra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.agra (RRLoopThree.graphI I)) = (RRLoopThree.agra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.cgra (RRLoopThree.graphI I)) = (RRLoopThree.cgra (RRLoopThree.graphI I')) \<and>
            (\<lambda> l. (lgra (graphI I) l) - {(y, x). x = n }) = (lgra (graphI I')))\<close>
  apply (subgoal_tac \<open> (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and>   
            (RRLoopThree.gra (RRLoopThree.graphI I)) = (RRLoopThree.gra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.agra (RRLoopThree.graphI I)) = (RRLoopThree.agra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.cgra (RRLoopThree.graphI I)) = (RRLoopThree.cgra (RRLoopThree.graphI I')) \<and>
            (\<forall> l \<in> (nodes (graphI I)). (lgra (graphI I) l - {(y, x). x = n } = (lgra (graphI I') l))))\<close>)
   prefer 2
   apply (simp add: del_data_setOOOOc_all) 
  apply (erule exE)
  apply (erule conjE)
  apply (rule_tac x = I' in exI)
  apply (rule conjI, assumption)
  apply (rule conjI, simp)
  apply (rule conjI, simp)
  apply (rule conjI, simp)
  apply (rule ext)
  apply (case_tac "l \<in>RRLoopThree.nodes (RRLoopThree.graphI I)")
  apply meson
  by (smt (verit, ccfv_threshold) RRLoopThree.state_transition_in_refl_def empty_Collect_eq empty_iff rtrancl.simps rtrancl_induct same_nodes set_diff_eq)
(*  if we use I instead of I'' in the notin premise
by (smt (verit, ccfv_SIG) RRLoopThree.state_transition_in_refl_def empty_Collect_eq empty_iff rtrancl.simps rtrancl_induct set_diff_eq)
*)
lemma del_data_funOOOO: \<open>inj Actor \<Longrightarrow>
(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI IO) l \<longrightarrow>
           s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI IO)) \<Longrightarrow>
          (IO  \<rightarrow>\<^sub>n* I) \<Longrightarrow>
          surj Actor \<Longrightarrow> finite (nodes (graphI I)) \<Longrightarrow>
            (\<forall> I''. IO  \<rightarrow>\<^sub>n* I'' \<longrightarrow> 
                (\<forall> l. l \<notin> (nodes (graphI I)) \<longrightarrow> (lgra (graphI I'') l) = {}))  \<Longrightarrow>
            (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and> 
            (\<lambda> l. (lgra (graphI I) l) - {(y, x). x = n }) = (lgra (graphI I')))\<close>
  apply (subgoal_tac \<open> (\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and> 
            (\<forall> l \<in> (nodes (graphI I)). (lgra (graphI I) l - {(y, x). x = n } = (lgra (graphI I') l))))\<close>)
   prefer 2
   apply (simp add: del_data_setOOOOc) 
  apply (erule exE)
  apply (erule conjE)
  apply (rule_tac x = I' in exI)
  apply (rule conjI, assumption)
  apply (rule ext)
  apply (case_tac "l \<in>RRLoopThree.nodes (RRLoopThree.graphI I)")
  apply meson
  by (smt (verit, ccfv_SIG) RRLoopThree.state_transition_in_refl_def empty_Collect_eq empty_iff rtrancl.simps rtrancl_induct set_diff_eq)

(* 
*)
lemma test_thmOOO: \<open>inj Actor \<Longrightarrow>
(\<forall> s hs n l. ((Actor s, hs), n) \<in> RRLoopThree.lgra (RRLoopThree.graphI IO) l \<longrightarrow>
           s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI IO)) \<Longrightarrow>
          (IO  \<rightarrow>\<^sub>n* I) \<Longrightarrow>
          surj Actor \<Longrightarrow> finite (nodes (graphI I)) \<Longrightarrow>
            (\<forall> I''. IO  \<rightarrow>\<^sub>n* I'' \<longrightarrow> 
                (\<forall> l. l \<notin> (nodes (graphI I'')) \<longrightarrow> (lgra (graphI I'') l) = {}))  \<Longrightarrow>
         (I,
          RRLoopThree.infrastructure.Infrastructure
          (RRLoopThree.igraph.Lgraph (RRLoopThree.gra (RRLoopThree.graphI I))
           (RRLoopThree.agra (RRLoopThree.graphI I)) (RRLoopThree.cgra (RRLoopThree.graphI I))
           (\<lambda> l::location. (RRLoopThree.lgra (RRLoopThree.graphI I)) l - {(y::actor \<times> actor set, x::char list). x = d}))
            (RRLoopThree.delta I )) 
\<in>  {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  apply (subgoal_tac \<open>(\<exists> I'.  (I  \<rightarrow>\<^sub>n* I') \<and>    
            (RRLoopThree.gra (RRLoopThree.graphI I)) = (RRLoopThree.gra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.agra (RRLoopThree.graphI I)) = (RRLoopThree.agra (RRLoopThree.graphI I')) \<and>
            (RRLoopThree.cgra (RRLoopThree.graphI I)) = (RRLoopThree.cgra (RRLoopThree.graphI I')) \<and>
            (\<lambda> l. (lgra (graphI I) l) - {(y, x). x = d }) = (lgra (graphI I')))\<close>)
   apply (erule exE)
  prefer 2
  using del_data_funOOOO_all apply presburger
  by (metis RRLoopThree.agra.simps RRLoopThree.cgra.simps RRLoopThree.delta.simps RRLoopThree.gra.simps RRLoopThree.graphI.simps RRLoopThree.igraph.exhaust RRLoopThree.infrastructure.exhaust RRLoopThree.lgra.simps RRLoopThree.state_transition_in_refl_def init_state_policy)


lemma test_thm: \<open>(I,
                    RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (RRLoopThree.gra (RRLoopThree.graphI I))
           (RRLoopThree.agra (RRLoopThree.graphI I)) (RRLoopThree.cgra (RRLoopThree.graphI I))
           (\<lambda> l::location. (RRLoopThree.lgra (RRLoopThree.graphI I)) l - {(y::actor \<times> actor set, x::char list). x = d}))
            (RRLoopThree.delta I )) 
\<in>  {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  sorry


end