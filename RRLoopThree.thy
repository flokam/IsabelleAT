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
       ((Actor h', hs), n) \<in> lgra G l' \<Longrightarrow> Actor h \<in> hs \<Longrightarrow> 
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

end