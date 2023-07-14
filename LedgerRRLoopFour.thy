theory LedgerRRLoopFour
(* Fourth instance of the RRLoop: here, we now introduce the ledger type
   and integrate it into a redefined infrastructure type. This should 
   avoid the put attack but doesn't in the end since an insider could still
   overwrite the entry made by Bob. *)
imports hcKripkeThree 
begin
type_synonym data = string
  (* Inspired by Myers DLM mode: first is the owner of a data item, second is the
     set of all actors that may access the data item *)
(* Here in this iteration of the RR-Loop the dlm needs to be refined replacing
   actors by identities since otherwise the uniqueness of the label imposed
   in the ledger typedef cannot be proved for actors (note that we intentionally
   didn't stipulate Actor to be injective to allow for insider attacks) 
before:
type_synonym dlm = "actor * actor set"
now: *)
type_synonym dlm = "identity * identity set"

type_synonym acond = "(dlm * data) set"

(* In this efficient modeling of ledger (cf older versions), we have a unique
(dlm * node set) for each data -- if it is defined --, that is, a data has a unique label and
one set of locations where it occurs. 
There is redundancy in this representation compared to the above one:
the fact that there is no label assigned to a data item may be
recorded as lg(d) = None or lg(d) = (l,{}) for any label l.
I don't see why this should cause confusion. 
*)
type_synonym ledger = \<open>data \<Rightarrow> (dlm \<times> location set)option\<close>

lemma ledger_def_prop: "\<forall> lg:: ledger. \<forall> d:: data.
     lg d = None | (\<exists>! lL. lg d = Some(lL))"
  by force 

lemma prod_exu: \<open>\<forall> p:: ('a * 'b). \<exists>! a. \<exists>! b. p = (a,b)\<close>
  by auto

lemma ledger_def_prop'[rule_format]: "\<forall> lg:: ledger. \<forall> d:: data.
     lg d = None | (\<exists>! l. (\<exists>! L. lg d = Some(l, L)))"
  apply (rule allI)+
  apply (case_tac "lg d")
   apply (erule disjI1)
  apply(rule disjI2)
  by (auto simp: ledger_def_prop prod_exu)

(*
typedef ledger = "{ ld :: dlm \<times> data \<Rightarrow> location set. \<forall> d. (\<forall> l. ld (l, d) = {}) \<or>
(\<exists>! l. ld (l, d) \<noteq> {})}"
  by auto

typedef ledger = "{ ld :: dlm \<times> data \<Rightarrow> location set. \<forall> d. (\<forall> l. ld (l, d) = {}) \<or>
(\<exists>! dl. ld dl \<noteq> {})}"
  by auto
*)

datatype igraph = Lgraph "(location * location)set" "location \<Rightarrow> identity set"
                         "actor \<Rightarrow> (string set * string set)"  "location \<Rightarrow> string"
                         "ledger"
datatype infrastructure = 
         Infrastructure "igraph" 
                        "[igraph ,location] \<Rightarrow> policy set" 
primrec loc :: "location \<Rightarrow> nat"
where  "loc(Location n) = n"
primrec gra :: "igraph \<Rightarrow> (location * location)set"
where  "gra(Lgraph g a c l ld) = g"
primrec agra :: "igraph \<Rightarrow> (location \<Rightarrow> identity set)"
where  "agra(Lgraph g a c l ld) = a"
primrec cgra :: "igraph \<Rightarrow> (actor \<Rightarrow> string set * string set)"
where  "cgra(Lgraph g a c l ld) = c"
primrec lgra :: "igraph \<Rightarrow> (location \<Rightarrow> string)"
  where  "lgra(Lgraph g a c l ld) = l"
primrec ledgra :: "igraph \<Rightarrow> ledger"
  where  "ledgra(Lgraph g a c l ld) = ld"

(*
definition ledgra_upd :: "[ledger, dlm \<times> data, location set] \<Rightarrow> ledger" ("_ _ := _" 50)
  where
 "ledgra_upd ld dl L == Abs_ledger((Rep_ledger ld)(dl := L))"


definition ledgra_at :: "[ledger, dlm \<times> data] \<Rightarrow> location set" ("_ \<nabla> _" 50)
  where  "l \<nabla> dl \<equiv> (Rep_ledger l) dl"

lemma ledgra_at_fun: "(\<forall> d. (\<forall> l. (f :: dlm \<times> data \<Rightarrow> location set)(l, d) = {}) \<or>
(\<exists>! l. f (l, d) \<noteq> {})) \<Longrightarrow> (Rep_ledger (Abs_ledger f)) dl = f dl"
  by (simp add: Abs_ledger_inverse)
*)

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
primrec lspace :: "[infrastructure, location ] \<Rightarrow> string"
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
  where "isin G l s \<equiv> s = (lgra G l)"

(* types need to change because of new dlm labels *)
definition owner :: "dlm * data \<Rightarrow> identity" where "owner d \<equiv> fst(fst d)"
    
definition owns :: "[igraph, location, identity, dlm * data] \<Rightarrow> bool"    
  where "owns G l a d \<equiv> owner d = a"
    
definition readers :: "dlm * data \<Rightarrow> identity set"
  where "readers d \<equiv> snd (fst d)"

definition has_access :: "[igraph, location, identity, dlm * data] \<Rightarrow> bool"    
where "has_access G l a d \<equiv> owns G l a d \<or> a \<in> readers d"
  
definition atI :: "[identity, igraph, location] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> (agra G l)"

definition enables :: "[infrastructure, location, actor, action] \<Rightarrow> bool"
where
"enables I l a a' \<equiv>  (\<exists> (p,e) \<in> delta I (graphI I) l. a' \<in> e \<and> p a)"

definition move_graph_a :: "[identity, location, location, igraph] \<Rightarrow> igraph"
where "move_graph_a n l l' g \<equiv> Lgraph (gra g) 
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then 
                     ((agra g)(l := (agra g l) - {n}))(l' := (insert n (agra g l')))
                     else (agra g))(cgra g)(lgra g)(ledgra g)"

(* type of functions that preserves the security labeling *)    
typedef label_fun = "{f :: dlm * data \<Rightarrow> dlm * data. 
                        \<forall> x:: dlm * data. fst x = fst (f x)}"  
proof (auto)
  show "\<exists>x::(identity \<times> identity set) \<times> string \<Rightarrow> (identity \<times> identity set) \<times> string.
       \<forall>(a::identity) (b::identity set) ba::string. (a, b) = fst (x ((a, b), ba))"
  by (rule_tac x = id in exI, simp)
qed

definition secure_process :: "label_fun \<Rightarrow> dlm * data \<Rightarrow> dlm * data" ("_ \<Updown> _" 50)
  where "f  \<Updown> d \<equiv> (Rep_label_fun f) d" 
    
lemma move_graph_eq: "move_graph_a a l l g = g"  
proof (simp add: move_graph_a_def, case_tac g, force)
qed

inductive state_transition_in :: "[LedgerRRLoopFour.infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
  move: "\<lbrakk> G = LedgerRRLoopFour.graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          (a) \<in> actors_graph(graphI I); LedgerRRLoopFour.enables I l' (Actor a) move;
         I' = LedgerRRLoopFour.Infrastructure (move_graph_a a l l' (graphI I))(delta I) \<rbrakk>
         \<Longrightarrow> (I :: LedgerRRLoopFour.infrastructure) \<rightarrow>\<^sub>n I'" 
| get_data : "G = LedgerRRLoopFour.graphI I \<Longrightarrow> (a @\<^bsub>G\<^esub> l) \<Longrightarrow> l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow> l' \<in> nodes G \<Longrightarrow>
        LedgerRRLoopFour.enables I l (Actor a) get \<Longrightarrow> 
        (ledgra G d = (Some ((a', as), L))) \<Longrightarrow> ((a \<in> as) \<or> (a = a')) \<Longrightarrow> 
        I' = LedgerRRLoopFour.Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                           ((ledgra G)(d := Some((a', as), (L \<union> {l})))))
                   (delta I)
         \<Longrightarrow> (I :: LedgerRRLoopFour.infrastructure) \<rightarrow>\<^sub>n I'" 
| process : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow>
        enables I l (Actor a) eval \<Longrightarrow> 
        ledgra G d = Some ((a', as), L) \<Longrightarrow>
        a \<in> as \<or> a = a'\<Longrightarrow>
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                                 (((ledgra G)(d:= None))((f d):= Some ((a', as), L))))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"  
| del_data : "G = graphI I \<Longrightarrow> a \<in> actors_graph G \<Longrightarrow> l \<in> nodes G \<Longrightarrow> l \<in> L \<Longrightarrow>
             ledgra G d = Some ((a', as), L) \<Longrightarrow>
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                    ((ledgra G)(d:= None)))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 
| put : "G = LedgerRRLoopFour.graphI I \<Longrightarrow> LedgerRRLoopFour.atI a G l \<Longrightarrow> 
         LedgerRRLoopFour.enables I l (Actor a) put \<Longrightarrow>
         ledgra G d = Some ((a, as), L) \<Longrightarrow>
        I' = LedgerRRLoopFour.Infrastructure 
                  (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                          ((ledgra G)(d := Some ((a, as), insert l L))))
                   (delta I)
          \<Longrightarrow> I \<rightarrow>\<^sub>n I'"


(* *)
instantiation "infrastructure" :: state
begin

definition 
   state_transition_infra_def: "(i \<rightarrow>\<^sub>i i') =  (i \<rightarrow>\<^sub>n (i' :: infrastructure))"

instance
  by (rule MC.class.MC.state.of_class.intro)

definition state_transition_in_refl ("(_ \<rightarrow>\<^sub>n* _)" 50)
where "s \<rightarrow>\<^sub>n* s' \<equiv> ((s,s') \<in> {(x,y). state_transition_in x y}\<^sup>*)"

end

thm Finite_Set.fold_def

definition dlm_to_dlm:: "LedgerRRLoopFour.dlm \<Rightarrow> RRLoopThree.dlm"
  where
  "dlm_to_dlm  \<equiv> (\<lambda> ((s :: string), (sl :: string set)). (Actor s, Actor ` sl))"

definition data_trans :: "LedgerRRLoopFour.dlm \<times> data \<Rightarrow> RRLoopThree.dlm \<times> data"
  where "data_trans  \<equiv> (\<lambda> (l :: (string *  string set),d :: string). (dlm_to_dlm l, d))"

definition ledger_to_loc :: \<open>ledger \<Rightarrow> location \<Rightarrow> (RRLoopThree.dlm \<times> RRLoopThree.data) set\<close>
  where 
\<open>ledger_to_loc ld l \<equiv> (if (\<exists> d. l \<in> snd(the(ld d))) then
               {(lb,d). l \<in> snd(the(ld d))} else {})\<close>

lemma update_empty_lem0: "xa \<in> (f(x := {})) y \<Longrightarrow> xa \<in> f y"
  by (simp, case_tac "x = y", simp+)


lemma inset_n_empty: "x \<in> s \<Longrightarrow> s \<noteq> {}"
  by force

lemma inj_data_trans: "inj Actor \<Longrightarrow> inj data_trans"
  apply (rule injI)
  apply (simp add: data_trans_def dlm_to_dlm_def)
  apply (case_tac x)
  apply (case_tac y)
  apply simp
  apply (case_tac aa)
  apply (case_tac a)
  apply simp
  apply (rule conjI)
  apply (erule conjE)+
   apply (erule injD, assumption)
  apply (erule image_inj)
  by simp

lemma setsub_spec: "A - {x. P x} = A - {x. x \<in> A \<and> P x}"
  by blast

lemma b32a0: "l \<noteq> x \<Longrightarrow> x \<notin> Rep_ledger lg xa \<Longrightarrow>
               x \<notin> ((Rep_ledger lg)(((a, as), n) := Rep_ledger lg ((a, as), n) - {l})) xa"
  apply simp
  apply (rule impI)
  apply (erule subst)
  by assumption

lemma inj_inj_on: "inj f \<Longrightarrow> inj_on f A"
  by (simp add: inj_def inj_onI)



definition ref_map :: "[LedgerRRLoopFour.infrastructure, 
                        [RRLoopThree.igraph, location] \<Rightarrow> policy set]
                        \<Rightarrow> RRLoopThree.infrastructure"
  where "ref_map I lp = RRLoopThree.Infrastructure 
                                 (RRLoopThree.Lgraph
                                        (gra (graphI I))(agra (graphI I))
                                        (cgra (graphI I))
                                        (ledger_to_loc (ledgra (graphI I))))
                                 lp"
    
lemma delta_invariant: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  delta(z) = delta(z')"
  apply clarify
  apply (erule state_transition_in.cases)
  by simp+


             
end