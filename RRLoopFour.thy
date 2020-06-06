theory RRLoopFour
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


typedef ledger = "{ ld :: dlm \<times> data \<Rightarrow> location set. \<forall> d. (\<forall> l. ld (l, d) = {}) \<or>
(\<exists>! l. ld (l, d) \<noteq> {})}"
  by auto
(*
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

definition ledgra_upd :: "[ledger, dlm \<times> data, location set] \<Rightarrow> ledger" ("_ _ := _" 50)
  where
 "ledgra_upd ld dl L == Abs_ledger((Rep_ledger ld)(dl := L))"


definition ledgra_at :: "[ledger, dlm \<times> data] \<Rightarrow> location set" ("_ \<nabla> _" 50)
  where  "l \<nabla> dl \<equiv> (Rep_ledger l) dl"

lemma ledgra_at_fun: "(\<forall> d. (\<forall> l. (f :: dlm \<times> data \<Rightarrow> location set)(l, d) = {}) \<or>
(\<exists>! l. f (l, d) \<noteq> {})) \<Longrightarrow> (Rep_ledger (Abs_ledger f)) dl = f dl"
  by (simp add: Abs_ledger_inverse)


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

inductive state_transition_in :: "[infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
  move: "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          (a) \<in> actors_graph(graphI I); enables I l' (Actor a) move;
         I' = Infrastructure (move_graph_a a l l' (graphI I))(delta I) \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 
| get_data : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow> l \<in> nodes G \<Longrightarrow> l' \<in> nodes G \<Longrightarrow> 
        enables I l (Actor a) get \<Longrightarrow> 
        (ledgra G \<nabla> ((a', as), n)) = L \<Longrightarrow> l' \<in> L  \<Longrightarrow> a \<in> as \<Longrightarrow> 
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                           ((ledgra G)((a', as), n) := (L \<union> {l})))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| process : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow>
        enables I l (Actor a) eval \<Longrightarrow> 
        (ledgra G \<nabla> ((a', as), n)) = L \<Longrightarrow>
        a \<in> as \<or> a = a'\<Longrightarrow>
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                                 ((ledgra G ((a', as), n) := {}
                                    (f :: label_fun) \<Updown> ((a', as), n) := L)))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"  
| del_data : "G = graphI I \<Longrightarrow> a \<in> actors_graph G \<Longrightarrow> l \<in> nodes G \<Longrightarrow> l \<in> L \<Longrightarrow>
             (ledgra G \<nabla> ((a, as), n)) = L \<Longrightarrow>
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                    (ledgra G ((a, as),n) := L - {l}))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| put : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow> enables I l (Actor a) put \<Longrightarrow>
        I' = Infrastructure 
                  (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                          (ledgra G ((a, as),n) := {l}))
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

thm Finite_Set.fold_def

definition dlm_to_dlm:: "RRLoopFour.dlm \<Rightarrow> RRLoopThree.dlm"
  where
  "dlm_to_dlm  \<equiv> (\<lambda> ((s :: string), (sl :: string set)). (Actor s, Actor ` sl))"

definition data_trans :: "RRLoopFour.dlm \<times> data \<Rightarrow> RRLoopThree.dlm \<times> data"
  where "data_trans  \<equiv> (\<lambda> (l :: (string *  string set),d :: string). (dlm_to_dlm l, d))"

definition ledger_to_loc:: "[ledger, location] \<Rightarrow> RRLoopThree.acond" (* acond is abbrev for (dlm \<times> data) set *)
  where 
   "ledger_to_loc ld l \<equiv> if l \<in> \<Union> (range(Rep_ledger ld)) 
                          then fmap data_trans {dl. l \<in> (ld \<nabla> dl)} else {}"

lemma ledger_to_loc_data_unique: "Rep_ledger ld (dl,d) \<noteq> {} \<Longrightarrow> 
                                  Rep_ledger ld (dl',d) \<noteq> {} \<Longrightarrow> dl = dl'"
  apply (subgoal_tac "Rep_ledger (ld)
    \<in> {ld::(char list \<times> char list set) \<times> char list \<Rightarrow> location set.
        \<forall>d::char list.
           (\<forall>l::char list \<times> char list set. ld (l, d) = {}) \<or>
           (\<exists>! l:: (char list \<times> char list set). ld (l,d) \<noteq> {})}")
   apply simp
   apply (drule_tac x = d in spec)
   apply (erule disjE)
    apply (drule_tac x = "fst dl" in spec)
    apply (drule_tac x = "snd dl" in spec)
    apply simp
   apply (erule ex1E)
  apply (frule_tac x = dl in spec)
   apply (drule mp, assumption)
  apply (frule_tac x = dl' in spec)
   apply (drule mp, assumption)
   apply (erule ssubst)+
  apply (rule refl)
by (rule Rep_ledger)

lemma ledger_to_loc_data_unique0: "Rep_ledger ld dld \<noteq> {} \<Longrightarrow> 
                                  \<forall> dld'. Rep_ledger ld dld' \<noteq> {} \<Longrightarrow> fst dld = fst dld'"
  apply (simp add: ledger_to_loc_data_unique)
  oops

lemma ledgra_ledger_to_loc: 
      "finite {dl::(char list \<times> char list set) \<times> char list. l \<in> Rep_ledger (ledgra G) dl} \<Longrightarrow>
       l \<in> (ledgra G \<nabla> ((a, as), n)) \<Longrightarrow>
        ((Actor a, Actor ` as), n) \<in> ledger_to_loc (ledgra G) l"
  apply (simp add: ledgra_at_def ledger_to_loc_def)
  apply (rule conjI)
   apply (rule impI)
   apply (subgoal_tac "((Actor a, Actor ` as), n) = data_trans ((a, as), n)")
  apply (erule ssubst)
    apply (rule fmap_lem_map, assumption)
    apply (simp add: Rep_ledger)
  apply (simp add: data_trans_def dlm_to_dlm_def)
  apply (rule exI)+
  by assumption

(*  lemma for ledgra_upd *)
lemma ledgra_update_lem: "(L = {} \<or> (Rep_ledger lg x \<noteq> {})) \<Longrightarrow>
                          Rep_ledger (Abs_ledger ((Rep_ledger lg)(x := L))) =
                            ((Rep_ledger lg)(x := L))"
  apply (subgoal_tac "((Rep_ledger lg)(x := L)) \<in> {ld::(char list \<times> char list set) \<times> char list \<Rightarrow> location set.
      \<forall>d::char list.
         (\<forall>l::char list \<times> char list set. ld (l, d) = {}) \<or>
         (\<exists>!l::char list \<times> char list set. ld (l, d) \<noteq> {})}")
   apply (erule Abs_ledger_inverse)
  apply simp
  apply (erule disjE)
(* L = {} *)
   apply simp
  apply (subgoal_tac "Rep_ledger lg \<in> {ld::(char list \<times> char list set) \<times> char list \<Rightarrow> location set.
      \<forall>d::char list.
         (\<forall>l::char list \<times> char list set. ld (l, d) = {}) \<or>
         (\<exists>!l::char list \<times> char list set. ld (l, d) \<noteq> {})}")
    apply simp
  apply blast
   apply (rule Rep_ledger)
(* *)
  apply (case_tac "L = {}") 
   apply simp
  apply (subgoal_tac "Rep_ledger lg \<in> {ld::(char list \<times> char list set) \<times> char list \<Rightarrow> location set.
      \<forall>d::char list.
         (\<forall>l::char list \<times> char list set. ld (l, d) = {}) \<or>
         (\<exists>!l::char list \<times> char list set. ld (l, d) \<noteq> {})}")
    apply simp
  apply blast
   apply (rule Rep_ledger)
(* L \<noteq> {} *)
  apply (rule allI)
  apply (case_tac "snd x = d")
  apply (rule disjI2)
   apply simp
   apply (rule_tac a = "fst x" in ex1I)
    apply (rule impI)
    apply (erule subst)
  apply simp
    apply (subgoal_tac "Rep_ledger lg \<in> {ld::(char list \<times> char list set) \<times> char list \<Rightarrow> location set.
      \<forall>d::char list.
         (\<forall>l::char list \<times> char list set. ld (l, d) = {}) \<or>
         (\<exists>!l::char list \<times> char list set. ld (l, d) \<noteq> {})}")
  apply simp
   apply (drule_tac x = d in spec)
   apply (erule disjE)
     apply (drule_tac x = "fst(fst x)" in spec)
     apply (drule_tac x = "snd(fst x)" in spec)
     apply (erule notE)
     apply force
    apply (erule ex1E)
    apply (case_tac "(xa, d) = x")
     apply simp
  apply (rotate_tac -1)
     apply (erule subst)
  apply simp
    apply (drule mp, assumption)
    apply (frule_tac x = "fst x" in spec)
    apply (drule mp)
  apply (erule subst)
     apply simp
    apply (drule_tac x = xa in spec)
    apply (drule mp, assumption)
    apply simp
   apply (rule Rep_ledger)
(* snd x \<noteq> d *)
  apply simp
  apply (subgoal_tac "Rep_ledger lg \<in> {ld::(char list \<times> char list set) \<times> char list \<Rightarrow> location set.
      \<forall>d::char list.
         (\<forall>l::char list \<times> char list set. ld (l, d) = {}) \<or>
         (\<exists>!l::char list \<times> char list set. ld (l, d) \<noteq> {})}")
  apply simp
   apply (drule_tac x = d in spec)
   apply (erule disjE)
    apply (rule disjI1)
    apply blast
   apply (rule disjI2)
   apply blast
by (rule Rep_ledger)
 
lemma ledgra_insert0: "(Rep_ledger lg)((a, as), n) = L \<Longrightarrow> l \<noteq> la \<Longrightarrow> l' \<in> L \<Longrightarrow>
         {dl::(char list \<times> char list set) \<times> char list.
           l \<in> Rep_ledger (lg ((a, as), n) := insert la L) dl} =
         {dl::(char list \<times> char list set) \<times> char list.
           l \<in> Rep_ledger lg dl}"
  apply (simp add: ledgra_upd_def)
  apply (subgoal_tac "insert la L = {} \<or> (Rep_ledger lg)((a, as), n) \<noteq> {}")
  prefer 2
   apply blast
  apply (drule ledgra_update_lem)
  apply (rotate_tac -1)
  apply (erule ssubst)
by force

lemma ledgra_insert: "(Rep_ledger lg)((a, as), n) = L \<Longrightarrow> l' \<in> L \<Longrightarrow>
        {dl::(char list \<times> char list set) \<times> char list.
         l \<in> Rep_ledger (lg ((a, as), n) := insert l L) dl} =
          insert ((a, as), n) {dl::(char list \<times> char list set) \<times> char list.
         l \<in> Rep_ledger lg dl}"
  apply (simp add: ledgra_upd_def)
  apply (subgoal_tac "insert l L = {} \<or> (Rep_ledger lg)((a, as), n) \<noteq> {}")
  prefer 2
   apply blast
  apply (drule ledgra_update_lem)
  apply (rotate_tac -1)
  apply (erule ssubst)
  by force

lemma ledger_to_loc_insert: 
  assumes a: "\<forall> l. finite {dl::(char list \<times> char list set) \<times> char list. l \<in> Rep_ledger lg dl}" 
  shows "(lg \<nabla> ((a, as), n)) = L \<Longrightarrow> l' \<in> L \<Longrightarrow>
           ledger_to_loc ((lg ((a, as), n) := insert l L)) =
          (ledger_to_loc lg)(l := insert ((Actor a, Actor ` as), n) (ledger_to_loc lg l))"
 proof (unfold ledger_to_loc_def, rule ext, case_tac "l = la") 
  show \<open>\<And>la::location.
       (lg \<nabla> ((a, as), n)) = L \<Longrightarrow>
       l' \<in> L \<Longrightarrow>
       l = la \<Longrightarrow>
       (if la \<in> \<Union> (range (Rep_ledger (lg ((a, as), n) := insert l L)))
        then fmap data_trans {dl::(char list \<times> char list set) \<times> char list. la \<in> (lg ((a, as), n) := insert l L \<nabla> dl)}
        else {}) =
       ((\<lambda>l::location.
            if l \<in> \<Union> (range (Rep_ledger lg))
            then fmap data_trans {dl::(char list \<times> char list set) \<times> char list. l \<in> (lg \<nabla> dl)} else {})
        (l := insert ((Actor a, Actor ` as), n)
               (if l \<in> \<Union> (range (Rep_ledger lg))
                then fmap data_trans {dl::(char list \<times> char list set) \<times> char list. l \<in> (lg \<nabla> dl)} else {})))
        la\<close>
   apply simp
  apply (rule conjI)
   apply (rule impI)+
  apply (simp add: ledgra_at_def)
   apply (rule conjI)
     apply (rule impI)+
     apply (subst ledgra_insert, assumption, assumption)
     apply (subst fmap_lem)
  prefer 2
       apply (simp add: data_trans_def dlm_to_dlm_def)
      apply (insert a)
      apply (erule spec)
     apply (simp add: ledgra_upd_def)
     apply (subst ledgra_update_lem)
      apply blast
     apply force
    apply (rule impI)+
(*  *)
    apply (rule conjI)
     apply (rule impI)
     apply (subgoal_tac 
          "{dl::(char list \<times> char list set) \<times> char list. la \<in> (lg ((a, as), n) := insert la L \<nabla> dl)} =
           {((a,as),n)}")
      apply (rotate_tac -1, erule ssubst)
    apply (subst fmap_lem_one)
      apply (simp add: data_trans_def dlm_to_dlm_def)
     apply (simp add: ledgra_at_def ledgra_upd_def)
     apply (subst ledgra_update_lem)
      apply blast
     apply force
     apply (simp add: ledgra_upd_def)
     apply (subst ledgra_update_lem)
     apply (simp add: ledgra_at_def, blast)
by force
next show "\<And>la::location.
       (lg \<nabla> ((a, as), n)) = L \<Longrightarrow>
       l' \<in> L \<Longrightarrow>
       l \<noteq> la \<Longrightarrow>
       (if la \<in> \<Union> (range (Rep_ledger (lg ((a, as), n) := insert l L)))
        then fmap data_trans {dl::(char list \<times> char list set) \<times> char list. la \<in> (lg ((a, as), n) := insert l L \<nabla> dl)}
        else {}) =
       ((\<lambda>l::location.
            if l \<in> \<Union> (range (Rep_ledger lg))
            then fmap data_trans {dl::(char list \<times> char list set) \<times> char list. l \<in> (lg \<nabla> dl)} else {})
        (l := insert ((Actor a, Actor ` as), n)
               (if l \<in> \<Union> (range (Rep_ledger lg))
                then fmap data_trans {dl::(char list \<times> char list set) \<times> char list. l \<in> (lg \<nabla> dl)} else {})))
        la"
   apply simp
  apply (rule conjI)
   apply (rule impI)+
  apply (simp add: ledgra_at_def)
   apply (rule conjI)
     apply (rule impI)+
      apply (subst ledgra_insert0, assumption, simp, assumption, rule refl)
     apply (simp add: ledgra_upd_def)
          apply (subst ledgra_update_lem)
      apply blast
     apply (rule impI)
    apply (subgoal_tac "{dl::(char list \<times> char list set) \<times> char list.
         la \<in> ((Rep_ledger lg)(((a, as), n) := insert l L)) dl} = {}")
    apply (rotate_tac -1, erule ssubst)
     apply (simp add: fmap_def)
     apply force
    apply (rule impI)+
    apply (rule FalseE)
    apply (erule exE)+
    apply (drule_tac x = aa in spec)
    apply (drule_tac x = b in spec)
    apply (drule_tac x = ba in spec)
    apply (rotate_tac -1, erule notE)
    apply (simp add: ledgra_upd_def)
    apply (subst ledgra_update_lem)
     apply (simp add: ledgra_at_def)
     apply blast
    apply (erule subst)
    apply (simp add: ledgra_at_def)
by force
qed


lemma update_empty_lem0: "xa \<in> (f(x := {})) y \<Longrightarrow> xa \<in> f y"
  by (simp, case_tac "x = y", simp+)


lemma ledger_del0: "Rep_ledger (lg x := {}) y \<subseteq> Rep_ledger lg y"
proof (rule subsetI, simp add: ledgra_upd_def)
  fix xa
  show "xa \<in> Rep_ledger (Abs_ledger ((Rep_ledger lg)(x := {}))) y \<Longrightarrow> xa \<in> Rep_ledger lg y"
  proof -
    assume a0:  "xa \<in> Rep_ledger (Abs_ledger ((Rep_ledger lg)(x := {}))) y"
    from a0 ledgra_update_lem have a1: "xa \<in> ((Rep_ledger lg)(x := {})) y" by simp
    with a0 show "xa \<in> Rep_ledger (Abs_ledger ((Rep_ledger lg)(x := {}))) y \<Longrightarrow>
               xa \<in> Rep_ledger lg y" 
      apply (rule_tac f = "\<lambda> y. Rep_ledger lg y" and x = x in update_empty_lem0)
      by assumption
  qed
qed

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


lemma ledger_to_loc_delete:   
  assumes a: "\<forall> l. finite {dl::(char list \<times> char list set) \<times> char list. l \<in> Rep_ledger lg dl}" 
      and b: "inj Actor"
  shows "(lg \<nabla> ((a, as), n)) = L \<Longrightarrow> l \<in> L \<Longrightarrow>
      ledger_to_loc (lg ((a, as), n) := L - {l}) =
       (ledger_to_loc lg)(l := ledger_to_loc lg l - {(y::actor \<times> actor set, x::char list). x = n})"
proof -
  assume a0: "(lg \<nabla> ((a, as), n)) = L" and a1: "l \<in> L"
  have a1a: "l \<in> Rep_ledger lg ((a, as), n)" 
    by (insert a0 a1, unfold ledgra_at_def, erule ssubst)
  have a1b: "ledger_to_loc lg l - {(y::actor \<times> actor set, x::char list). x = n} =
             ledger_to_loc lg l - {(y::actor \<times> actor set, x::char list). 
                      (y, x) \<in> ledger_to_loc lg l \<and> x = n}" by blast
  show "(lg \<nabla> ((a, as), n)) = L \<Longrightarrow> l \<in> L \<Longrightarrow> ledger_to_loc (lg ((a, as), n) := L - {l}) =
       (ledger_to_loc lg)(l := ledger_to_loc lg l - {(y::actor \<times> actor set, x::char list). x = n})"
  proof(rule ext, case_tac "\<forall> dl. dl \<noteq> ((a,as),n) \<longrightarrow> x \<notin> Rep_ledger lg dl")
    fix x
    assume A: "\<forall>dl::(char list \<times> char list set) \<times> char list. dl \<noteq> ((a, as), n) \<longrightarrow> x \<notin> Rep_ledger lg dl" 
    show "ledger_to_loc (lg ((a, as), n) := L - {l}) x =
       ((ledger_to_loc lg)(l := ledger_to_loc lg l - {(y::actor \<times> actor set, x::char list). x = n})) x"
    proof (case_tac "l = x", simp)
      assume lex: "l = x"
      show "ledger_to_loc (lg ((a, as), n) := L - {x}) x =
            ledger_to_loc lg x - {(y::actor \<times> actor set, x::char list). x = n}"
      proof -
        have b00: "(\<forall> b::(char list \<times> char list set) \<times> char list.
             x \<notin> ((Rep_ledger lg)(((a, as), n) := Rep_ledger lg ((a, as), n) - {x})) b)"
          by (rule allI, case_tac "b = ((a,as),n)", simp, simp add: A)
        have b0: "x \<notin> \<Union> (range(Rep_ledger(lg ((a, as), n) := L - {x})))"
          by (unfold ledgra_upd_def, subst ledgra_update_lem, rule disjI2, 
              rule inset_n_empty, rule a1a, insert a0, erule subst, unfold ledgra_at_def, 
              insert b00, blast)
        have b1: "ledger_to_loc (lg ((a, as), n) := L - {x}) x = {}" using b0 ledger_to_loc_def by simp
        have b2000: "x \<in> \<Union> (range (Rep_ledger lg))" 
          by (insert a1a, insert lex, force)
        have b200: "ledger_to_loc lg x = fmap data_trans {dl. x \<in> Rep_ledger lg dl}" 
          by (unfold ledger_to_loc_def, insert b2000, simp add: ledgra_at_def)
        have b21: "{dl::(char list \<times> char list set) \<times> char list. x \<in> Rep_ledger lg dl}
                   = {((a,as),n)}" 
          by (rule equalityI, insert A, blast, insert a1a, insert lex, simp)
        have b22: "{data_trans ((a,as),n)} = fmap data_trans {((a,as),n)}" 
           by (rule sym, rule fmap_lem_one) 
        have b20: "ledger_to_loc lg x = {data_trans ((a,as),n)}"
          by (subst b200, subst b22, subst b21, rule refl)
        have b2: "ledger_to_loc lg x - {(y::actor \<times> actor set, x::char list). x = n} = {}" 
               by (subst b20, simp add: data_trans_def)
        show ?thesis by (subst b1, subst b2, rule refl)
      qed
    next assume lnex: "l \<noteq> x" show 
     "ledger_to_loc (lg ((a, as), n) := L - {l}) x =
    ((ledger_to_loc lg)(l := ledger_to_loc lg l - {(y::actor \<times> actor set, x::char list). x = n})) x"
      proof (case_tac "x \<in> Rep_ledger lg ((a,as),n)")
        assume b3: "x \<in> Rep_ledger lg ((a,as),n)"
          have b300: "x \<in> \<Union> (range (Rep_ledger lg))" 
             by (insert a1a, insert b3, force)
          have b30: "x \<in> Rep_ledger (lg ((a,as),n):= L - {l})((a,as),n)" 
            by (insert lnex, insert b3, insert a0, unfold ledgra_upd_def, subst ledgra_update_lem,
                  rule disjI2, erule inset_n_empty, simp add: ledgra_at_def)
          have b3000: "x \<in> \<Union> (range (Rep_ledger (lg ((a, as), n) := L - {l})))"
            by (insert b300, insert b30, force)
          have b31a: "ledger_to_loc (lg ((a, as), n) := L - {l}) x =
                   fmap data_trans {dl. x \<in> Rep_ledger (lg ((a,as),n):= (L - {l})) dl}"
            by (insert b3000, insert lnex, insert A, unfold ledger_to_loc_def, simp add: ledgra_at_def)
          have b31b: "{dl. x \<in> Rep_ledger (lg ((a,as),n):= (L - {l})) dl} =
                       {dl. x \<in> ((Rep_ledger lg)(((a,as),n):= L - {l})) dl}" 
            by (unfold ledgra_upd_def, subst ledgra_update_lem, 
                rule disjI2, rule inset_n_empty, rule b3, rule refl)
          have b31c: "fmap data_trans {dl. x \<in> Rep_ledger (lg ((a,as),n):= (L - {l})) dl} =
                   fmap data_trans {dl. x \<in> ((Rep_ledger lg)(((a,as),n):= L - {l})) dl}"
            by (subst b31b, rule refl)
          have b32a: "{dl. x \<in> ((Rep_ledger lg)(((a, as), n) := L - {l})) dl} = {((a,as),n)}" 
          proof
            show "{((a, as), n)} \<subseteq> {dl. x \<in> ((Rep_ledger lg)(((a, as), n) := L - {l})) dl}"
              by (insert b3, insert lnex, simp, insert a0, simp add: ledgra_at_def)
          next show "{dl. x \<in> ((Rep_ledger lg)(((a, as), n) := L - {l})) dl} \<subseteq> {((a, as), n)}"
              by (insert A, insert lnex, insert b3, insert a0, unfold ledgra_at_def, 
                  erule subst, rule subsetI, drule CollectD, subgoal_tac "xa = ((a,as),n)",
                  simp, rule_tac Q = "x \<in> Rep_ledger lg ((a, as), n)" in contrapos_pp, assumption, 
                  drule_tac x = xa in spec, drule mp, assumption, drule b32a0, assumption,
                  erule_tac notE, assumption)
          qed
          have b32: "ledger_to_loc (lg ((a, as), n) := L - {l}) x =
                    fmap data_trans {((a,as),n)}" 
              by (subst b31a, subst b31c, subst b32a, rule refl)
          have b33: "((ledger_to_loc lg)(l := ledger_to_loc lg l - {(y::actor \<times> actor set, x::char list). x = n})) x
                    = (ledger_to_loc lg) x" by (insert lnex ,simp)
          have b34: "(ledger_to_loc lg) x = fmap data_trans {dl. x \<in> Rep_ledger lg dl}" 
            by (insert b300, insert b3, unfold ledger_to_loc_def ledgra_at_def, simp)
          have b35a: "{dl. x \<in> Rep_ledger lg dl} = {((a,as),n)}"
            by (insert b3, insert A, blast)
          have b35: "fmap data_trans {dl. x \<in> Rep_ledger lg dl} = fmap data_trans {((a,as),n)}"
            by (subst b35a, rule refl)
        show ?thesis
          by (subst b32, subst b33, subst b34, subst b35, rule refl)
      next assume b4: "x \<notin> Rep_ledger lg ((a,as),n)"
        have b40: "x \<notin> Rep_ledger (lg ((a,as),n) := L - {l})((a,as),n)" 
          by (insert a0, unfold ledgra_at_def, erule subst, unfold ledgra_upd_def,
              subst ledgra_update_lem, rule disjI2, rule inset_n_empty, rule a1a, 
              insert b4, erule contrapos_nn, simp)
        have b40b: "x \<notin> \<Union> (range (Rep_ledger lg))" 
          by (insert A, insert b4, force)
        have b40a: "x \<notin> \<Union> (range (Rep_ledger (lg ((a,as),n) := L - {l})))" 
          by (insert b40b, insert a0, unfold ledgra_at_def, erule subst, unfold ledgra_upd_def,
              subst ledgra_update_lem, rule disjI2, rule inset_n_empty, rule a1a, simp) 
        have b41: "ledger_to_loc (lg ((a, as), n) := L - {l}) x = {}" 
          by (insert b40a, unfold ledger_to_loc_def, simp)
        have b420: "((ledger_to_loc lg)(l := ledger_to_loc lg l - {(y::actor \<times> actor set, x::char list). x = n})) x
                   = (ledger_to_loc lg) x"
          by (insert lnex ,simp)
        have b42:  "((ledger_to_loc lg)(l := ledger_to_loc lg l - {(y::actor \<times> actor set, x::char list). x = n})) x
                   = {}" 
          by (subst b420, insert b40b, simp add: ledger_to_loc_def) 
        show ?thesis
          by (subst b41, subst b42, rule refl)
      qed
    qed
  next fix x
    assume B: "\<not> (\<forall>dl::(char list \<times> char list set) \<times> char list. dl \<noteq> ((a, as), n) \<longrightarrow> x \<notin> Rep_ledger lg dl)"
    show "ledger_to_loc (lg ((a, as), n) := L - {l}) x =
       ((ledger_to_loc lg)(l := ledger_to_loc lg l - {(y::actor \<times> actor set, x::char list). x = n})) x"
    proof -
      have B0: "(\<exists> dl. dl \<noteq> ((a, as), n) \<and> x \<in> Rep_ledger lg dl)" using B by blast
      show ?thesis 
      proof (case_tac "l = x", simp)
        assume lex: "l = x"
        show "ledger_to_loc (lg ((a, as), n) := L - {x}) x =
              ledger_to_loc lg x - {(y::actor \<times> actor set, x::char list). x = n}"
        proof -
          have c000: "x \<in> Rep_ledger lg ((a,as),n)"
            by (insert a0, insert a1, insert lex, simp add: ledgra_at_def)
          have c00: "x \<in> \<Union> (range (Rep_ledger lg))" 
              by (insert a1a, insert lex, force)
          have c0: "x \<in> \<Union> (range(Rep_ledger(lg ((a, as), n) := L - {x})))"
            by (unfold ledgra_upd_def, subst ledgra_update_lem, rule disjI2, rule inset_n_empty, 
                rule a1a, insert B0, erule exE, insert a0, erule subst, unfold ledgra_at_def, force)
          have c1: "ledger_to_loc (lg ((a, as), n) := L - {x}) x =
                    fmap data_trans {dl. x \<in> Rep_ledger (lg ((a,as),n):= (L - {l})) dl}"
            by (insert c0, insert lex, unfold ledger_to_loc_def, simp add: ledgra_at_def)
          have c20: "{dl. x \<in> Rep_ledger (lg ((a,as),n):= (L - {l})) dl} =
                       {dl. x \<in> ((Rep_ledger lg)(((a,as),n):= L - {l})) dl}"
            by (unfold ledgra_upd_def, subst ledgra_update_lem, rule disjI2, rule inset_n_empty,
                   rule c000, rule refl)
          have c2: "ledger_to_loc (lg ((a, as), n) := L - {x}) x =
                     fmap data_trans  {dl. x \<in> ((Rep_ledger lg)(((a,as),n):= L - {l})) dl}"
            by (subst c1, subst c20, rule refl)
          have c30: "ledger_to_loc lg x - {(y::actor \<times> actor set, x::char list). x = n} =
                    fmap data_trans {dl. x \<in> Rep_ledger lg dl} - {(y,x). x = n}"
            by (insert c00, unfold ledger_to_loc_def, simp add: ledgra_at_def)
          have c3000: "fmap data_trans {dl. x \<in> Rep_ledger lg dl} - {(y,x). x = n} = 
           fmap data_trans {dl. x \<in> Rep_ledger lg dl} - 
               {(y,z). (y,z) \<in> fmap data_trans {dl. x \<in> Rep_ledger lg dl} \<and> z = n }"
            by blast
          have c30a: "{(y,z). (y,z) \<in> fmap data_trans {dl. x \<in> Rep_ledger lg dl} \<and> z = n } =
                      fmap data_trans {dl. x \<in> Rep_ledger lg dl \<and> snd dl = n}"
            by (subst fmap_set_rep', insert a, erule spec, subst fmap_set_rep',
                rule_tac B = "{dl. x \<in> Rep_ledger lg dl}" in finite_subset, blast, erule spec,
                unfold data_trans_def, rule equalityI, force, force)
          have c30b: "fmap data_trans {dl. x \<in> Rep_ledger lg dl} - 
               {(y,z). (y,z) \<in> fmap data_trans {dl. x \<in> Rep_ledger lg dl} \<and> z = n } =
               fmap data_trans ({dl. x \<in> Rep_ledger lg dl} - {dl. x \<in> Rep_ledger lg dl \<and> snd dl = n})"
            by (subst c30a, rule fmap_set_del_set, insert a, erule spec, rule inj_inj_on,
                  rule inj_data_trans, rule b, blast)
          have c30c: "{dl. x \<in> Rep_ledger lg dl \<and> snd dl = n}= 
                      {((a,as),n)}" 
          proof 
            show "{((a, as), n)} \<subseteq> {dl. x \<in> Rep_ledger lg dl \<and> snd dl = n}"
              by (insert c000, simp)
          next show "{dl. x \<in> Rep_ledger lg dl \<and> snd dl = n} \<subseteq> {((a, as), n)}"
             by (insert c000, rule subsetI, subgoal_tac "xa = ((a,as),n)", simp,
              drule CollectD, case_tac xa, simp,
              rule_tac dl = aa and dl' = "(a,as)" in ledger_to_loc_data_unique,
               erule conjE, erule inset_n_empty, erule conjE, rule inset_n_empty, simp)
            qed
          have c300: "fmap data_trans {dl. x \<in> Rep_ledger lg dl} - {(y,x). x = n} =
                      fmap data_trans ({dl. x \<in> Rep_ledger lg dl} - {((a,as),n)})"
            by (subst c3000, subst c30b, subst c30c, rule refl)            
          have c3: "ledger_to_loc lg x - {(y::actor \<times> actor set, x::char list). x = n} =
                   fmap data_trans ({dl. x \<in> Rep_ledger lg dl} - {((a,as),n)})" 
            by (subst c30, subst c300, rule refl)
          have c4: "{dl. x \<in> ((Rep_ledger lg)(((a,as),n):= L - {l})) dl} =
                    {dl. x \<in> Rep_ledger lg dl} - {((a,as),n)}"
            by (insert a0, unfold ledgra_at_def, erule subst, insert lex, simp, blast)
          show ?thesis
            by (subst c2, subst c3, subst c4, rule refl)
        qed
      next assume lnex: "l \<noteq> x"
        show "ledger_to_loc (lg ((a, as), n) := L - {l}) x =
    ((ledger_to_loc lg)(l := ledger_to_loc lg l - {(y::actor \<times> actor set, x::char list). x = n})) x"
        proof -
          have d3000: "x \<in> \<Union>(range (Rep_ledger (lg ((a, as), n) := L - {l})))"
            apply (insert B0)
            by (metis Union_iff a0 a1 fun_upd_apply insert_absorb insert_not_empty 
                ledgra_at_def ledgra_upd_def ledgra_update_lem rangeI)
          have d300: "x \<in> \<Union> (range (Rep_ledger (lg)))"
            by (insert B0, insert d3000, force)
          have d4000: "ledger_to_loc (lg ((a, as), n) := L - {l}) x =
                    fmap data_trans {dl. x \<in> Rep_ledger (lg ((a, as), n) := L - {l}) dl}"
            by (insert d3000, unfold ledger_to_loc_def, simp add: ledgra_at_def)
          have d400: "{dl. x \<in> Rep_ledger (lg ((a,as),n):= (L - {l})) dl} =
                       {dl. x \<in> ((Rep_ledger lg)(((a,as),n):= L - {l})) dl}" 
            by (unfold ledgra_upd_def, subst ledgra_update_lem, rule disjI2, rule inset_n_empty,
                rule a1a, rule refl)
          have d40: "ledger_to_loc (lg ((a, as), n) := L - {l}) x =
                     fmap data_trans {dl. x \<in> ((Rep_ledger lg)(((a,as),n):= L - {l})) dl}" 
            by (subst d4000, subst d400, rule refl)
          have d4: "x \<in> Rep_ledger lg ((a, as), n) \<Longrightarrow> {dl. x \<in> ((Rep_ledger lg)(((a,as),n):= L - {l})) dl} =
                     {dl. x \<in> (Rep_ledger lg) dl}"
            by (insert lnex, insert a0, insert a1, erule subst, simp add: ledgra_at_def, blast)
          have d5000: "((ledger_to_loc lg)(l := ledger_to_loc lg l - {(y::actor \<times> actor set, x::char list). x = n})) x
                   = (ledger_to_loc lg) x"
            by (insert lnex, simp)
          have d500: "(ledger_to_loc lg) x = fmap data_trans {dl. x \<in> Rep_ledger lg dl}" 
            by (insert d300, insert a1a, unfold ledger_to_loc_def ledgra_at_def, simp)
          show ?thesis
            apply (subst d40, subst d5000, subst d500, case_tac "x \<in> Rep_ledger lg ((a, as), n)",
                insert d4, drule meta_mp, assumption, erule ssubst, rule refl)
            by (metis Diff_iff a0 fun_upd_apply ledgra_at_def)
      qed
  qed
qed
qed
qed

definition ref_map :: "[RRLoopFour.infrastructure, 
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