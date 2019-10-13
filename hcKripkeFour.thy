theory hcKripkeFour
imports RRLoopFour
begin

locale scenarioHCKripkeFour = scenarioHCKripkeThree +
fixes hc_actorsF :: "identity set"
defines hc_actorsF_def: "hc_actorsF \<equiv> {''Patient'', ''Doctor''}"
fixes hc_locationsF :: "location set"
defines hc_locationsF_def: "hc_locationsF \<equiv> 
          {Location 0, Location 1, Location 2, Location 3}"

fixes sphoneF :: "location"
defines sphoneF_def: "sphoneF \<equiv> Location 0"
fixes homeF :: "location"
defines homeF_def: "homeF \<equiv> Location 1"
fixes hospitalF :: "location"
defines hospitalF_def: "hospitalF \<equiv> Location 2"
fixes cloudF :: "location"
defines cloudF_def: "cloudF \<equiv> Location 3"

fixes global_policyF :: "[infrastructure, identity] \<Rightarrow> bool"
defines global_policyF_def: "global_policyF I a \<equiv> a \<notin> hc_actorsF 
                 \<longrightarrow> \<not>(enables I cloudF (Actor a) put)"  

fixes ex_credsF :: "actor \<Rightarrow> (string set * string set)"
defines ex_credsF_def: "ex_credsF \<equiv> (\<lambda> x. if x = Actor ''Patient'' then 
                         ({''PIN'',''skey''}, {}) else 
                            (if x = Actor ''Doctor'' then
                                ({''PIN''},{}) else ({},{})))"

fixes ex_locsF :: "location \<Rightarrow> string"
defines "ex_locsF \<equiv>  (\<lambda> x.  if x = cloudF then ''free'' else '''')"

fixes ex_ledger :: "ledger"
defines ex_ledger_def: "ex_ledger \<equiv>
          (Abs_ledger 
          (\<lambda> (l, d). if (d = ''42'' \<and> l = (''Patient'',{''Doctor''})) then {cloudF} else {}))"


fixes ex_locF_ass :: "location \<Rightarrow> identity set"
defines ex_locF_ass_def: "ex_locF_ass \<equiv>
          (\<lambda> x.  if x = homeF then {''Patient''}  
                 else (if x = hospitalF then {''Doctor'', ''Eve''} 
                       else {}))"
fixes ex_graphF :: "igraph"
defines ex_graphF_def: "ex_graphF \<equiv> Lgraph 
     {(homeF, cloudF), (sphoneF, cloudF), (cloudF,hospitalF)}
     ex_locF_ass
     ex_credsF ex_locsF ex_ledger"

fixes ex_graphF' :: "igraph"
defines ex_graphF'_def: "ex_graphF' \<equiv> Lgraph 
     {(homeF, cloudF), (sphoneF, cloudF), (cloudF,hospitalF)}
       (\<lambda> x. if x = cloudF then {''Patient''} else 
           (if x = hospitalF then {''Doctor'',''Eve''} else {})) 
     ex_credsF ex_locsF ex_ledger"

fixes ex_graphF'' :: "igraph"
defines ex_graphF''_def: "ex_graphF'' \<equiv> Lgraph 
     {(homeF, cloudF), (sphoneF, cloudF), (cloudF,hospitalF)}
       (\<lambda> x. if x = cloudF then {''Patient'', ''Eve''} else 
           (if x = hospitalF then {''Doctor''} else {})) 
     ex_credsF ex_locsF ex_ledger"

fixes local_policiesF :: "[igraph, location] \<Rightarrow> policy set"
defines local_policiesF_def: "local_policiesF G \<equiv> 
    (\<lambda> x. if x = homeF then
        {(\<lambda> y. True, {put,get,move,eval})}
          else (if x = sphoneF then 
             {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
                else (if x = cloudF then
                {(\<lambda> y. True, {put,get,move,eval})}
                       else (if x = hospitalF then
                {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospitalF) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} else {}))))"

fixes rmapF :: "RRLoopFour.infrastructure \<Rightarrow> RRLoopThree.infrastructure"
defines rmapF_def:
"rmapF I \<equiv> ref_map I local_policiesR"

fixes hc_scenarioF :: "infrastructure"
defines hc_scenarioF_def:
"hc_scenarioF \<equiv> Infrastructure ex_graphF local_policiesF"

fixes IhcF :: "infrastructure set"
defines IhcF_def:
  "IhcF \<equiv> {hc_scenarioF}"

fixes hc_scenarioF' :: "infrastructure"
defines hc_scenarioF'_def:
"hc_scenarioF' \<equiv> Infrastructure ex_graphF' local_policiesF"

fixes HCF' :: "infrastructure set"
defines HCF'_def:
  "HCF' \<equiv> {hc_scenarioF'}"

fixes hc_scenarioF'' :: "infrastructure"
defines hc_scenarioF''_def:
"hc_scenarioF'' \<equiv> Infrastructure ex_graphF'' local_policiesF"

fixes HCF'' :: "infrastructure set"
defines HCF''_def:
  "HCF'' \<equiv> {hc_scenarioF''}"

fixes hc_statesF
defines hc_statesF_def: "hc_statesF \<equiv> { I. hc_scenarioF \<rightarrow>\<^sub>i* I }"

fixes hc_KripkeF
defines "hc_KripkeF \<equiv> Kripke hc_statesF {hc_scenarioF}"

fixes shcF
defines "shcF \<equiv> {x. \<not> (global_policyF x ''Eve'')}"  

assumes no_insider: "inj Actor"

begin

 lemma same_nodes0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> nodes(graphI z) = nodes(graphI z')"   
    apply clarify
  apply (erule RRLoopFour.state_transition_in.cases)
  by (simp add: move_graph_a_def atI_def actors_graph_def nodes_def)+

lemma same_nodes: "(hc_scenarioF, s) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
\<Longrightarrow> RRLoopFour.nodes (graphI hc_scenarioF) = RRLoopFour.nodes (graphI s)"
  apply (erule rtrancl_induct)
   apply (rule refl)
  apply (drule CollectD)
    apply simp
    apply (drule same_nodes0)
  by simp  

(* lgra is obsolete: need to adapt to ledger
lemma finite_data_imp0: 
"(hc_scenarioF, I) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*  \<Longrightarrow>
((\<forall>l::location. (finite (RRLoopFour.lgra (RRLoopFour.graphI hc_scenarioF) l))) \<longrightarrow>
(\<forall>l::location. (finite (RRLoopFour.lgra (RRLoopFour.graphI I) l))))"
    apply (erule rtrancl_induct)  
   apply simp+
  apply clarify
  apply (erule state_transition_in.cases) 
  apply (simp add: move_graph_a_def)
by simp+
*)
lemma finite_data_imp0: 
"(hc_scenarioF, I) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*  \<Longrightarrow>
(\<forall>l::location. (finite {dl::(char list \<times> char list set) \<times> char list. 
                          l \<in> Rep_ledger (ledgra (RRLoopFour.graphI hc_scenarioF)) dl})) \<longrightarrow>
(\<forall>l::location. finite {dl::(char list \<times> char list set) \<times> char list. 
                          l \<in> Rep_ledger (ledgra (RRLoopFour.graphI I)) dl})"
    apply (erule rtrancl_induct)  
   apply simp+
  apply clarify
  apply (erule state_transition_in.cases) 
(* move *)
      apply (simp add: move_graph_a_def)
(* get *)
     apply simp
     apply (rotate_tac 2)
     apply (drule_tac x = l in spec) 
     apply (case_tac "l = la")
      apply (rotate_tac -1)
  apply (erule subst)
      apply (subst ledgra_insert)
        apply (simp add: ledgra_at_def)
  apply assumption
      apply (simp add: finite_insert)
     apply (subst ledgra_insert0)
       apply (simp add: ledgra_at_def)
  apply assumption+
(* delete *)
  prefer 2
    apply simp
    apply (rotate_tac 2)
    apply (drule_tac x = l in spec)
    apply (rotate_tac -1)
    apply (rule finite_subset)
     prefer 2
     apply assumption
    apply (rule subsetI)
    apply clarify
    apply (case_tac "((aa, b), ba) = ((a, as), n)")
    
  apply (rotate_tac -1)
  apply (erule subst)
    apply (simp add: ledgra_at_def)
 
  sorry

lemma ifte_post: "h \<in> (if B then {h} else {}) \<Longrightarrow> B"
  apply (case_tac B, assumption)
by simp

lemma finite_data0: 
"(hc_scenarioF, I) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*  \<Longrightarrow>
(\<forall>l::location. finite {dl::(char list \<times> char list set) \<times> char list. 
                          l \<in> Rep_ledger (ledgra (RRLoopFour.graphI I)) dl})"
  apply (drule finite_data_imp0)
  apply (erule mp)
  apply (simp add: hc_scenarioF_def ex_graphF_def ex_locsF_def ex_ledger_def Abs_ledger_inverse)
  apply (rule allI)
  apply (case_tac "l = cloudF")
   apply simp
   apply (subgoal_tac "{dl::(char list \<times> char list set) \<times> char list.
         cloudF
         \<in> (case dl of
             (l::char list \<times> char list set, d::char list) \<Rightarrow>
               if d = ''42'' \<and> l = (''Patient'', {''Doctor''}) then {cloudF} else {})}
          = {((''Patient'', {''Doctor''}), ''42'')}")
    apply simp
(* *)
   apply (rule equalityI)
    apply (rule subsetI, drule CollectD)
    apply simp
    apply (case_tac x)
  apply simp
    apply (drule ifte_post)
    apply (erule conjE)
  apply (rule conjI, assumption, assumption)
(* *)
  apply (rule subsetI)
  apply simp
(* *)
   apply (subgoal_tac "{dl::(char list \<times> char list set) \<times> char list.
         l
         \<in> (case dl of
             (l::char list \<times> char list set, d::char list) \<Rightarrow>
               if d = ''42'' \<and> l = (''Patient'', {''Doctor''}) then {cloudF} else {})}
          = {}")
   apply (erule ssubst)
   apply (rule finite.emptyI)
by simp

lemma finite_label_imp0: "(hc_scenarioF, I) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*  \<Longrightarrow>
(\<forall>l::location. \<forall> a :: string. \<forall> d :: string. 
                          l \<in> Rep_ledger (ledgra (RRLoopFour.graphI hc_scenarioF)) ((a,as),d)
                       \<longrightarrow> finite as) \<longrightarrow>
(\<forall>l::location.  \<forall> a :: string. \<forall> d :: string. 
                          l \<in> Rep_ledger (ledgra (RRLoopFour.graphI I)) ((a,as),d)
                       \<longrightarrow> finite as)"
  sorry

lemma finite_label0[rule_format]: "(hc_scenarioF, I) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*  \<Longrightarrow>
(\<forall>l::location.  \<forall> a :: string. \<forall> d :: string. 
                          l \<in> Rep_ledger (ledgra (RRLoopFour.graphI I)) ((a,as),d)
                       \<longrightarrow> finite as)"
  sorry


(*
"(hc_scenarioF, I) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*  \<Longrightarrow>
\<forall>l::location. finite (RRLoopFour.lgra (RRLoopFour.graphI I) l)"
  apply (drule finite_data_imp0)
by (simp add: hc_scenarioR_def ex_graphR_def ex_locsR_def)
*)

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

lemma refmapThree_lem: "\<forall>s::RRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>s'::RRLoopFour.infrastructure. s \<rightarrow>\<^sub>n s' \<longrightarrow> rmapF s \<rightarrow>\<^sub>n rmapF s')"
  apply clarify
  apply (subgoal_tac "nodes(graphI hc_scenarioF) = nodes(graphI s)")
   prefer 2
   apply (erule same_nodes)
  apply (subgoal_tac "delta hc_scenarioF = delta s")
  prefer 2
  apply (erule init_state_policy)
  apply (erule state_transition_in.cases) 
proof -
(* move *)
  show "\<And>(s::RRLoopFour.infrastructure) (s'::RRLoopFour.infrastructure) (G::RRLoopFour.igraph)
       (I::RRLoopFour.infrastructure) (a::char list) (l::location) (l'::location)
       I'::RRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopFour.nodes (RRLoopFour.graphI hc_scenarioF) = RRLoopFour.nodes (RRLoopFour.graphI s) \<Longrightarrow>
       RRLoopFour.delta hc_scenarioF = RRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> RRLoopFour.nodes G \<Longrightarrow>
       l' \<in> RRLoopFour.nodes G \<Longrightarrow>
       a \<in> RRLoopFour.actors_graph (RRLoopFour.graphI I) \<Longrightarrow>
       RRLoopFour.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       RRLoopFour.infrastructure.Infrastructure (RRLoopFour.move_graph_a a l l' (RRLoopFour.graphI I))
        (RRLoopFour.delta I) \<Longrightarrow>
       rmapF s \<rightarrow>\<^sub>n rmapF s'"
  apply (rule_tac I = "rmapF s" and I' = "rmapF s'" and l = l and l' = l' 
                             and  h = a
 in RRLoopThree.state_transition_in.move)
  apply (rule refl)
            apply (simp add: rmapF_def ref_map_def atI_def RRLoopThree.atI_def)
           apply (simp add: rmapF_def ref_map_def nodes_def RRLoopThree.nodes_def)
           apply (simp add: rmapF_def ref_map_def nodes_def RRLoopThree.nodes_def)
         apply (simp add: rmapF_def ref_map_def actors_graph_def RRLoopThree.actors_graph_def)
         apply (rule_tac x = l in exI)
         apply (simp add: nodes_def RRLoopThree.nodes_def atI_def)
  prefer 2
     apply (simp add: rmapF_def ref_map_def move_graph_a_def RRLoopThree.move_graph_a_def)
(* enables move *)
  apply (simp add: rmapF_def ref_map_def enables_def RRLoopThree.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policiesR_def local_policiesF_def hospitalR_def sphoneF_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def
                 atI_def RRLoopThree.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
  apply (drule sym)
  apply (simp add: hc_scenarioF_def local_policiesR_def local_policiesF_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
         apply (simp add: has_def RRLoopThree.has_def atI_def 
                RRLoopThree.credentials_def RRLoopFour.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioF_def local_policiesF_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
         apply (simp add: has_def RRLoopThree.has_def atI_def 
                RRLoopThree.credentials_def RRLoopFour.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioF_def local_policiesF_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
         apply (simp add: has_def RRLoopTwo.has_def atI_def 
                RRLoopThree.credentials_def RRLoopFour.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioF_def local_policiesF_def)
        apply (simp add: hc_scenarioF_def local_policiesF_def ex_graphF_def RRLoopFour.nodes_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
  apply (subgoal_tac "RRLoopFour.nodes (RRLoopFour.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: local_policiesR_def ex_graphF_def RRLoopFour.nodes_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
  apply (simp add: hospitalR_def sphoneR_def RRLoopFour.nodes_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
   apply (simp add: local_policiesF_def ex_graphF_def RRLoopFour.nodes_def)
   apply (simp add: hospitalR_def sphoneR_def RRLoopFour.nodes_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
  by blast
(* get *)
next show "\<And>(s::RRLoopFour.infrastructure) (s'::RRLoopFour.infrastructure) (G::RRLoopFour.igraph)
       (I::RRLoopFour.infrastructure) (a::char list) (l::location) (l'::location) (a'::char list)
       (as::char list set) (n::char list) (L::location set) I'::RRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopFour.nodes (RRLoopFour.graphI hc_scenarioF) = RRLoopFour.nodes (RRLoopFour.graphI s) \<Longrightarrow>
       RRLoopFour.delta hc_scenarioF = RRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> RRLoopFour.nodes G \<Longrightarrow>
       l' \<in> RRLoopFour.nodes G \<Longrightarrow>
       RRLoopFour.enables I l (Actor a) get \<Longrightarrow>
       (ledgra G \<nabla> ((a', as), n)) = L \<Longrightarrow>
       l' \<in> L \<Longrightarrow>
       a \<in> as \<Longrightarrow>
       I' =
       RRLoopFour.infrastructure.Infrastructure
        (RRLoopFour.igraph.Lgraph (RRLoopFour.gra G) (RRLoopFour.agra G) (RRLoopFour.cgra G)
          (RRLoopFour.lgra G) (ledgra G ((a', as), n) := L \<union> {l}))
        (RRLoopFour.delta I) \<Longrightarrow>
       rmapF s \<rightarrow>\<^sub>n rmapF s'"
    apply (rule_tac I = "rmapF s" and I' = "rmapF s'" and l = l and h = a and l' = l' and 
                             h' = a' and  hs = "fmap Actor as" and  n = n
         in RRLoopThree.state_transition_in.get_data)
  apply (rule refl)
        apply (simp add: rmapF_def ref_map_def atI_def RRLoopThree.atI_def)
                apply (simp add: rmapF_def ref_map_def nodes_def RRLoopThree.nodes_def)
           apply (simp add: rmapF_def ref_map_def nodes_def RRLoopThree.nodes_def)
      prefer 2
    apply (simp add: rmapF_def ref_map_def)
       apply (rule ledgra_ledger_to_loc)
    apply (frule finite_data0)
    apply (erule spec)
    apply (simp add: ledger_to_loc_def)
(* *)
      prefer 2
      apply (rule fmap_lem_map)
       apply (erule_tac l = l' and a = a' and d = n in finite_label0)
    apply (simp add: ledgra_at_def, assumption)
     prefer 2
     apply (simp add: rmapF_def ref_map_def)
     apply (rule ledger_to_loc_insert)
    apply (rule allI)
       apply (frule finite_data0)
       apply (erule spec)
    apply assumption+
(* enables get*)
 apply (simp add: rmapF_def ref_map_def enables_def RRLoopThree.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policiesR_def local_policiesF_def hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def
                 atI_def RRLoopThree.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
     apply (drule sym)
  apply (simp add: hc_scenarioF_def local_policiesR_def local_policiesF_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
         apply (simp add: has_def RRLoopThree.has_def atI_def 
                RRLoopThree.credentials_def RRLoopFour.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioF_def local_policiesF_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
         apply (simp add: has_def RRLoopThree.has_def atI_def 
                RRLoopThree.credentials_def RRLoopFour.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
     apply (rule impI)+
(* *)
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioF_def local_policiesF_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
         apply (simp add: has_def RRLoopThree.has_def atI_def 
                RRLoopThree.credentials_def RRLoopFour.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioF_def local_policiesF_def)
        apply (simp add: hc_scenarioF_def local_policiesF_def ex_graphF_def RRLoopFour.nodes_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
  apply (subgoal_tac "RRLoopFour.nodes (RRLoopFour.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: hc_scenarioF_def local_policiesF_def ex_graphF_def RRLoopFour.nodes_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
    by blast 
(* eval *)
next show "\<And>(s::RRLoopFour.infrastructure) (s'::RRLoopFour.infrastructure) (G::RRLoopFour.igraph)
       (I::RRLoopFour.infrastructure) (a::char list) (l::location) (a'::char list) (as::char list set)
       (n::char list) (L::location set) (I'::RRLoopFour.infrastructure) f::RRLoopFour.label_fun.
       (hc_scenarioF, s) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopFour.nodes (RRLoopFour.graphI hc_scenarioF) = RRLoopFour.nodes (RRLoopFour.graphI s) \<Longrightarrow>
       RRLoopFour.delta hc_scenarioF = RRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       RRLoopFour.enables I l (Actor a) eval \<Longrightarrow>
       (ledgra G \<nabla> ((a', as), n)) = L \<Longrightarrow>
       a \<in> as \<or> a = a' \<Longrightarrow>
       I' =
       RRLoopFour.infrastructure.Infrastructure
        (RRLoopFour.igraph.Lgraph (RRLoopFour.gra G) (RRLoopFour.agra G) (RRLoopFour.cgra G)
          (RRLoopFour.lgra G) (ledgra G ((a', as), n) := {} f \<Updown> ((a', as), n) := L ))
        (RRLoopFour.delta I) \<Longrightarrow>
       rmapF s \<rightarrow>\<^sub>n rmapF s'"
    sorry
(* delete *)
next show "\<And>(s::RRLoopFour.infrastructure) (s'::RRLoopFour.infrastructure) (G::RRLoopFour.igraph)
       (I::RRLoopFour.infrastructure) (a::char list) (l::location) (L::location set) (as::char list set)
       (n::char list) I'::RRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopFour.nodes (RRLoopFour.graphI hc_scenarioF) = RRLoopFour.nodes (RRLoopFour.graphI s) \<Longrightarrow>
       RRLoopFour.delta hc_scenarioF = RRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopFour.graphI I \<Longrightarrow>
       a \<in> RRLoopFour.actors_graph G \<Longrightarrow>
       l \<in> RRLoopFour.nodes G \<Longrightarrow>
       l \<in> L \<Longrightarrow>
       (ledgra G \<nabla> ((a, as), n)) = L \<Longrightarrow>
       I' =
       RRLoopFour.infrastructure.Infrastructure
        (RRLoopFour.igraph.Lgraph (RRLoopFour.gra G) (RRLoopFour.agra G) (RRLoopFour.cgra G)
          (RRLoopFour.lgra G) (ledgra G ((a, as), n) := L - {l}))
        (RRLoopFour.delta I) \<Longrightarrow>
       rmapF s \<rightarrow>\<^sub>n rmapF s'"
    apply (rule_tac I = "rmapF s" and I' = "rmapF s'" and h = a and l = l and
                               hs = "fmap Actor as" and  n = n
         in RRLoopThree.state_transition_in.del_data)
  apply (rule refl)
        apply (simp add: rmapF_def ref_map_def atI_def RRLoopThree.actors_graph_def actors_graph_def
                        RRLoopThree.nodes_def nodes_def)
                apply (simp add: rmapF_def ref_map_def nodes_def RRLoopThree.nodes_def)
           apply (simp add: rmapF_def ref_map_def nodes_def RRLoopThree.nodes_def)
       apply (rule ledgra_ledger_to_loc)
    apply (frule finite_data0)
    apply (erule spec)
    apply (simp add: ledger_to_loc_def)
(* *)
    apply (simp add: rmapF_def ref_map_def)
    apply (rule ledger_to_loc_delete)
    apply (frule finite_data0)
    apply (rule allI)
    apply (erule spec)
    by (rule no_insider)
(* put *)
next show "\<And>(s::RRLoopFour.infrastructure) (s'::RRLoopFour.infrastructure) (G::RRLoopFour.igraph)
       (I::RRLoopFour.infrastructure) (a::char list) (l::location) (I'::RRLoopFour.infrastructure)
       (as::char list set) n::char list.
       (hc_scenarioF, s) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopFour.nodes (RRLoopFour.graphI hc_scenarioF) = RRLoopFour.nodes (RRLoopFour.graphI s) \<Longrightarrow>
       RRLoopFour.delta hc_scenarioF = RRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       RRLoopFour.enables I l (Actor a) put \<Longrightarrow>
       I' =
       RRLoopFour.infrastructure.Infrastructure
        (RRLoopFour.igraph.Lgraph (RRLoopFour.gra G) (RRLoopFour.agra G) (RRLoopFour.cgra G)
          (RRLoopFour.lgra G) (ledgra G ((a, as), n) := {l}))
        (RRLoopFour.delta I) \<Longrightarrow>
       rmapF s \<rightarrow>\<^sub>n rmapF s'"
    sorry
qed

theorem refmapThree: "hc_KripkeR  \<sqsubseteq>\<^sub>rmapF hc_KripkeF" 
proof (rule strong_mt', simp add: hc_KripkeF_def hc_KripkeR_def hc_statesR_def hc_statesF_def state_transition_refl_def, rule conjI)
  show "rmapF hc_scenarioF = hc_scenarioR"
    apply (simp add: rmapF_def ref_map_def hc_scenarioF_def hc_scenarioR_def ex_graphF_def ex_graphR_def
           homeF_def homeR_def cloudF_def cloudR_def sphoneF_def sphoneR_def hospitalF_def hospitalR_def
           ex_locF_ass_def ex_locR_ass_def ex_credsF_def ex_credsR_def ex_ledger_def ex_locsR_def)
    apply (rule conjI)
     apply (rule ext)
    apply (simp add: hospitalF_def hospitalR_def)
    apply (unfold ledger_to_loc_def data_trans_def dlm_to_dlm_def ledgra_at_def)
    apply (subgoal_tac "(\<lambda>(l::char list \<times> char list set, d::char list).
                         if d = ''42'' \<and> l = (''Patient'', {''Doctor''}) then {cloudF} else {})
     \<in> {ld::(char list \<times> char list set) \<times> char list \<Rightarrow> location set.
      \<forall>d::char list.
         (\<forall>l::char list \<times> char list set. ld (l, d) = {}) \<or>
         (\<exists>!l::char list \<times> char list set. ld (l, d) \<noteq> {})}")
     apply (drule Abs_ledger_inverse)
    apply (erule ssubst)
    apply (simp add: fmap_def cloudF_def)
    apply (rule ext)
    apply simp
     apply (rule impI)
    apply (subgoal_tac "{dl::(char list \<times> char list set) \<times> char list.
         Location (3::nat)
         \<in> (case dl of
             (l::char list \<times> char list set, d::char list) \<Rightarrow>
               if d = ''42'' \<and> l = (''Patient'', {''Doctor''}) then {cloudF} else {})}=
         {((''Patient'', {''Doctor''}),''42'')}")
    apply (rotate_tac 1)
      apply (erule ssubst)
    apply (subst fmap_lem_one)
      apply simp
      apply (rule fmap_lem_one)
     apply (rule equalityI)
      apply clarify
      apply (unfold cloudF_def)
      apply (drule ifte_post)
      apply (erule conjE, rule conjI, assumption, assumption)
     apply clarify
     apply simp
by simp
next show " \<forall>s::RRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::RRLoopFour.infrastructure, y::RRLoopFour.infrastructure). x \<rightarrow>\<^sub>i y}\<^sup>* \<longrightarrow>
       (\<forall>s'::RRLoopFour.infrastructure. s \<rightarrow>\<^sub>i s' \<longrightarrow> rmapF s \<rightarrow>\<^sub>i rmapF s')"
apply (unfold state_transition_infra_def RRLoopThree.state_transition_infra_def)
    by (rule refmapThree_lem)
qed

(* show attack "Eve can still do put at cloud and since we haven't
   forbidden it, she can overwrite Bob's entry "  *)
theorem hc_EFF: "hc_KripkeF \<turnstile> EF shcF"  
  sorry

theorem Ledger_con: "h \<in> hc_actorsF \<Longrightarrow> h' \<in> hc_actorsF \<Longrightarrow> l \<in> hc_locationsF \<Longrightarrow> 
                   l' \<in> hc_locationsF \<Longrightarrow> l \<in> (ledgra G  \<nabla> ((h, hs), n)) \<Longrightarrow> 
                   l' \<in> (ledgra G  \<nabla> ((h', hs'), n)) \<Longrightarrow> (h, hs) = (h', hs')"
  apply (simp add: ledgra_at_def)
  apply (subgoal_tac "Rep_ledger (ledgra G) \<in> {ld::(char list \<times> char list set) \<times> char list \<Rightarrow> location set.
        \<forall>d::char list.
           (\<forall>l::char list \<times> char list set. ld (l, d) = {}) \<or>
           (\<exists>!l:: (char list \<times> char list set). ld (l,d) \<noteq> {})}")
  prefer 2
   apply (rule Rep_ledger)
  apply simp
  apply (drule_tac x = n in spec)
  apply (erule disjE)
   apply blast
  apply (erule ex1E)
by blast

end

end
 