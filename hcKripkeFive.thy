theory hcKripkeFive
imports RRLoopFive
begin

locale scenarioHCKripkeFive = scenarioHCKripkeFour +
fixes hc_actorsV :: "identity set"
defines hc_actorsV_def: "hc_actorsV \<equiv> {''Patient'', ''Doctor''}"
fixes hc_locationsV :: "location set"
defines hc_locationsV_def: "hc_locationsV \<equiv> 
          {Location 0, Location 1, Location 2, Location 3}"

fixes sphoneV :: "location"
defines sphoneV_def: "sphoneV \<equiv> Location 0"
fixes homeV :: "location"
defines homeV_def: "homeV \<equiv> Location 1"
fixes hospitalV :: "location"
defines hospitalV_def: "hospitalV \<equiv> Location 2"
fixes cloudV :: "location"
defines cloudV_def: "cloudV \<equiv> Location 3"

fixes global_policyV :: "[infrastructure, identity] \<Rightarrow> bool"
defines global_policyV_def: "global_policyV I a \<equiv> a \<notin> hc_actorsV 
                 \<longrightarrow> \<not>(enables I cloudV (Actor a) put)"  

fixes ex_credsV :: "actor \<Rightarrow> (string set * string set)"
defines ex_credsV_def: "ex_credsV \<equiv> (\<lambda> x. if x = Actor ''Patient'' then 
                         ({''PIN'',''skey''}, {}) else 
                            (if x = Actor ''Doctor'' then
                                ({''PIN''},{}) else ({},{})))"

fixes ex_locsV :: "location \<Rightarrow> string"
defines "ex_locsV \<equiv>  (\<lambda> x.  if x = cloudV then ''free'' else '''')"

fixes ex_ledgerV :: "ledger"
defines ex_ledgerV_def: "ex_ledgerV \<equiv>
          (Abs_ledger 
          (\<lambda> (l, d). if (d = ''42'' \<and> l = (''Patient'',{''Doctor''})) then {cloudV} else {}))"


fixes ex_locV_ass :: "location \<Rightarrow> identity set"
defines ex_locV_ass_def: "ex_locV_ass \<equiv>
          (\<lambda> x.  if x = homeV then {''Patient''}  
                 else (if x = hospitalV then {''Doctor'', ''Eve''} 
                       else {}))"

fixes ex_graphV :: "igraph"
defines ex_graphV_def: "ex_graphV \<equiv> Lgraph 
     {(homeV, cloudV), (sphoneV, cloudV), (cloudV,hospitalV)}
     ex_locV_ass
     ex_credsV ex_locsV ex_ledgerV"

fixes ex_graphV' :: "igraph"
defines ex_graphV'_def: "ex_graphV' \<equiv> Lgraph 
     {(homeV, cloudV), (sphoneV, cloudV), (cloudV,hospitalV)}
       (\<lambda> x. if x = cloudV then {''Patient''} else 
           (if x = hospitalV then {''Doctor'',''Eve''} else {})) 
     ex_credsV ex_locsV ex_ledgerV"

fixes ex_graphV'' :: "igraph"
defines ex_graphV''_def: "ex_graphV'' \<equiv> Lgraph 
     {(homeV, cloudV), (sphoneV, cloudV), (cloudV,hospitalV)}
       (\<lambda> x. if x = cloudV then {''Patient'', ''Eve''} else 
           (if x = hospitalV then {''Doctor''} else {})) 
     ex_credsV ex_locsV ex_ledgerV"

fixes local_policiesV :: "[igraph, location] \<Rightarrow> policy set"
defines local_policiesV_def: "local_policiesV G \<equiv> 
    (\<lambda> x. if x = homeV then
        {(\<lambda> y. True, {put,get,move,eval})}
          else (if x = sphoneV then 
             {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
                else (if x = cloudV then
                {(\<lambda> y. True, {put,get,move,eval})}
                       else (if x = hospitalV then
                {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospitalV) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} else {}))))"

fixes rmapV :: "RRLoopFive.infrastructure \<Rightarrow> RRLoopFour.infrastructure"
defines rmapV_def:
"rmapV I \<equiv> ref_map I local_policiesF"

fixes hc_scenarioV :: "infrastructure"
defines hc_scenarioV_def:
"hc_scenarioV \<equiv> Infrastructure ex_graphV local_policiesV"

fixes IhcV :: "infrastructure set"
defines IhcV_def:
  "IhcV \<equiv> {hc_scenarioV}"

fixes hc_scenarioV' :: "infrastructure"
defines hc_scenarioV'_def:
"hc_scenarioV' \<equiv> Infrastructure ex_graphV' local_policiesV"

fixes HCV' :: "infrastructure set"
defines HCV'_def:
  "HCV' \<equiv> {hc_scenarioV'}"

fixes hc_scenarioV'' :: "infrastructure"
defines hc_scenarioV''_def:
"hc_scenarioV'' \<equiv> Infrastructure ex_graphV'' local_policiesV"

fixes HCV'' :: "infrastructure set"
defines HCV''_def:
  "HCV'' \<equiv> {hc_scenarioV''}"

fixes hc_statesV
defines hc_statesV_def: "hc_statesV \<equiv> { I. hc_scenarioV \<rightarrow>\<^sub>i* I }"

fixes hc_KripkeV
defines "hc_KripkeV \<equiv> Kripke hc_statesV {hc_scenarioV}"

fixes shcV
defines "shcV \<equiv> {x. \<not> (global_policyV x ''Eve'')}"  


begin
 lemma same_nodes0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> nodes(graphI z) = nodes(graphI z')"   
    apply clarify
  apply (erule RRLoopFive.state_transition_in.cases)
  by (simp add: move_graph_a_def atI_def actors_graph_def nodes_def)+

lemma same_nodes: "(hc_scenarioV, s) \<in> {(x::RRLoopFive.infrastructure, y::RRLoopFive.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
\<Longrightarrow> RRLoopFive.nodes (graphI hc_scenarioV) = RRLoopFive.nodes (graphI s)"
  apply (erule rtrancl_induct)
   apply (rule refl)
  apply (drule CollectD)
    apply simp
    apply (drule same_nodes0)
  by simp  

lemma finite_data_imp0: 
"(hc_scenarioV, I) \<in> {(x::RRLoopFive.infrastructure, y::RRLoopFive.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*  \<Longrightarrow>
(\<forall>l::location. (finite {dl::(char list \<times> char list set) \<times> char list. 
                          l \<in> Rep_ledger (ledgra (RRLoopFive.graphI hc_scenarioV)) dl})) \<longrightarrow>
(\<forall>l::location. finite {dl::(char list \<times> char list set) \<times> char list. 
                          l \<in> Rep_ledger (ledgra (RRLoopFive.graphI I)) dl})"
    apply (erule rtrancl_induct)  
   apply simp+
  apply clarify
  apply (erule state_transition_in.cases) 
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


lemma finite_data0: 
"(hc_scenarioV, I) \<in> {(x::RRLoopFive.infrastructure, y::RRLoopFive.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*  \<Longrightarrow>
(\<forall>l::location. finite {dl::(char list \<times> char list set) \<times> char list. 
                          l \<in> Rep_ledger (ledgra (RRLoopFive.graphI I)) dl})"
  apply (drule finite_data_imp0)
  apply (erule mp)
  apply (simp add: hc_scenarioV_def ex_graphV_def ex_locsV_def ex_ledgerV_def Abs_ledger_inverse)
  apply (rule allI)
  apply (case_tac "l = cloudV")
   apply simp
   apply (subgoal_tac "{dl::(char list \<times> char list set) \<times> char list.
         cloudV
         \<in> (case dl of
             (l::char list \<times> char list set, d::char list) \<Rightarrow>
               if d = ''42'' \<and> l = (''Patient'', {''Doctor''}) then {cloudV} else {})}
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
               if d = ''42'' \<and> l = (''Patient'', {''Doctor''}) then {cloudV} else {})}
          = {}")
   apply (erule ssubst)
   apply (rule finite.emptyI)
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


lemma refmapFour_lem: "\<forall>s::RRLoopFive.infrastructure.
       (hc_scenarioV, s) \<in> {(x::RRLoopFive.infrastructure, y::RRLoopFive.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>s'::RRLoopFive.infrastructure. s \<rightarrow>\<^sub>n s' \<longrightarrow> rmapV s \<rightarrow>\<^sub>n rmapV s')"
  apply clarify
  apply (subgoal_tac "nodes(graphI hc_scenarioV) = nodes(graphI s)")
   prefer 2
   apply (erule same_nodes)
  apply (subgoal_tac "delta hc_scenarioV = delta s")
  prefer 2
  apply (erule init_state_policy)
  apply (erule state_transition_in.cases) 
proof -
(* move *)
show "\<And>(s::RRLoopFive.infrastructure) (s'::RRLoopFive.infrastructure) (G::RRLoopFive.igraph)
       (I::RRLoopFive.infrastructure) (a::char list) (l::location) (l'::location)
       I'::RRLoopFive.infrastructure.
       (hc_scenarioV, s)
       \<in> {(x::RRLoopFive.infrastructure, y::RRLoopFive.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopFive.nodes (RRLoopFive.graphI hc_scenarioV) =
       RRLoopFive.nodes (RRLoopFive.graphI s) \<Longrightarrow>
       RRLoopFive.delta hc_scenarioV = RRLoopFive.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopFive.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> RRLoopFive.nodes G \<Longrightarrow>
       l' \<in> RRLoopFive.nodes G \<Longrightarrow>
       a \<in> RRLoopFive.actors_graph (RRLoopFive.graphI I) \<Longrightarrow>
       RRLoopFive.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       RRLoopFive.infrastructure.Infrastructure
        (RRLoopFive.move_graph_a a l l' (RRLoopFive.graphI I)) (RRLoopFive.delta I) \<Longrightarrow>
       rmapV s \<rightarrow>\<^sub>n rmapV s'"
  apply (rule_tac I = "rmapV s" and I' = "rmapV s'" and l = l and l' = l' 
                             and a = a
 in RRLoopFour.state_transition_in.move)
  apply (rule refl)
            apply (simp add: rmapV_def ref_map_def atI_def RRLoopFour.atI_def)
           apply (simp add: rmapV_def ref_map_def nodes_def RRLoopFour.nodes_def)
           apply (simp add: rmapV_def ref_map_def nodes_def RRLoopFour.nodes_def)
         apply (simp add: rmapV_def ref_map_def actors_graph_def RRLoopFour.actors_graph_def)
         apply (rule_tac x = l in exI)
         apply (simp add: nodes_def RRLoopFour.nodes_def atI_def)
  prefer 2
        apply (simp add: rmapV_def ref_map_def move_graph_a_def RRLoopFour.move_graph_a_def)
  apply (simp add: rmapV_def ref_map_def enables_def RRLoopFour.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policiesF_def local_policiesV_def hospitalF_def sphoneV_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def
                 atI_def RRLoopFour.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
  apply (drule sym)
  apply (simp add: hc_scenarioV_def local_policiesF_def local_policiesV_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
         apply (simp add: has_def RRLoopFour.has_def atI_def 
                RRLoopFour.credentials_def RRLoopFive.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioV_def local_policiesV_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
         apply (simp add: has_def RRLoopFour.has_def atI_def 
                RRLoopFour.credentials_def RRLoopFive.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioV_def local_policiesV_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeT_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopFour.credentials_def RRLoopFive.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioV_def local_policiesV_def)
        apply (simp add: hc_scenarioV_def local_policiesV_def ex_graphV_def RRLoopFive.nodes_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
  apply (subgoal_tac "RRLoopFive.nodes (RRLoopFive.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: local_policiesV_def ex_graphV_def RRLoopFive.nodes_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
  apply (simp add: hospitalF_def sphoneF_def RRLoopFive.nodes_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
   apply (simp add: local_policiesV_def ex_graphV_def RRLoopFive.nodes_def)
   apply (simp add: hospitalF_def sphoneF_def RRLoopFive.nodes_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
  by blast
(* get *)
next show "\<And>(s::RRLoopFive.infrastructure) (s'::RRLoopFive.infrastructure) (G::RRLoopFive.igraph)
       (I::RRLoopFive.infrastructure) (a::char list) (l::location) (l'::location) (a'::char list)
       (as::char list set) (n::char list) (L::location set) I'::RRLoopFive.infrastructure.
       (hc_scenarioV, s)
       \<in> {(x::RRLoopFive.infrastructure, y::RRLoopFive.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopFive.nodes (RRLoopFive.graphI hc_scenarioV) =
       RRLoopFive.nodes (RRLoopFive.graphI s) \<Longrightarrow>
       RRLoopFive.delta hc_scenarioV = RRLoopFive.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopFive.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> RRLoopFive.nodes G \<Longrightarrow>
       l' \<in> RRLoopFive.nodes G \<Longrightarrow>
       RRLoopFive.enables I l (Actor a) get \<Longrightarrow>
       (RRLoopFive.ledgra G \<nabla> ((a', as), n)) = L \<Longrightarrow>
       l' \<in> L \<Longrightarrow>
       a \<in> as \<Longrightarrow>
       I' =
       RRLoopFive.infrastructure.Infrastructure
        (RRLoopFive.igraph.Lgraph (RRLoopFive.gra G) (RRLoopFive.agra G) (RRLoopFive.cgra G)
          (RRLoopFive.lgra G) (RRLoopFive.ledgra G ((a', as), n) := L \<union> {l}))
        (RRLoopFive.delta I) \<Longrightarrow>
       rmapV s \<rightarrow>\<^sub>n rmapV s'"
    apply (rule_tac I = "rmapV s" and I' = "rmapV s'" and l = l and a = a and l' = l' and 
                                  a' = a' and  as = as and n = n
         in RRLoopFour.state_transition_in.get_data)
  apply (rule refl)
        apply (simp add: rmapV_def ref_map_def atI_def RRLoopFour.atI_def)
                apply (simp add: rmapV_def ref_map_def nodes_def RRLoopFour.nodes_def)
          apply (simp add: rmapV_def ref_map_def nodes_def RRLoopFour.nodes_def) 
      prefer 2
          apply (simp add: rmapV_def ref_map_def)
(* *)
      prefer 2
      apply (simp add: rmapV_def ref_map_def)
     prefer 2
      apply (simp add: rmapV_def ref_map_def)
     prefer 2
      apply (simp add: rmapV_def ref_map_def)
(* enables get*)
 apply (simp add: rmapV_def ref_map_def enables_def RRLoopFour.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policiesF_def local_policiesV_def hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def
                 atI_def RRLoopFour.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
     apply (drule sym)
  apply (simp add: hc_scenarioV_def local_policiesV_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
         apply (simp add: has_def RRLoopFour.has_def atI_def 
                RRLoopFour.credentials_def RRLoopFive.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioV_def local_policiesV_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
         apply (simp add: has_def RRLoopFour.has_def atI_def 
                RRLoopFour.credentials_def RRLoopFive.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
     apply (rule impI)+
(* *)
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioV_def local_policiesV_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
         apply (simp add: has_def RRLoopFour.has_def atI_def 
                RRLoopFour.credentials_def RRLoopFive.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioV_def local_policiesV_def)
        apply (simp add: hc_scenarioV_def local_policiesV_def ex_graphV_def RRLoopFive.nodes_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
  apply (subgoal_tac "RRLoopFive.nodes (RRLoopFive.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: hc_scenarioV_def local_policiesV_def ex_graphV_def RRLoopFive.nodes_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
    by blast 
(* eval *)
next show "\<And>(s::RRLoopFive.infrastructure) (s'::RRLoopFive.infrastructure) (G::RRLoopFive.igraph)
       (I::RRLoopFive.infrastructure) (a::char list) (l::location) (a'::char list)
       (as::char list set) (n::char list) (L::location set) (I'::RRLoopFive.infrastructure)
       f::label_fun.
       (hc_scenarioV, s)
       \<in> {(x::RRLoopFive.infrastructure, y::RRLoopFive.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopFive.nodes (RRLoopFive.graphI hc_scenarioV) =
       RRLoopFive.nodes (RRLoopFive.graphI s) \<Longrightarrow>
       RRLoopFive.delta hc_scenarioV = RRLoopFive.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopFive.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       RRLoopFive.enables I l (Actor a) eval \<Longrightarrow>
       (RRLoopFive.ledgra G \<nabla> ((a', as), n)) = L \<Longrightarrow>
       a \<in> as \<or> a = a' \<Longrightarrow>
       I' =
       RRLoopFive.infrastructure.Infrastructure
        (RRLoopFive.igraph.Lgraph (RRLoopFive.gra G) (RRLoopFive.agra G) (RRLoopFive.cgra G)
          (RRLoopFive.lgra G) (RRLoopFive.ledgra G ((a', as), n) := {} f \<Updown> ((a', as), n) := L))
        (RRLoopFive.delta I) \<Longrightarrow>
       rmapV s \<rightarrow>\<^sub>n rmapV s'"
    apply (rule_tac I = "rmapV s" and I' = "rmapV s'" and l = l and a = a and 
                     a' = a' and as = as and L = L and n = n 
           in RRLoopFour.state_transition_in.process)
  apply (rule refl)
        apply (simp add: rmapV_def ref_map_def atI_def RRLoopFour.atI_def)
                apply (simp add: rmapV_def ref_map_def nodes_def RRLoopFour.nodes_def)
      prefer 2
       apply (simp add: rmapV_def ref_map_def)
      prefer 2
      apply (simp add: rmapV_def ref_map_def)
     prefer 2
     apply (simp add: rmapV_def ref_map_def secure_process_def)
    prefer 2
(* enables eval *)
 apply (simp add: rmapV_def ref_map_def enables_def RRLoopFour.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policiesF_def local_policiesV_def hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def
                 atI_def RRLoopFour.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
  apply (drule sym)
  apply (simp add: hc_scenarioV_def local_policiesV_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
         apply (simp add: has_def RRLoopFour.has_def atI_def 
                RRLoopFour.credentials_def RRLoopFive.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioV_def local_policiesV_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
         apply (simp add: has_def RRLoopFour.has_def atI_def 
                RRLoopFour.credentials_def RRLoopFive.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioV_def local_policiesV_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopFour.credentials_def RRLoopFive.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioV_def local_policiesV_def)
        apply (simp add: hc_scenarioV_def local_policiesV_def ex_graphV_def RRLoopFive.nodes_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
    apply (metis (full_types) RRLoopFive.delta.simps bex_empty cloudV_def hc_scenarioV_def homeV_def hospitalV_def local_policiesV_def numeral_1_eq_Suc_0 numerals(1) sphoneV_def)
    sorry
(* put *)
next show "\<And>(s::RRLoopFive.infrastructure) (s'::RRLoopFive.infrastructure) (G::RRLoopFive.igraph)
       (I::RRLoopFive.infrastructure) (a::char list) (l::location) (as::char list set)
       (n::char list) I'::RRLoopFive.infrastructure.
       (hc_scenarioV, s)
       \<in> {(x::RRLoopFive.infrastructure, y::RRLoopFive.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopFive.nodes (RRLoopFive.graphI hc_scenarioV) =
       RRLoopFive.nodes (RRLoopFive.graphI s) \<Longrightarrow>
       RRLoopFive.delta hc_scenarioV = RRLoopFive.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopFive.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       RRLoopFive.enables I l (Actor a) put \<Longrightarrow>
       (RRLoopFive.ledgra G \<nabla> ((a, as), n)) = {} \<Longrightarrow>
       I' =
       RRLoopFive.infrastructure.Infrastructure
        (RRLoopFive.igraph.Lgraph (RRLoopFive.gra G) (RRLoopFive.agra G) (RRLoopFive.cgra G)
          (RRLoopFive.lgra G) (RRLoopFive.ledgra G ((a, as), n) := {l}))
        (RRLoopFive.delta I) \<Longrightarrow>
       rmapV s \<rightarrow>\<^sub>n rmapV s'"
    apply (rule_tac I = "rmapV s" and I' = "rmapV s'" and l = l and a = a  
                       and a = a and as = as and n = n
                     in RRLoopFour.state_transition_in.put)
  apply (rule refl)
       apply (simp add: rmapV_def ref_map_def atI_def RRLoopFour.atI_def)
     apply (simp add: rmapV_def ref_map_def RRLoopFour.nodes_def nodes_def)
       prefer 2
     apply (simp add: rmapV_def ref_map_def)
(* enables put*)
 apply (simp add: rmapV_def ref_map_def enables_def RRLoopFour.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI,assumption)
  apply(simp add: local_policiesF_def local_policiesV_def hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def
                 atI_def RRLoopFour.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
  apply (drule sym)
  apply (simp add: hc_scenarioV_def local_policiesV_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
         apply (simp add: has_def RRLoopFour.has_def atI_def 
                RRLoopFour.credentials_def RRLoopFive.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioV_def local_policiesV_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
         apply (simp add: has_def RRLoopFour.has_def atI_def 
                RRLoopFour.credentials_def RRLoopFive.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioV_def local_policiesV_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
         apply (simp add: has_def RRLoopFour.has_def atI_def 
                RRLoopFour.credentials_def RRLoopFive.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioV_def local_policiesV_def)
        apply (simp add: hc_scenarioV_def local_policiesV_def ex_graphV_def RRLoopFive.nodes_def)
  apply (simp add: hospitalF_def sphoneF_def
                  homeF_def cloudF_def cloudV_def homeV_def sphoneV_def hospitalV_def hc_scenarioV_def)
    by (metis (full_types) RRLoopFive.delta.simps bex_empty cloudV_def hc_scenarioV_def homeV_def hospitalV_def local_policiesV_def numeral_1_eq_Suc_0 numerals(1) sphoneV_def)
qed

theorem refmapFive: "hc_KripkeF  \<sqsubseteq>\<^sub>rmapV hc_KripkeV" 
proof (rule strong_mt', simp add: hc_KripkeV_def hc_KripkeF_def hc_statesF_def hc_statesV_def state_transition_refl_def, rule conjI)
  show "rmapV hc_scenarioV = hc_scenarioF"
    apply (simp add: rmapV_def ref_map_def hc_scenarioV_def hc_scenarioF_def ex_graphV_def ex_graphF_def
           homeV_def homeF_def cloudV_def cloudF_def sphoneV_def sphoneF_def hospitalV_def hospitalF_def
           ex_locV_ass_def ex_locF_ass_def ex_credsV_def ex_credsF_def
           ex_locsV_def ex_locsF_def ex_ledgerV_def ex_ledger_def) 
    apply (rule conjI)
     apply (unfold hospitalV_def hospitalF_def, rule refl)
by (unfold cloudV_def cloudF_def, rule refl)
next show "\<forall>s::RRLoopFive.infrastructure.
       (hc_scenarioV, s)
       \<in> {(x::RRLoopFive.infrastructure, y::RRLoopFive.infrastructure). x \<rightarrow>\<^sub>i y}\<^sup>* \<longrightarrow>
       (\<forall>s'::RRLoopFive.infrastructure. s \<rightarrow>\<^sub>i s' \<longrightarrow> rmapV s \<rightarrow>\<^sub>i rmapV s')"
    apply (unfold state_transition_infra_def RRLoopFour.state_transition_infra_def)
    by (rule refmapFour_lem)
qed


(* show attack "Eve can still do put at cloud and since we haven't
   forbidden it, she can overwrite Bob's entry "  *)
theorem hc_EFV: "hc_KripkeV \<turnstile> EF shcV"  
  sorry

(* See hcKripkeFour
theorem Ledger_con: "h \<in> hc_actorsV \<Longrightarrow> h' \<in> hc_actorsV \<Longrightarrow> l \<in> hc_locationsV \<Longrightarrow>
    l' \<in> hc_locationsV \<Longrightarrow> 
    l \<in> (ledgra G \<nabla> ((h, hs),n)) \<Longrightarrow> l' \<in> (ledgra G \<nabla> ((h', hs'),n)) \<Longrightarrow> 
    (h, hs) = (h', hs')"

*)

end

end
 