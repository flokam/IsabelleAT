theory hcKripkeTwo
imports RRLoopTwo
begin

locale scenarioHCKripkeTwo = scenarioHCKripkeOne +
fixes hc_actorsT :: "identity set"
defines hc_actorsT_def: "hc_actorsT \<equiv> {''Patient'', ''Doctor''}"
fixes hc_locationsT :: "location set"
defines hc_locationsT_def: "hc_locationsT \<equiv> 
          {Location 0, Location 1, Location 2, Location 3}"

fixes sphoneT :: "location"
defines sphoneT_def: "sphoneT \<equiv> Location 0"
fixes homeT :: "location"
defines homeT_def: "homeT \<equiv> Location 1"
fixes hospitalT :: "location"
defines hospitalT_def: "hospitalT \<equiv> Location 2"
fixes cloudT :: "location"
defines cloudT_def: "cloudT \<equiv> Location 3"

fixes global_policyT :: "[infrastructure, identity] \<Rightarrow> bool"
defines global_policyT_def: "global_policyT I a \<equiv> a \<notin> hc_actorsT 
                 \<longrightarrow> \<not>(enables I cloudT (Actor a) eval)"  

fixes ex_credsT :: "actor \<Rightarrow> (string set * string set)"
defines ex_credsT_def: "ex_credsT \<equiv> (\<lambda> x. if x = Actor ''Patient'' then 
                         ({''PIN'',''skey''}, {}) else 
                            (if x = Actor ''Doctor'' then
                                ({''PIN''},{}) else ({},{})))"

fixes ex_locsT :: "location \<Rightarrow> string * acond"
defines "ex_locsT \<equiv>  (\<lambda> x.  if x = cloudT then
             (''free'',{((Actor ''Patient'',{Actor ''Doctor''}),42)}) 
             else ('''',{}))"

fixes ex_locT_ass :: "location \<Rightarrow> identity set"
defines ex_locT_ass_def: "ex_locT_ass \<equiv>
          (\<lambda> x.  if x = homeT then {''Patient''}  
                 else (if x = hospitalT then {''Doctor'', ''Eve''} 
                       else {}))"
fixes ex_graphT :: "igraph"
defines ex_graphT_def: "ex_graphT \<equiv> Lgraph 
     {(homeT, cloudT), (sphoneT, cloudT), (cloudT,hospitalT)}
     ex_locT_ass
     ex_credsT ex_locsT"

fixes ex_graphT' :: "igraph"
defines ex_graphT'_def: "ex_graphT' \<equiv> Lgraph 
     {(homeT, cloudT), (sphoneT, cloudT), (cloudT,hospitalT)}
       (\<lambda> x. if x = cloudT then {''Patient''} else 
           (if x = hospitalT then {''Doctor'',''Eve''} else {})) 
     ex_credsT ex_locsT"

fixes ex_graphT'' :: "igraph"
defines ex_graphT''_def: "ex_graphT'' \<equiv> Lgraph 
     {(homeT, cloudT), (sphoneT, cloudT), (cloudT,hospitalT)}
       (\<lambda> x. if x = cloudT then {''Patient'', ''Eve''} else 
           (if x = hospitalT then {''Doctor''} else {})) 
     ex_credsT ex_locsT"

fixes local_policiesT :: "[igraph, location] \<Rightarrow> policy set"
defines local_policiesT_def: "local_policiesT G \<equiv> 
    (\<lambda> x. if x = homeT then
        {(\<lambda> y. True, {put,get,move,eval})}
          else (if x = sphoneT then 
             {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
                else (if x = cloudT then
                {(\<lambda> y. True, {put,get,move,eval})}
                       else (if x = hospitalT then
                {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospitalT) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} else {}))))"

fixes rmapT :: "RRLoopTwo.infrastructure \<Rightarrow> RRLoopOne.infrastructure"
defines rmapT_def:
"rmapT I \<equiv> ref_map I local_policies"

fixes hc_scenarioT :: "infrastructure"
defines hc_scenarioT_def:
"hc_scenarioT \<equiv> Infrastructure ex_graphT local_policiesT"

fixes IhcT :: "infrastructure set"
defines IhcT_def:
  "IhcT \<equiv> {hc_scenarioT}"

fixes hc_scenarioT' :: "infrastructure"
defines hc_scenarioT'_def:
"hc_scenarioT' \<equiv> Infrastructure ex_graphT' local_policiesT"

fixes HCT' :: "infrastructure set"
defines HCT'_def:
  "HCT' \<equiv> {hc_scenarioT'}"

fixes hc_scenarioT'' :: "infrastructure"
defines hc_scenarioT''_def:
"hc_scenarioT'' \<equiv> Infrastructure ex_graphT'' local_policiesT"

fixes HCT'' :: "infrastructure set"
defines HCT''_def:
  "HCT'' \<equiv> {hc_scenarioT''}"

fixes hc_statesT
defines hc_statesT_def: "hc_statesT \<equiv> { I. hc_scenarioT \<rightarrow>\<^sub>i* I }"

fixes hc_KripkeT
defines "hc_KripkeT \<equiv> Kripke hc_statesT {hc_scenarioT}"

fixes shcT 
defines "shcT \<equiv> {x. \<not> (global_policyT x ''Eve'')}"  


begin

lemma refmapOne_lem: " \<forall>(s::RRLoopTwo.infrastructure) s'::RRLoopTwo.infrastructure. s \<rightarrow>\<^sub>n s' \<longrightarrow> rmapT s \<rightarrow>\<^sub>n rmapT s'"
  apply clarify
  apply (erule state_transition_in.cases) 
  apply (rule_tac I = "rmapT s" and I' = "rmapT s'" and l = l and l' = l' 
                             and a = a 
 in RRLoopOne.state_transition_in.move)
  apply (rule refl)
            apply (simp add: rmapT_def ref_map_def atI_def RRLoopOne.atI_def)
           apply (simp add: rmapT_def ref_map_def nodes_def RRLoopOne.nodes_def)
           apply (simp add: rmapT_def ref_map_def nodes_def RRLoopOne.nodes_def)
         apply (simp add: rmapT_def ref_map_def actors_graph_def RRLoopOne.actors_graph_def)
         apply (rule_tac x = l in exI)
         apply (simp add: nodes_def RRLoopOne.nodes_def atI_def)
  prefer 2
        apply (simp add: rmapT_def ref_map_def move_graph_a_def RRLoopOne.move_graph_a_def)
(* Critical case: we don't know how the policies of refined and old model relate, i.e.
   how do we prove:
   RRLoopTwo.enables I l' (Actor a) move \<Rightarrow> RRLoopOne.enables (rmapT s) l' (Actor a) move ? 
   In this version of the rmap_def, rmapT basically just replaces with local_policiesT
   but we need to know at least that delta I is local_policiesT. So an additional assumption
   that  for all states (that are reachable?) the policy local_policiesT applies, i.e.
   delta s = local_policiesT *)
(* For now only as a local assumption: *)
  apply (subgoal_tac "delta I = local_policiesT")
  apply (simp add: rmapT_def ref_map_def enables_def RRLoopOne.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policies_def local_policiesT_def hospital_def sphone_def
                  home_def cloud_def cloudT_def homeT_def sphoneT_def hospitalT_def
                 atI_def RRLoopOne.atI_def)
        apply (rule conjI)
         apply (rule impI)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudT_def homeT_def sphoneT_def hospitalT_def)
         apply (erule exE)
         apply (erule conjE)+
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopTwo.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
         apply (rule impI)+
         apply (simp add: sphoneT_def cloudT_def)
         apply (rule impI)+
        apply (rule conjI)
         apply (rule impI)
         apply (simp add: sphoneT_def cloudT_def has_def RRLoopOne.has_def
                          RRLoopOne.credentials_def RRLoopTwo.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
         apply (rule impI)
         apply (simp add: sphoneT_def cloudT_def has_def RRLoopOne.has_def
                          RRLoopOne.credentials_def RRLoopTwo.credentials_def)
  apply (subgoal_tac " RRLoopTwo.nodes (RRLoopTwo.graphI I) = 
                      {Location (0::nat),Location (1::nat),Location (2::nat),Location (3::nat)}")

         apply simp
  apply (simp add: nodes_def)
  sorry

(*
  apply (simp add: rmapT_def ref_map_def)
   apply (rule_tac I = "RRLoopOne.infrastructure.Infrastructure
        (RRLoopOne.igraph.Lgraph (RRLoopTwo.gra (RRLoopTwo.graphI I))
          (RRLoopTwo.agra (RRLoopTwo.graphI I)) (RRLoopTwo.cgra (RRLoopTwo.graphI I))
          (\<lambda>l::location. {fst (RRLoopTwo.lgra (RRLoopTwo.graphI I) l)}))
        local_policies" and I' = "RRLoopOne.infrastructure.Infrastructure
                             (RRLoopOne.igraph.Lgraph
                               (RRLoopTwo.gra (RRLoopTwo.move_graph_a a l l' (RRLoopTwo.graphI I)))
                               (RRLoopTwo.agra (RRLoopTwo.move_graph_a a l l' (RRLoopTwo.graphI I)))
                               (RRLoopTwo.cgra (RRLoopTwo.move_graph_a a l l' (RRLoopTwo.graphI I)))
                               (\<lambda>la::location.
                                   {fst (RRLoopTwo.lgra
                                          (RRLoopTwo.move_graph_a a l l' (RRLoopTwo.graphI I)) la)}))
                             local_policies" and l = l and l' = l' 
                             and a = a 
 in RRLoopOne.state_transition_in.move)
  apply (rule refl)
            apply (simp add: atI_def RRLoopOne.atI_def)
           apply (simp add: nodes_def RRLoopOne.nodes_def)
           apply (simp add: nodes_def RRLoopOne.nodes_def)
         apply (simp add: actors_graph_def RRLoopOne.actors_graph_def)
         apply (rule_tac x = l in exI)
         apply (simp add: nodes_def RRLoopOne.nodes_def atI_def)
        apply (simp add: enables_def RRLoopOne.enables_def)
        apply (erule bexE)
        apply (rule_tac x = x in bexI, assumption)
  apply (simp add: local_policies_def sphone_def home_def hospital_def cloud_def)
        apply (rule conjI)
  apply (rule_tac I = "rmapT s" and I' = "rmapT s'" in  RRLoopOne.state_transition_in.move)
  apply simp
*)
 lemma same_nodes0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> nodes(graphI z) = nodes(graphI z')"   
    apply clarify
  apply (erule RRLoopTwo.state_transition_in.cases)
  by (simp add: move_graph_a_def atI_def actors_graph_def nodes_def)+

lemma same_nodes: "(hc_scenarioT, s) \<in> {(x::RRLoopTwo.infrastructure, y::RRLoopTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
\<Longrightarrow> RRLoopTwo.nodes (graphI hc_scenarioT) = RRLoopTwo.nodes (graphI s)"
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

lemma refmapOne_lem': "\<forall>s::RRLoopTwo.infrastructure.
       (hc_scenarioT, s) \<in> {(x::RRLoopTwo.infrastructure, y::RRLoopTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>s'::RRLoopTwo.infrastructure. s \<rightarrow>\<^sub>n s' \<longrightarrow> rmapT s \<rightarrow>\<^sub>n rmapT s')"
  apply clarify
  apply (subgoal_tac "nodes(graphI hc_scenarioT) = nodes(graphI s)")
   prefer 2
   apply (erule same_nodes)
  apply (subgoal_tac "delta hc_scenarioT = delta s")
  prefer 2
  apply (erule init_state_policy)
  apply (erule state_transition_in.cases) 
  apply (rule_tac I = "rmapT s" and I' = "rmapT s'" and l = l and l' = l' 
                             and a = a 
 in RRLoopOne.state_transition_in.move)
  apply (rule refl)
            apply (simp add: rmapT_def ref_map_def atI_def RRLoopOne.atI_def)
           apply (simp add: rmapT_def ref_map_def nodes_def RRLoopOne.nodes_def)
           apply (simp add: rmapT_def ref_map_def nodes_def RRLoopOne.nodes_def)
         apply (simp add: rmapT_def ref_map_def actors_graph_def RRLoopOne.actors_graph_def)
         apply (rule_tac x = l in exI)
         apply (simp add: nodes_def RRLoopOne.nodes_def atI_def)
  prefer 2
        apply (simp add: rmapT_def ref_map_def move_graph_a_def RRLoopOne.move_graph_a_def)
  apply (simp add: rmapT_def ref_map_def enables_def RRLoopOne.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policies_def local_policiesT_def hospital_def sphone_def
                  home_def cloud_def cloudT_def homeT_def sphoneT_def hospitalT_def
                 atI_def RRLoopOne.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
  apply (drule sym)
  apply (simp add: hc_scenarioT_def local_policiesT_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudT_def homeT_def sphoneT_def hospitalT_def hc_scenarioT_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopTwo.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioT_def local_policiesT_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudT_def homeT_def sphoneT_def hospitalT_def hc_scenarioT_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopTwo.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioT_def local_policiesT_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudT_def homeT_def sphoneT_def hospitalT_def hc_scenarioT_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopTwo.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioT_def local_policiesT_def)
        apply (simp add: hc_scenarioT_def local_policiesT_def ex_graphT_def RRLoopTwo.nodes_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudT_def homeT_def sphoneT_def hospitalT_def hc_scenarioT_def)
  apply (subgoal_tac "RRLoopTwo.nodes (RRLoopTwo.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: hc_scenarioT_def local_policiesT_def ex_graphT_def RRLoopTwo.nodes_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudT_def homeT_def sphoneT_def hospitalT_def hc_scenarioT_def)
  apply blast
(* *)
  sorry



theorem refmapOne': "hc_Kripke  \<sqsubseteq>\<^sub>rmapT hc_KripkeT" 
proof (rule strong_mt', simp add: hc_KripkeT_def hc_Kripke_def hc_states_def hc_statesT_def state_transition_refl_def, rule conjI)
  show "rmapT hc_scenarioT = hc_scenario"
    apply (simp add: rmapT_def ref_map_def hc_scenarioT_def hc_scenario_def ex_graphT_def ex_graph_def
           homeT_def home_def cloudT_def cloud_def sphoneT_def sphone_def hospitalT_def hospital_def
           ex_locT_ass_def ex_loc_ass_def ex_credsT_def ex_creds_def
           ex_locsT_def ex_locs_def) 
    apply (rule conjI)
    apply (unfold hospitalT_def hospital_def, rule refl)
    by force
next show "\<forall>s::RRLoopTwo.infrastructure.
       (hc_scenarioT, s) \<in> {(x::RRLoopTwo.infrastructure, y::RRLoopTwo.infrastructure). x \<rightarrow>\<^sub>i y}\<^sup>* \<longrightarrow>
       (\<forall>s'::RRLoopTwo.infrastructure. s \<rightarrow>\<^sub>i s' \<longrightarrow> rmapT s \<rightarrow>\<^sub>i rmapT s')"
    apply (unfold state_transition_infra_def RRLoopOne.state_transition_infra_def)
    by (rule refmapOne_lem')
qed

theorem refmapOne: "hc_Kripke  \<sqsubseteq>\<^sub>rmapT hc_KripkeT" 
proof (rule strong_mt, simp add: hc_KripkeT_def hc_Kripke_def hc_states_def hc_statesT_def state_transition_refl_def, rule conjI)
  show "rmapT hc_scenarioT = hc_scenario"
    apply (simp add: rmapT_def ref_map_def hc_scenarioT_def hc_scenario_def ex_graphT_def ex_graph_def
           homeT_def home_def cloudT_def cloud_def sphoneT_def sphone_def hospitalT_def hospital_def
           ex_locT_ass_def ex_loc_ass_def ex_credsT_def ex_creds_def
           ex_locsT_def ex_locs_def) 
    apply (rule conjI)
    apply (unfold hospitalT_def hospital_def, rule refl)
    by force
next show "\<forall>(s::RRLoopTwo.infrastructure) s'::RRLoopTwo.infrastructure. s \<rightarrow>\<^sub>i s' \<longrightarrow> rmapT s \<rightarrow>\<^sub>i rmapT s'"
    apply (unfold state_transition_infra_def RRLoopOne.state_transition_infra_def)
    by (rule refmapOne_lem)
qed

(* show attack "Eve can do eval at cloud"  *)
lemma step1: "hc_scenarioT \<rightarrow>\<^sub>n hc_scenarioT'"
proof (rule_tac l = homeT and a = "''Patient''" and l' = cloudT in move)
  show "graphI hc_scenarioT = graphI hc_scenarioT" by (rule refl)
next show "''Patient'' @\<^bsub>graphI hc_scenarioT\<^esub> homeT" 
    by (simp add: hc_scenarioT_def ex_graphT_def ex_locT_ass_def atI_def nodes_def)
next show "homeT \<in> nodes (graphI hc_scenarioT)"
    by (simp add: hc_scenarioT_def ex_graphT_def ex_locT_ass_def atI_def nodes_def, blast)
next show "cloudT \<in> nodes (graphI hc_scenarioT)"
    by (simp add: hc_scenarioT_def nodes_def ex_graphT_def, blast)
next show "''Patient'' \<in> actors_graph (graphI hc_scenarioT)"
    by (simp add: actors_graph_def hc_scenarioT_def ex_graphT_def ex_locT_ass_def nodes_def, blast)
next show "enables hc_scenarioT cloudT (Actor ''Patient'') move"
    by (simp add: enables_def hc_scenarioT_def ex_graphT_def local_policiesT_def
                    ex_credsT_def ex_locsT_def has_def credentials_def)
next show "hc_scenarioT' =
    Infrastructure (move_graph_a ''Patient'' homeT cloudT (graphI hc_scenarioT)) (delta hc_scenarioT)"
    apply (simp add: hc_scenarioT'_def ex_graphT'_def move_graph_a_def 
                   hc_scenarioT_def ex_graphT_def homeT_def cloudT_def hospitalT_def
                    ex_locT_ass_def ex_credsT_def)
    apply (rule ext)
    by (simp add: hospitalT_def)
qed

lemma step1r: "hc_scenarioT  \<rightarrow>\<^sub>n* hc_scenarioT'"
proof (simp add: state_transition_in_refl_def)
  show " (hc_scenarioT, hc_scenarioT') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  by (insert step1, auto)
qed

lemma step2: "hc_scenarioT'  \<rightarrow>\<^sub>n hc_scenarioT''"
proof (rule_tac l = hospitalT and a = "''Eve''" and l' = cloudT in move, rule refl)
  show "''Eve'' @\<^bsub>graphI hc_scenarioT'\<^esub> hospitalT"
   by (simp add: hc_scenarioT'_def ex_graphT'_def hospitalT_def cloudT_def atI_def nodes_def)
next show "hospitalT \<in> nodes (graphI hc_scenarioT')"
    by (simp add: hc_scenarioT'_def ex_graphT'_def hospitalT_def cloudT_def atI_def nodes_def, blast)
next show "cloudT \<in> nodes (graphI hc_scenarioT')"
    by (simp add: hc_scenarioT'_def nodes_def ex_graphT'_def, blast)
next show "''Eve'' \<in> actors_graph (graphI hc_scenarioT')"
    by (simp add: actors_graph_def hc_scenarioT'_def ex_graphT'_def nodes_def
                     hospitalT_def cloudT_def, blast)
next show "enables hc_scenarioT' cloudT (Actor ''Eve'') move"
    by (simp add: enables_def hc_scenarioT'_def ex_graphT_def local_policiesT_def
                  ex_credsT_def ex_locsT_def has_def credentials_def cloudT_def sphoneT_def)
next show "hc_scenarioT'' =
    Infrastructure (move_graph_a ''Eve'' hospitalT cloudT (graphI hc_scenarioT')) (delta hc_scenarioT')"
    apply (simp add: hc_scenarioT'_def ex_graphT''_def move_graph_a_def hc_scenarioT''_def 
                     ex_graphT'_def homeT_def cloudT_def hospitalT_def ex_credsT_def)
    apply (rule ext)
    apply (simp add: hospitalT_def)
    by blast
qed

lemma step2r: "hc_scenarioT'  \<rightarrow>\<^sub>n* hc_scenarioT''"
proof (simp add: state_transition_in_refl_def)
  show "(hc_scenarioT', hc_scenarioT'') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step2, auto)
qed

(* Second attack: Eve can get onto cloud and manipulate data 
   because the policy allows Eve to eval on cloud. *)
(* Note the first bunch of lemmas develops the attack refinement *)
lemma hcT_ref: "[\<N>\<^bsub>(IhcT,shcT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcT,shcT)\<^esup> \<sqsubseteq>
                  [\<N>\<^bsub>(IhcT,HCT')\<^esub>, \<N>\<^bsub>(HCT',shcT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcT,shcT)\<^esup>"  
proof (rule_tac l = "[]" and l' = "[\<N>\<^bsub>(IhcT,HCT')\<^esub>, \<N>\<^bsub>(HCT',shcT)\<^esub>]" and
                  l'' = "[]" and si = IhcT and si' = IhcT and 
                  si'' = shcT and si''' = shcT in refI, simp, rule refl)
  show "([\<N>\<^bsub>(IhcT, HCT')\<^esub>, \<N>\<^bsub>(HCT', shcT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcT, shcT)\<^esup>) =
    ([] @ [\<N>\<^bsub>(IhcT, HCT')\<^esub>, \<N>\<^bsub>(HCT', shcT)\<^esub>] @ [] \<oplus>\<^sub>\<and>\<^bsup>(IhcT, shcT)\<^esup>)"
  by simp
qed

lemma att_hcT: "\<turnstile>[\<N>\<^bsub>(IhcT,HCT')\<^esub>, \<N>\<^bsub>(HCT',shcT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcT,shcT)\<^esup>"
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(IhcT, HCT')\<^esub>"
   apply (simp add: IhcT_def HCT'_def att_base)
   apply (subst state_transition_infra_def)
   by (rule step1)
next show "\<turnstile>[\<N>\<^bsub>(HCT', shcT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(HCT', shcT)\<^esup>"
   apply (subst att_and, simp)
   apply (simp add: HCT'_def shcT_def att_base)
   apply (subst state_transition_infra_def)
   apply (rule_tac x = hc_scenarioT'' in exI)
   apply (rule conjI)
   apply (simp add: global_policyT_def hc_scenarioT''_def hc_actorsT_def 
                    enables_def local_policiesT_def cloudT_def sphoneT_def)
    by (rule step2)
qed

lemma hcT_abs_att: "\<turnstile>\<^sub>V [\<N>\<^bsub>(IhcT,shcT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcT,shcT)\<^esup>"
proof (rule ref_valI, rule hcT_ref, rule att_hcT)
qed

lemma hcT_att: "hc_KripkeT \<turnstile> EF {x. \<not>(global_policyT x ''Eve'')}"
proof -
  have a: " \<turnstile>[\<N>\<^bsub>(IhcT, HCT')\<^esub>, \<N>\<^bsub>(HCT', shcT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcT, shcT)\<^esup>"
    by (rule att_hcT)
  hence "(IhcT,shcT) = attack ([\<N>\<^bsub>(IhcT, HCT')\<^esub>, \<N>\<^bsub>(HCT', shcT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcT, shcT)\<^esup>)"
    by simp
  hence "Kripke {s::infrastructure. \<exists>i::infrastructure\<in>IhcT. i \<rightarrow>\<^sub>i* s} IhcT \<turnstile> EF shcT"
    apply (insert a)
    apply (erule AT_EF)
    by simp
  thus  "hc_KripkeT \<turnstile> EF {x::infrastructure. \<not> global_policyT x ''Eve''}"
    by (simp add: hc_KripkeT_def hc_statesT_def IhcT_def shcT_def)
qed


theorem hc_EFT: "hc_KripkeT \<turnstile> EF shcT"  
proof (insert hcT_att, simp add: shcT_def) 
qed

end
end
