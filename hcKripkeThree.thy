theory hcKripkeThree
imports RRLoopThree
begin

locale scenarioHCKripkeThree = scenarioHCKripkeTwo +
fixes hc_actorsR :: "identity set"
defines hc_actorsR_def: "hc_actorsR \<equiv> {''Patient'', ''Doctor''}"
fixes hc_locationsR :: "location set"
defines hc_locationsR_def: "hc_locationsR \<equiv> 
          {Location 0, Location 1, Location 2, Location 3}"

fixes sphoneR :: "location"
defines sphoneR_def: "sphoneR \<equiv> Location 0"
fixes homeR :: "location"
defines homeR_def: "homeR \<equiv> Location 1"
fixes hospitalR :: "location"
defines hospitalR_def: "hospitalR \<equiv> Location 2"
fixes cloudR :: "location"
defines cloudR_def: "cloudR \<equiv> Location 3"

fixes global_policyR :: "[infrastructure, identity] \<Rightarrow> bool"
defines global_policyR_def: "global_policyR I a \<equiv> a \<notin> hc_actorsR 
                 \<longrightarrow> \<not>(enables I cloudR (Actor a) put)"  

fixes ex_credsR :: "actor \<Rightarrow> (string set * string set)"
defines ex_credsR_def: "ex_credsR \<equiv> (\<lambda> x. if x = Actor ''Patient'' then 
                         ({''PIN'',''skey''}, {}) else 
                            (if x = Actor ''Doctor'' then
                                ({''PIN''},{}) else ({},{})))"

fixes ex_locsR :: "location \<Rightarrow> acond"
defines "ex_locsR \<equiv>  (\<lambda> x.  if x = cloudR then
             ({((Actor ''Patient'',{Actor ''Doctor''}),''42'')}) 
             else ({}))"

fixes ex_locR_ass :: "location \<Rightarrow> identity set"
defines ex_locR_ass_def: "ex_locR_ass \<equiv>
          (\<lambda> x.  if x = homeR then {''Patient''}  
                 else (if x = hospitalR then {''Doctor'', ''Eve''} 
                       else {}))"
fixes ex_graphR :: "igraph"
defines ex_graphR_def: "ex_graphR \<equiv> Lgraph 
     {(homeR, cloudR), (sphoneR, cloudR), (cloudR,hospitalR)}
     ex_locR_ass
     ex_credsR ex_locsR"

fixes ex_graphR' :: "igraph"
defines ex_graphR'_def: "ex_graphR' \<equiv> Lgraph 
     {(homeR, cloudR), (sphoneR, cloudR), (cloudR,hospitalR)}
       (\<lambda> x. if x = cloudR then {''Patient''} else 
           (if x = hospitalR then {''Doctor'',''Eve''} else {})) 
     ex_credsR ex_locsR"

fixes ex_graphR'' :: "igraph"
defines ex_graphR''_def: "ex_graphR'' \<equiv> Lgraph 
     {(homeR, cloudR), (sphoneR, cloudR), (cloudR,hospitalR)}
       (\<lambda> x. if x = cloudR then {''Patient'', ''Eve''} else 
           (if x = hospitalR then {''Doctor''} else {})) 
     ex_credsR ex_locsR"

fixes local_policiesR :: "[igraph, location] \<Rightarrow> policy set"
defines local_policiesR_def: "local_policiesR G \<equiv> 
    (\<lambda> x. if x = homeR then
        {(\<lambda> y. True, {put,get,move,eval})}
          else (if x = sphoneR then 
             {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
                else (if x = cloudR then
                {(\<lambda> y. True, {put,get,move,eval})}
                       else (if x = hospitalR then
                {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospitalR) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} else {}))))"

fixes rmapR :: "RRLoopThree.infrastructure \<Rightarrow> RRLoopTwo.infrastructure"
defines rmapR_def:
"rmapR I \<equiv> ref_map I local_policiesT"

fixes hc_scenarioR :: "infrastructure"
defines hc_scenarioR_def:
"hc_scenarioR \<equiv> Infrastructure ex_graphR local_policiesR"

fixes IhcR :: "infrastructure set"
defines IhcR_def:
  "IhcR \<equiv> {hc_scenarioR}"

fixes hc_scenarioR' :: "infrastructure"
defines hc_scenarioR'_def:
"hc_scenarioR' \<equiv> Infrastructure ex_graphR' local_policiesR"

fixes HCR' :: "infrastructure set"
defines HCR'_def:
  "HCR' \<equiv> {hc_scenarioR'}"

fixes hc_scenarioR'' :: "infrastructure"
defines hc_scenarioR''_def:
"hc_scenarioR'' \<equiv> Infrastructure ex_graphR'' local_policiesR"

fixes HCR'' :: "infrastructure set"
defines HCR''_def:
  "HCR'' \<equiv> {hc_scenarioR''}"

fixes hc_statesR
defines hc_statesR_def: "hc_statesR \<equiv> { I. hc_scenarioR \<rightarrow>\<^sub>i* I }"

fixes hc_KripkeR
defines "hc_KripkeR \<equiv> Kripke hc_statesR {hc_scenarioR}"

fixes shcR
defines "shcR \<equiv> {x. \<not> (global_policyR x ''Eve'')}"  

assumes no_insider: "inj Actor"

begin

 lemma same_nodes0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> nodes(graphI z) = nodes(graphI z')"   
    apply clarify
  apply (erule RRLoopThree.state_transition_in.cases)
  by (simp add: move_graph_a_def atI_def actors_graph_def nodes_def)+

lemma same_nodes: "(hc_scenarioR, s) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
\<Longrightarrow> RRLoopThree.nodes (graphI hc_scenarioR) = RRLoopThree.nodes (graphI s)"
  apply (erule rtrancl_induct)
   apply (rule refl)
  apply (drule CollectD)
    apply simp
    apply (drule same_nodes0)
  by simp  

lemma finite_data_imp0: 
"(hc_scenarioR, I) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*  \<Longrightarrow>
(\<forall>l::location. finite (RRLoopThree.lgra (RRLoopThree.graphI hc_scenarioR) l)) \<longrightarrow>
(\<forall>l::location. finite (RRLoopThree.lgra (RRLoopThree.graphI I) l))"
    apply (erule rtrancl_induct)  
   apply simp+
  apply clarify
  apply (erule state_transition_in.cases) 
  apply (simp add: move_graph_a_def)
by simp+

lemma finite_data0: 
"(hc_scenarioR, I) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*  \<Longrightarrow>
\<forall>l::location. finite (RRLoopThree.lgra (RRLoopThree.graphI I) l)"
  apply (drule finite_data_imp0)
by (simp add: hc_scenarioR_def ex_graphR_def ex_locsR_def)

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


lemma refmapTwo_lem: "\<forall>s::RRLoopThree.infrastructure.
       (hc_scenarioR, s) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>s'::RRLoopThree.infrastructure. s \<rightarrow>\<^sub>n s' \<longrightarrow> rmapR s \<rightarrow>\<^sub>n rmapR s')"
  apply clarify
  apply (subgoal_tac "nodes(graphI hc_scenarioR) = nodes(graphI s)")
   prefer 2
   apply (erule same_nodes)
  apply (subgoal_tac "delta hc_scenarioR = delta s")
  prefer 2
  apply (erule init_state_policy)
  apply (erule state_transition_in.cases) 
proof -
(* move *)
show "\<And>(s::RRLoopThree.infrastructure) (s'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (l'::location)
       I'::RRLoopThree.infrastructure.
       (hc_scenarioR, s)
       \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopThree.nodes (RRLoopThree.graphI hc_scenarioR) = RRLoopThree.nodes (RRLoopThree.graphI s) \<Longrightarrow>
       RRLoopThree.delta hc_scenarioR = RRLoopThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopThree.graphI I \<Longrightarrow>
       h @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> RRLoopThree.nodes G \<Longrightarrow>
       l' \<in> RRLoopThree.nodes G \<Longrightarrow>
       h \<in> RRLoopThree.actors_graph (RRLoopThree.graphI I) \<Longrightarrow>
       RRLoopThree.enables I l' (Actor h) move \<Longrightarrow>
       I' =
       RRLoopThree.infrastructure.Infrastructure (RRLoopThree.move_graph_a h l l' (RRLoopThree.graphI I))
        (RRLoopThree.delta I) \<Longrightarrow>
       rmapR s \<rightarrow>\<^sub>n rmapR s'"
  apply (rule_tac I = "rmapR s" and I' = "rmapR s'" and l = l and l' = l' 
                             and a = h
 in RRLoopTwo.state_transition_in.move)
  apply (rule refl)
            apply (simp add: rmapR_def ref_map_def atI_def RRLoopTwo.atI_def)
           apply (simp add: rmapR_def ref_map_def nodes_def RRLoopTwo.nodes_def)
           apply (simp add: rmapR_def ref_map_def nodes_def RRLoopTwo.nodes_def)
         apply (simp add: rmapR_def ref_map_def actors_graph_def RRLoopTwo.actors_graph_def)
         apply (rule_tac x = l in exI)
         apply (simp add: nodes_def RRLoopTwo.nodes_def atI_def)
  prefer 2
        apply (simp add: rmapR_def ref_map_def move_graph_a_def RRLoopTwo.move_graph_a_def)
  apply (simp add: rmapR_def ref_map_def enables_def RRLoopTwo.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policiesT_def local_policiesR_def hospitalT_def sphoneR_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def
                 atI_def RRLoopTwo.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
  apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesT_def local_policiesR_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopTwo.has_def atI_def 
                RRLoopTwo.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopTwo.has_def atI_def 
                RRLoopTwo.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopTwo.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
        apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
  apply (subgoal_tac "RRLoopThree.nodes (RRLoopThree.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
  apply (simp add: hospitalT_def sphoneT_def RRLoopThree.nodes_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
   apply (simp add: local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
   apply (simp add: hospitalT_def sphoneT_def RRLoopThree.nodes_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
  by blast
(* get *)
next show "\<And>(s::RRLoopThree.infrastructure) (s'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (l'::location) (h'::char list)
       (hs::actor set) (n::char list) I'::RRLoopThree.infrastructure.
       (hc_scenarioR, s)
       \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopThree.nodes (RRLoopThree.graphI hc_scenarioR) = RRLoopThree.nodes (RRLoopThree.graphI s) \<Longrightarrow>
       RRLoopThree.delta hc_scenarioR = RRLoopThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopThree.graphI I \<Longrightarrow>
       h @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> RRLoopThree.nodes G \<Longrightarrow>
       l' \<in> RRLoopThree.nodes G \<Longrightarrow>
       RRLoopThree.enables I l (Actor h) get \<Longrightarrow>
       ((Actor h', hs), n) \<in> RRLoopThree.lgra G l' \<Longrightarrow>
       Actor h \<in> hs \<or> h = h'\<Longrightarrow>
       I' =
       RRLoopThree.infrastructure.Infrastructure
        (RRLoopThree.igraph.Lgraph (RRLoopThree.gra G) (RRLoopThree.agra G) (RRLoopThree.cgra G)
          ((RRLoopThree.lgra G)(l := RRLoopThree.lgra G l \<union> {((Actor h', hs), n)})))
        (RRLoopThree.delta I) \<Longrightarrow>
       rmapR s \<rightarrow>\<^sub>n rmapR s'"
    apply (rule_tac I = "rmapR s" and I' = "rmapR s'" and l = l and h = h and l' = l' and 
                                  n = n
         in RRLoopTwo.state_transition_in.get_data)
  apply (rule refl)
        apply (simp add: rmapR_def ref_map_def atI_def RRLoopTwo.atI_def)
                apply (simp add: rmapR_def ref_map_def nodes_def RRLoopTwo.nodes_def)
           apply (simp add: rmapR_def ref_map_def nodes_def RRLoopTwo.nodes_def)
      prefer 2
       apply (simp add: rmapR_def ref_map_def)
(* *)
      prefer 2
      apply (simp add: rmapR_def ref_map_def)
     prefer 2
      apply (simp add: rmapR_def ref_map_def)
(* enables get*)
 apply (simp add: rmapR_def ref_map_def enables_def RRLoopTwo.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policiesT_def local_policiesR_def hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def
                 atI_def RRLoopTwo.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
     apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopTwo.has_def atI_def 
                RRLoopTwo.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopTwo.has_def atI_def 
                RRLoopTwo.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
     apply (rule impI)+
(* *)
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopTwo.has_def atI_def 
                RRLoopTwo.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
        apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
  apply (subgoal_tac "RRLoopThree.nodes (RRLoopThree.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
    by blast 
(* eval *)
next show "\<And>(s::RRLoopThree.infrastructure) (s'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (h'::char list) (hs::actor set)
       (n::char list) (I'::RRLoopThree.infrastructure) f::label_fun.
       (hc_scenarioR, s) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopThree.nodes (RRLoopThree.graphI hc_scenarioR) = RRLoopThree.nodes (RRLoopThree.graphI s) \<Longrightarrow>
       RRLoopThree.delta hc_scenarioR = RRLoopThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
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
           (l := RRLoopThree.lgra G l - {(y::actor \<times> actor set, x::char list). x = n} \<union>
                 {f \<Updown> ((Actor h', hs), n)})))
        (RRLoopThree.delta I) \<Longrightarrow>
       rmapR s \<rightarrow>\<^sub>n rmapR s'"
    apply (rule_tac I = "rmapR s" and I' = "rmapR s'" and l = l and h = h and 
                     n = n  and f = "Rep_label_fun f"
           in RRLoopTwo.state_transition_in.process)
  apply (rule refl)
        apply (simp add: rmapR_def ref_map_def atI_def RRLoopTwo.atI_def)
                apply (simp add: rmapR_def ref_map_def nodes_def RRLoopTwo.nodes_def)
      prefer 2
       apply (simp add: rmapR_def ref_map_def)
      prefer 2
      apply (simp add: rmapR_def ref_map_def)
     prefer 2
      apply (simp add: rmapR_def ref_map_def secure_process_def)
(* enables eval *)
 apply (simp add: rmapR_def ref_map_def enables_def RRLoopTwo.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policiesT_def local_policiesR_def hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def
                 atI_def RRLoopTwo.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
  apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopTwo.has_def atI_def 
                RRLoopTwo.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopTwo.has_def atI_def 
                RRLoopTwo.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopTwo.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
        apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
  apply (subgoal_tac "RRLoopThree.nodes (RRLoopThree.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
    by blast 
(* delete *)
next show "\<And>(s::RRLoopThree.infrastructure) (s'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (hs::actor set) (n::char list)
       I'::RRLoopThree.infrastructure.
       (hc_scenarioR, s) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopThree.nodes (RRLoopThree.graphI hc_scenarioR) = RRLoopThree.nodes (RRLoopThree.graphI s) \<Longrightarrow>
       RRLoopThree.delta hc_scenarioR = RRLoopThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopThree.graphI I \<Longrightarrow>
       h \<in> RRLoopThree.actors_graph G \<Longrightarrow>
       l \<in> RRLoopThree.nodes G \<Longrightarrow>
       ((Actor h, hs), n) \<in> RRLoopThree.lgra G l \<Longrightarrow>
       I' =
       RRLoopThree.infrastructure.Infrastructure
        (RRLoopThree.igraph.Lgraph (RRLoopThree.gra G) (RRLoopThree.agra G) (RRLoopThree.cgra G)
          ((RRLoopThree.lgra G)(l := RRLoopThree.lgra G l - {(y::actor \<times> actor set, x::char list). x = n})))
        (RRLoopThree.delta I) \<Longrightarrow>
       rmapR s \<rightarrow>\<^sub>n rmapR s'"
    apply (rule_tac I = "rmapR s" and I' = "rmapR s'" and l = l and h = h and n = n
                     in RRLoopTwo.state_transition_in.del_data)
  apply (rule refl)
       apply (simp add: rmapR_def ref_map_def atI_def RRLoopTwo.actors_graph_def actors_graph_def
                        RRLoopTwo.nodes_def nodes_def)
                apply (simp add: rmapR_def ref_map_def nodes_def RRLoopTwo.nodes_def)

     apply (simp add: rmapR_def ref_map_def)
    by (simp add: rmapR_def ref_map_def)
(* put *)
next show "\<And>(s::RRLoopThree.infrastructure) (s'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (I'::RRLoopThree.infrastructure)
       (hs::actor set) n::char list.
       (hc_scenarioR, s) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopThree.nodes (RRLoopThree.graphI hc_scenarioR) = RRLoopThree.nodes (RRLoopThree.graphI s) \<Longrightarrow>
       RRLoopThree.delta hc_scenarioR = RRLoopThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopThree.graphI I \<Longrightarrow>
       h @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> RRLoopThree.nodes G \<Longrightarrow>
       RRLoopThree.enables I l (Actor h) put \<Longrightarrow>
       I' =
       RRLoopThree.infrastructure.Infrastructure
        (RRLoopThree.igraph.Lgraph (RRLoopThree.gra G) (RRLoopThree.agra G) (RRLoopThree.cgra G)
          ((RRLoopThree.lgra G)(l := RRLoopThree.lgra G l \<union> {((Actor h, hs), n)})))
        (RRLoopThree.delta I) \<Longrightarrow>
       rmapR s \<rightarrow>\<^sub>n rmapR s'"
    apply (rule_tac I = "rmapR s" and I' = "rmapR s'" and l = l and h = h and n = n
                     in RRLoopTwo.state_transition_in.put)
  apply (rule refl)
       apply (simp add: rmapR_def ref_map_def atI_def RRLoopTwo.atI_def)
     apply (simp add: rmapR_def ref_map_def RRLoopTwo.nodes_def nodes_def)
       prefer 2
     apply (simp add: rmapR_def ref_map_def)
(* enables put*)
 apply (simp add: rmapR_def ref_map_def enables_def RRLoopTwo.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI,assumption)
  apply(simp add: local_policiesT_def local_policiesR_def hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def
                 atI_def RRLoopTwo.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
  apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopTwo.has_def atI_def 
                RRLoopTwo.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopTwo.has_def atI_def 
                RRLoopTwo.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopTwo.has_def atI_def 
                RRLoopTwo.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
        apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
  apply (subgoal_tac "RRLoopThree.nodes (RRLoopThree.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospitalT_def sphoneT_def
                  homeT_def cloudT_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
    by blast 
qed

theorem refmapTwo: "hc_KripkeT  \<sqsubseteq>\<^sub>rmapR hc_KripkeR" 
proof (rule strong_mt', simp add: hc_KripkeR_def hc_KripkeT_def hc_statesT_def hc_statesR_def state_transition_refl_def, rule conjI)
  show "rmapR hc_scenarioR = hc_scenarioT"
    apply (simp add: rmapR_def ref_map_def hc_scenarioR_def hc_scenarioT_def ex_graphR_def ex_graphT_def
           homeR_def homeT_def cloudR_def cloudT_def sphoneR_def sphoneT_def hospitalR_def hospitalT_def
           ex_locR_ass_def ex_locT_ass_def ex_credsR_def ex_credsT_def
           ex_locsR_def ex_locsT_def) 
    apply (rule ext)
by (simp add: hospitalR_def hospitalT_def)
next show "\<forall>s::RRLoopThree.infrastructure.
       (hc_scenarioR, s) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>i y}\<^sup>* \<longrightarrow>
       (\<forall>s'::RRLoopThree.infrastructure. s \<rightarrow>\<^sub>i s' \<longrightarrow> rmapR s \<rightarrow>\<^sub>i rmapR s')"
    apply (unfold state_transition_infra_def RRLoopTwo.state_transition_infra_def)
    by (rule refmapTwo_lem)
qed

(* show attack "Eve can do put at cloud"  *)
lemma step1: "hc_scenarioR \<rightarrow>\<^sub>n hc_scenarioR'"
proof (rule_tac l = homeR and h = "''Patient''" and l' = cloudR in move)
  show "graphI hc_scenarioR = graphI hc_scenarioR" by (rule refl)
next show "''Patient'' @\<^bsub>graphI hc_scenarioR\<^esub> homeR" 
    by (simp add: hc_scenarioR_def ex_graphR_def ex_locR_ass_def atI_def nodes_def)
next show "homeR \<in> nodes (graphI hc_scenarioR)"
    by (simp add: hc_scenarioR_def ex_graphR_def ex_locR_ass_def atI_def nodes_def, blast)
next show "cloudR \<in> nodes (graphI hc_scenarioR)"
    by (simp add: hc_scenarioR_def nodes_def ex_graphR_def, blast)
next show "''Patient'' \<in> actors_graph (graphI hc_scenarioR)"
    by (simp add: actors_graph_def hc_scenarioR_def ex_graphR_def ex_locR_ass_def nodes_def, blast)
next show "enables hc_scenarioR cloudR (Actor ''Patient'') move"
    by (simp add: enables_def hc_scenarioR_def ex_graphR_def local_policiesR_def
                    ex_credsR_def ex_locsR_def has_def credentials_def)
next show "hc_scenarioR' =
    Infrastructure (move_graph_a ''Patient'' homeR cloudR (graphI hc_scenarioR)) (delta hc_scenarioR)"
    apply (simp add: hc_scenarioR'_def ex_graphR'_def move_graph_a_def 
                   hc_scenarioR_def ex_graphR_def homeR_def cloudR_def hospitalR_def
                    ex_locR_ass_def ex_credsR_def)
    apply (rule ext)
    by (simp add: hospitalR_def)
qed

lemma step1r: "hc_scenarioR  \<rightarrow>\<^sub>n* hc_scenarioR'"
proof (simp add: state_transition_in_refl_def)
  show " (hc_scenarioR, hc_scenarioR') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  by (insert step1, auto)
qed

lemma step2: "hc_scenarioR'  \<rightarrow>\<^sub>n hc_scenarioR''"
proof (rule_tac l = hospitalR and h = "''Eve''" and l' = cloudR in move, rule refl)
  show "''Eve'' @\<^bsub>graphI hc_scenarioR'\<^esub> hospitalR"
   by (simp add: hc_scenarioR'_def ex_graphR'_def hospitalR_def cloudR_def atI_def nodes_def)
next show "hospitalR \<in> nodes (graphI hc_scenarioR')"
    by (simp add: hc_scenarioR'_def ex_graphR'_def hospitalR_def cloudR_def atI_def nodes_def, blast)
next show "cloudR \<in> nodes (graphI hc_scenarioR')"
    by (simp add: hc_scenarioR'_def nodes_def ex_graphR'_def, blast)
next show "''Eve'' \<in> actors_graph (graphI hc_scenarioR')"
    by (simp add: actors_graph_def hc_scenarioR'_def ex_graphR'_def nodes_def
                     hospitalR_def cloudR_def, blast)
next show "enables hc_scenarioR' cloudR (Actor ''Eve'') move"
    by (simp add: enables_def hc_scenarioR'_def ex_graphR_def local_policiesR_def
                  ex_credsR_def ex_locsR_def has_def credentials_def cloudR_def sphoneR_def)
next show "hc_scenarioR'' =
    Infrastructure (move_graph_a ''Eve'' hospitalR cloudR (graphI hc_scenarioR')) (delta hc_scenarioR')"
    apply (simp add: hc_scenarioR'_def ex_graphR''_def move_graph_a_def hc_scenarioR''_def 
                     ex_graphR'_def homeR_def cloudR_def hospitalR_def ex_credsR_def)
    apply (rule ext)
    apply (simp add: hospitalR_def)
    by blast
qed

lemma step2r: "hc_scenarioR'  \<rightarrow>\<^sub>n* hc_scenarioR''"
proof (simp add: state_transition_in_refl_def)
  show "(hc_scenarioR', hc_scenarioR'') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step2, auto)
qed

(* Second attack: Eve can go to cloud and override Bob's data
   (that she got from outside the system) and pass it as her own 
   (labeling it as hers) because the policy allows Eve to put on cloud. *)
(* Note the first bunch of lemmas develops the attack refinement *)
lemma hcR_ref: "[\<N>\<^bsub>(IhcR,shcR)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcR,shcR)\<^esup> \<sqsubseteq>
                  [\<N>\<^bsub>(IhcR,HCR')\<^esub>, \<N>\<^bsub>(HCR',shcR)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcR,shcR)\<^esup>"  
proof (rule_tac l = "[]" and l' = "[\<N>\<^bsub>(IhcR,HCR')\<^esub>, \<N>\<^bsub>(HCR',shcR)\<^esub>]" and
                  l'' = "[]" and si = IhcR and si' = IhcR and 
                  si'' = shcR and si''' = shcR in refI, simp, rule refl)
  show "([\<N>\<^bsub>(IhcR, HCR')\<^esub>, \<N>\<^bsub>(HCR', shcR)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcR, shcR)\<^esup>) =
    ([] @ [\<N>\<^bsub>(IhcR, HCR')\<^esub>, \<N>\<^bsub>(HCR', shcR)\<^esub>] @ [] \<oplus>\<^sub>\<and>\<^bsup>(IhcR, shcR)\<^esup>)"
  by simp
qed

lemma att_hcR: "\<turnstile>[\<N>\<^bsub>(IhcR,HCR')\<^esub>, \<N>\<^bsub>(HCR',shcR)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcR,shcR)\<^esup>"
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(IhcR, HCR')\<^esub>"
   apply (simp add: IhcR_def HCR'_def att_base)
   apply (subst state_transition_infra_def)
   by (rule step1)
next show "\<turnstile>[\<N>\<^bsub>(HCR', shcR)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(HCR', shcR)\<^esup>"
   apply (subst att_and, simp)
   apply (simp add: HCR'_def shcR_def att_base)
   apply (subst state_transition_infra_def)
   apply (rule_tac x = hc_scenarioR'' in exI)
   apply (rule conjI)
   apply (simp add: global_policyR_def hc_scenarioR''_def hc_actorsR_def 
                    enables_def local_policiesR_def cloudR_def sphoneR_def)
    by (rule step2)
qed

lemma hcR_abs_att: "\<turnstile>\<^sub>V [\<N>\<^bsub>(IhcR,shcR)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcR,shcR)\<^esup>"
proof (rule ref_valI, rule hcR_ref, rule att_hcR)
qed

lemma hcR_att: "hc_KripkeR \<turnstile> EF {x. \<not>(global_policyR x ''Eve'')}"
proof -
  have a: " \<turnstile>[\<N>\<^bsub>(IhcR, HCR')\<^esub>, \<N>\<^bsub>(HCR', shcR)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcR, shcR)\<^esup>"
    by (rule att_hcR)
  hence "(IhcR,shcR) = attack ([\<N>\<^bsub>(IhcR, HCR')\<^esub>, \<N>\<^bsub>(HCR', shcR)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IhcR, shcR)\<^esup>)"
    by simp
  hence "Kripke {s::infrastructure. \<exists>i::infrastructure\<in>IhcR. i \<rightarrow>\<^sub>i* s} IhcR \<turnstile> EF shcR"
    apply (insert a)
    apply (erule AT_EF)
    by simp
  thus  "hc_KripkeR \<turnstile> EF {x::infrastructure. \<not> global_policyR x ''Eve''}"
    by (simp add: hc_KripkeR_def hc_statesR_def IhcR_def shcR_def)
qed


theorem hc_EFR: "hc_KripkeR \<turnstile> EF shcR"  
proof (insert hcR_att, simp add: shcR_def) 
qed

(* Privacy preservation *)
lemma priv_pres: "h \<in> hc_actorsR \<Longrightarrow> l \<in> hc_locationsR \<Longrightarrow>
         owns (Igraph hc_scenarioR) l (Actor h) d \<Longrightarrow>
         hc_KripkeR \<turnstile> AG {x. \<forall> l \<in> hc_locationsR. owns (Igraph x) l (Actor h) d }"  
proof (simp add: hc_KripkeR_def check_def, rule conjI)
  show "hc_scenarioR \<in> hc_statesR" by (simp add: hc_statesR_def state_transition_refl_def)
next show "h \<in> hc_actorsR \<Longrightarrow>
    l \<in> hc_locationsR \<Longrightarrow>
    owns (Igraph hc_scenarioR) l (Actor h) d \<Longrightarrow>
    hc_scenarioR \<in> AG {x::infrastructure. \<forall>l::location\<in>hc_locationsR. owns (Igraph x) l (Actor h) d}"
      apply (unfold AG_def)
      apply (simp add: gfp_def)
      apply (rule_tac x = "{x::infrastructure. \<forall>l::location\<in>hc_locationsR. owns (Igraph x) l (Actor h) d}" in exI)
      apply (rule conjI)
      apply (rule subset_refl)
      apply (rule conjI)
      apply (unfold AX_def)
      apply (simp add: owns_def)
      by (simp add: hc_scenarioR_def owns_def)
  qed

(* This is the global policy expressing data privacy *)
(* It cannot be proved justly because Eve can steal and put Bob's data on the cloud labeled as her own *)
lemma global_policy: \<open>(\<forall> (l :: location) \<in> nodes(graphI I). (\<forall> l' \<in> nodes(graphI I). 
     \<forall> d:: data. \<forall> lb:: dlm. \<forall> lb':: dlm. 
         (lb, d) \<in> (lgra(graphI I) l) \<longrightarrow> (lb', d) \<in> (lgra(graphI I) l') \<longrightarrow> lb = lb')) \<close>
  oops

end
end
 