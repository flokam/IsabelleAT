theory hcKripkeThree
imports RRLoopThree
begin

locale scenarioHCKripkeThree = scenarioHCKripkeOne +
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
             ({((Actor ''Patient'',[Actor ''Doctor'']),''42'')}) 
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

fixes rmapR :: "RRLoopThree.infrastructure \<Rightarrow> RRLoopOne.infrastructure"
defines rmapR_def:
"rmapR I \<equiv> ref_map I local_policies"

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
 in RRLoopOne.state_transition_in.move)
  apply (rule refl)
            apply (simp add: rmapR_def ref_map_def atI_def RRLoopOne.atI_def)
           apply (simp add: rmapR_def ref_map_def nodes_def RRLoopOne.nodes_def)
           apply (simp add: rmapR_def ref_map_def nodes_def RRLoopOne.nodes_def)
         apply (simp add: rmapR_def ref_map_def actors_graph_def RRLoopOne.actors_graph_def)
         apply (rule_tac x = l in exI)
         apply (simp add: nodes_def RRLoopOne.nodes_def atI_def)
  prefer 2
        apply (simp add: rmapR_def ref_map_def move_graph_a_def RRLoopOne.move_graph_a_def)
  apply (simp add: rmapR_def ref_map_def enables_def RRLoopOne.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policies_def local_policiesR_def hospital_def sphoneR_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def
                 atI_def RRLoopOne.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
  apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policies_def local_policiesR_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
        apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
  apply (subgoal_tac "RRLoopThree.nodes (RRLoopThree.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
  apply (simp add: hospital_def sphone_def RRLoopThree.nodes_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
   apply (simp add: local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
   apply (simp add: hospital_def sphone_def RRLoopThree.nodes_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
  by blast
(* get *)
next show "\<And>(s::RRLoopThree.infrastructure) (s'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (l'::location) (h'::char list)
       (hs::actor list) (n::char list) I'::RRLoopThree.infrastructure.
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
       Actor h \<in> set hs \<Longrightarrow>
       I' =
       RRLoopThree.infrastructure.Infrastructure
        (RRLoopThree.igraph.Lgraph (RRLoopThree.gra G) (RRLoopThree.agra G) (RRLoopThree.cgra G)
          ((RRLoopThree.lgra G)(l := RRLoopThree.lgra G l \<union> {((Actor h', hs), n)})))
        (RRLoopThree.delta I) \<Longrightarrow>
       rmapR s \<rightarrow>\<^sub>n rmapR s'"
    apply (rule_tac I = "rmapR s" and I' = "rmapR s'" and l = l and h = h and l' = l' and 
                                  s = "dmap ((Actor h', hs), n)"
         in RRLoopOne.state_transition_in.get)
  apply (rule refl)
        apply (simp add: rmapR_def ref_map_def atI_def RRLoopOne.atI_def)
                apply (simp add: rmapR_def ref_map_def nodes_def RRLoopOne.nodes_def)
           apply (simp add: rmapR_def ref_map_def nodes_def RRLoopOne.nodes_def)
      prefer 2
      apply (simp add: rmapR_def ref_map_def)
      apply (subgoal_tac "finite(RRLoopThree.lgra (RRLoopThree.graphI I) l')")
       apply (drule_tac n = "((Actor h', hs), n)" and f = "dmap" in fmap_lem_map)
        apply assumption
    apply simp
      apply (subgoal_tac "\<forall> l. finite (RRLoopThree.lgra (RRLoopThree.graphI I) l)")
       apply (erule spec)
      apply (erule finite_data0)
(* *)
      prefer 2
      apply (simp add: rmapR_def ref_map_def)
     apply (rule ext)
     apply simp
    apply (rule impI)
     apply (subst fmap_lem)
      prefer 2
      apply simp
      apply (subgoal_tac "\<forall> l. finite (RRLoopThree.lgra (RRLoopThree.graphI I) l)")
       apply (erule spec)
     apply (erule finite_data0)
(* enables get*)
 apply (simp add: rmapR_def ref_map_def enables_def RRLoopOne.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policies_def local_policiesR_def hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def
                 atI_def RRLoopOne.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
     apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopThree.credentials_def)

         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
     apply (rule impI)+
(* *)
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
        apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
  apply (subgoal_tac "RRLoopThree.nodes (RRLoopThree.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
    by blast 
(* eval *)
next show "\<And>(s::RRLoopThree.infrastructure) (s'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (h'::char list) (hs::actor list)
       (n::char list) (I'::RRLoopThree.infrastructure) f::label_fun.
       (hc_scenarioR, s)
       \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopThree.nodes (RRLoopThree.graphI hc_scenarioR) = RRLoopThree.nodes (RRLoopThree.graphI s) \<Longrightarrow>
       RRLoopThree.delta hc_scenarioR = RRLoopThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopThree.graphI I \<Longrightarrow>
       h @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> RRLoopThree.nodes G \<Longrightarrow>
       RRLoopThree.enables I l (Actor h) eval \<Longrightarrow>
       ((Actor h', hs), n) \<in> RRLoopThree.lgra G l \<Longrightarrow>
       Actor h \<in> set hs \<or> h = h' \<Longrightarrow>
       I' =
       RRLoopThree.infrastructure.Infrastructure
        (RRLoopThree.igraph.Lgraph (RRLoopThree.gra G) (RRLoopThree.agra G) (RRLoopThree.cgra G)
          ((RRLoopThree.lgra G)
           (l := RRLoopThree.lgra G l - {((Actor h', hs), n)} \<union> {f \<Updown> ((Actor h', hs), n)})))
        (RRLoopThree.delta I) \<Longrightarrow>
       rmapR s \<rightarrow>\<^sub>n rmapR s'"
    apply (rule_tac I = "rmapR s" and I' = "rmapR s'" and l = l and h = h and 
                     n = "dmap ((Actor h', hs), n)"  and 
                 f = "\<lambda> x. dmap (f  \<Updown> ((Actor h', hs), trunc (flat_label (Actor h', hs)) x))"
           in RRLoopOne.state_transition_in.process)
  apply (rule refl)
        apply (simp add: rmapR_def ref_map_def atI_def RRLoopOne.atI_def)
                apply (simp add: rmapR_def ref_map_def nodes_def RRLoopOne.nodes_def)
      prefer 2
      apply (simp add: rmapR_def ref_map_def)
      apply (subgoal_tac "finite(RRLoopThree.lgra (RRLoopThree.graphI I) l)")
       apply (drule_tac n = "((Actor h', hs), n)" and f = "dmap" in fmap_lem_map)
        apply assumption+

       apply (subgoal_tac "\<forall> l. finite (RRLoopThree.lgra (RRLoopThree.graphI I) l)")
    apply simp
       apply (erule finite_data0)
(* *)
      prefer 2
      apply (simp add: rmapR_def ref_map_def)
     apply (rule ext)
     apply simp
    apply (rule impI)
     apply (subst fmap_lem)
       apply (subgoal_tac "\<forall> l. finite (RRLoopThree.lgra (RRLoopThree.graphI I) l)")
    apply simp
      apply (erule finite_data0)
      apply (subgoal_tac "(fmap dmap (RRLoopThree.lgra (RRLoopThree.graphI I) l - {((Actor h', hs), n)}) =
                        (fmap dmap (RRLoopThree.lgra (RRLoopThree.graphI I) l) - {dmap ((Actor h', hs), n)}))")
    apply (rotate_tac -1)
      apply (erule ssubst)
      apply (subst trunc_dmap)
    apply (rule refl)
     apply (subst fmap_lem_del)
       apply (subgoal_tac "\<forall> l. finite (RRLoopThree.lgra (RRLoopThree.graphI I) l)")
    apply simp
      apply (erule finite_data0)
    apply (rule dmap_inj, rule no_insider)
      apply assumption
    apply (rule refl)
(* enables eval *)
 apply (simp add: rmapR_def ref_map_def enables_def RRLoopOne.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policies_def local_policiesR_def hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def
                 atI_def RRLoopOne.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
  apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
        apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
  apply (subgoal_tac "RRLoopThree.nodes (RRLoopThree.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
    by blast 
(* delete *)
next show "\<And>(s::RRLoopThree.infrastructure) (s'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (actors::RRLoopThree.igraph \<Rightarrow> char list set)
       (l::location) (hs::actor list) (n::char list) I'::RRLoopThree.infrastructure.
       (hc_scenarioR, s)
       \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       RRLoopThree.nodes (RRLoopThree.graphI hc_scenarioR) = RRLoopThree.nodes (RRLoopThree.graphI s) \<Longrightarrow>
       RRLoopThree.delta hc_scenarioR = RRLoopThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = RRLoopThree.graphI I \<Longrightarrow>
       h \<in> actors_graph G \<Longrightarrow>
       l \<in> RRLoopThree.nodes G \<Longrightarrow>
       ((Actor h, hs), n) \<in> RRLoopThree.lgra G l \<Longrightarrow>
       I' =
       RRLoopThree.infrastructure.Infrastructure
        (RRLoopThree.igraph.Lgraph (RRLoopThree.gra G) (RRLoopThree.agra G) (RRLoopThree.cgra G)
          ((RRLoopThree.lgra G)(l := RRLoopThree.lgra G l - {((Actor h, hs), n)})))
        (RRLoopThree.delta I) \<Longrightarrow>
       rmapR s \<rightarrow>\<^sub>n rmapR s'"
    apply (rule_tac I = "rmapR s" and I' = "rmapR s'" and l = l and h = h and n = "dmap ((Actor h, hs), n)"
                     in RRLoopOne.state_transition_in.del_data)
  apply (rule refl)
       apply (simp add: rmapR_def ref_map_def atI_def RRLoopOne.actors_graph_def actors_graph_def
                        RRLoopOne.nodes_def nodes_def)
                apply (simp add: rmapR_def ref_map_def nodes_def RRLoopOne.nodes_def)
      prefer 2
     apply (simp add: rmapR_def ref_map_def)
     apply (rule ext)
     apply simp
    apply (rule impI)
     apply (subst fmap_lem_del)
      apply (subgoal_tac "\<forall> l. finite (RRLoopThree.lgra (RRLoopThree.graphI I) l)")
       apply (erule spec)
        apply (erule finite_data0)
    apply (rule dmap_inj, rule no_insider)
    apply simp+
     apply (simp add: rmapR_def ref_map_def)
      apply (subgoal_tac "finite(RRLoopThree.lgra (RRLoopThree.graphI I) l)")
       apply (drule_tac n = "((Actor h, hs), n)" and f = "dmap" in fmap_lem_map)
        apply assumption
       apply simp
      apply (subgoal_tac "\<forall> l. finite (RRLoopThree.lgra (RRLoopThree.graphI I) l)")
       apply (erule spec)
by (erule finite_data0)
(* put *)
next show "\<And>(s::RRLoopThree.infrastructure) (s'::RRLoopThree.infrastructure) (G::RRLoopThree.igraph)
       (I::RRLoopThree.infrastructure) (h::char list) (l::location) (I'::RRLoopThree.infrastructure)
       (hs::actor list) n::char list.
       (hc_scenarioR, s)
       \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
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
    apply (rule_tac I = "rmapR s" and I' = "rmapR s'" and l = l and h = h and n = "dmap ((Actor h, hs), n)"
                     in RRLoopOne.state_transition_in.put)
  apply (rule refl)
       apply (simp add: rmapR_def ref_map_def atI_def RRLoopOne.atI_def)
      prefer 2
     apply (simp add: rmapR_def ref_map_def)
     apply (rule ext)
     apply simp
    apply (rule impI)
     apply (subst fmap_lem)
      apply (subgoal_tac "\<forall> l. finite (RRLoopThree.lgra (RRLoopThree.graphI I) l)")
       apply (erule spec)
      apply (erule finite_data0)
    apply simp
    apply (simp add: rmapR_def ref_map_def)
(* enables put*)
 apply (simp add: rmapR_def ref_map_def enables_def RRLoopOne.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI,assumption)
  apply(simp add: local_policies_def local_policiesR_def hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def
                 atI_def RRLoopOne.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
  apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
         apply (simp add: has_def RRLoopOne.has_def atI_def 
                RRLoopOne.credentials_def RRLoopThree.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioR_def local_policiesR_def)
        apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
  apply (subgoal_tac "RRLoopThree.nodes (RRLoopThree.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: hc_scenarioR_def local_policiesR_def ex_graphR_def RRLoopThree.nodes_def)
  apply (simp add: hospital_def sphone_def
                  home_def cloud_def cloudR_def homeR_def sphoneR_def hospitalR_def hc_scenarioR_def)
    by blast 
qed

theorem refmapTwo: "hc_Kripke  \<sqsubseteq>\<^sub>rmapR hc_KripkeR" 
proof (rule strong_mt', simp add: hc_KripkeR_def hc_Kripke_def hc_states_def hc_statesR_def state_transition_refl_def, rule conjI)
  show "rmapR hc_scenarioR = hc_scenario"
    apply (simp add: rmapR_def ref_map_def hc_scenarioR_def hc_scenario_def ex_graphR_def ex_graph_def
           homeR_def home_def cloudR_def cloud_def sphoneR_def sphone_def hospitalR_def hospital_def
           ex_locR_ass_def ex_loc_ass_def ex_credsR_def ex_creds_def
           ex_locsR_def ex_locs_def) 
    apply (rule conjI)
     apply (unfold hospitalR_def hospital_def, rule refl)
    apply (rule ext)
    apply simp
    apply (rule conjI)
     apply (rule impI)
     apply (simp add: fmap_def fold_one)
         apply (rule dmap_ex, rule no_insider)
    by (simp add: fmap_def)
next show "\<forall>s::RRLoopThree.infrastructure.
       (hc_scenarioR, s) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>i y}\<^sup>* \<longrightarrow>
       (\<forall>s'::RRLoopThree.infrastructure. s \<rightarrow>\<^sub>i s' \<longrightarrow> rmapR s \<rightarrow>\<^sub>i rmapR s')"
    apply (unfold state_transition_infra_def RRLoopOne.state_transition_infra_def)
    by (rule refmapTwo_lem)
qed

(* show attack "Eve can do put at cloud"  *)
theorem hc_EFR: "hc_KripkeR \<turnstile> EF shcR"  
  sorry

end
end
 