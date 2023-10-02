theory LedgerhcKripke
imports LedgerRRLoopFour
begin

locale scenarioHCKripkeFour = scenarioHCKripkeThree +
fixes hc_actorsF :: "identity set"
defines hc_actorsF_def: "hc_actorsF \<equiv> {''Patient'', ''Doctor''}"
fixes hc_locationsF :: "location set"
defines hc_locationsF_def: \<open>hc_locationsF \<equiv> 
          {Location 0, Location 1, Location 2, Location 3}\<close>

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
          (\<lambda> d. if d = ''42'' then Some((Actor ''Patient'',{Actor ''Doctor''}), {cloudF}) else None)"


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

fixes rmapF :: "LedgerRRLoopFour.infrastructure \<Rightarrow> RRLoopThree.infrastructure"
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
assumes no_fake_id: "surj Actor"

begin

 lemma same_nodes0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> nodes(graphI z) = nodes(graphI z')"   
    apply clarify
  apply (erule LedgerRRLoopFour.state_transition_in.cases)
  by (simp add: move_graph_a_def atI_def actors_graph_def nodes_def)+

lemma same_nodes: "(hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
\<Longrightarrow> LedgerRRLoopFour.nodes (graphI hc_scenarioF) = LedgerRRLoopFour.nodes (graphI s)"
  apply (erule rtrancl_induct)
   apply (rule refl)
  apply (drule CollectD)
    apply simp
    apply (drule same_nodes0)
  by simp  

lemma finite_nodes: \<open>(hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
\<Longrightarrow> finite(nodes (graphI hc_scenarioF)) \<Longrightarrow> finite(nodes (graphI s))\<close>
  using local.same_nodes by force

lemma finite_nodes_hcF: \<open>finite(nodes (graphI hc_scenarioF))\<close>
  apply (simp add: hc_scenarioF_def ex_graphF_def LedgerRRLoopFour.nodes_def
                   homeF_def cloudF_def hospitalF_def sphoneF_def)
  apply (subgoal_tac \<open>{x::location.
      \<exists>y::location.
         x = Location (Suc (0::nat)) \<and> y = Location (3::nat) \<or>
         x = Location (0::nat) \<and> y = Location (3::nat) \<or>
         x = Location (3::nat) \<and> y = Location (2::nat) \<or>
         y = Location (Suc (0::nat)) \<and> x = Location (3::nat) \<or>
         y = Location (0::nat) \<and> x = Location (3::nat) \<or>
         y = Location (3::nat) \<and> x = Location (2::nat)}
   \<subseteq> {Location (0:: nat),Location (1:: nat), 
      Location (2:: nat),Location (3:: nat)}\<close>)
  prefer 2
   apply fastforce
  by (erule finite_subset, simp)

lemma owner_actors_init: \<open>\<forall>(s::char list) (hs::actor set) (n::char list) l::location.
       ((Actor s, hs), n)
       \<in> RRLoopThree.lgra (RRLoopThree.graphI (hc_scenarioR::RRLoopThree.infrastructure)) l \<longrightarrow>
       s \<in> RRLoopThree.actors_graph (RRLoopThree.graphI hc_scenarioR)\<close>
  apply (simp add: hc_scenarioR_def ex_graphR_def RRLoopThree.actors_graph_def
                   RRLoopThree.nodes_def)
  by (smt (verit, best) Actor_iff empty_iff ex_locR_ass_def ex_locsR_def fst_conv insert_iff)

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

lemma outside_dom_empty_one_step[rule_format]: \<open>\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>
      ((\<forall>l::location.
           l \<notin> RRLoopThree.nodes (RRLoopThree.graphI z) \<longrightarrow>
           RRLoopThree.lgra (RRLoopThree.graphI z) l = {}) \<longrightarrow>
       (\<forall>l::location.
           l \<notin> RRLoopThree.nodes (RRLoopThree.graphI z') \<longrightarrow>
           RRLoopThree.lgra (RRLoopThree.graphI z') l = {}))\<close>
    apply clarify
  apply (erule RRLoopThree.state_transition_in.cases)
  apply (smt (verit, ccfv_threshold) RRLoopThree.graphI.simps RRLoopThree.lgra.simps RRLoopThree.move_graph_a_def RRLoopThree.same_nodes0 RRLoopThree.state_transition_in.move)
  apply (metis (no_types, lifting) RRLoopThree.graphI.simps RRLoopThree.lgra.simps RRLoopThree.same_nodes0 RRLoopThree.state_transition_in.get_data fun_upd_apply)
  using RRLoopThree.nodes_def apply force
  using RRLoopThree.nodes_def apply auto[1]
  by (metis RRLoopThree.graphI.simps RRLoopThree.lgra.simps RRLoopThree.same_nodes0 RRLoopThree.state_transition_in.put fun_upd_apply)

lemma outside_dom_empty_step: \<open>
       (hc_scenarioR, s) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
  \<Longrightarrow>     (\<forall>l::location.
           l \<notin> RRLoopThree.nodes (RRLoopThree.graphI hc_scenarioR) \<longrightarrow>
           RRLoopThree.lgra (RRLoopThree.graphI hc_scenarioR) l = {}) \<longrightarrow>
       (\<forall>l::location.
           l \<notin> RRLoopThree.nodes (RRLoopThree.graphI s) \<longrightarrow>
           RRLoopThree.lgra (RRLoopThree.graphI s) l = {})\<close>
  apply (erule rtrancl_induct)
  apply simp
  by (simp add: outside_dom_empty_one_step)

lemma outside_dom_empty_hc_scenario: \<open>\<forall>l::location.
           l \<notin> RRLoopThree.nodes (RRLoopThree.graphI hc_scenarioR) \<longrightarrow>
           RRLoopThree.lgra (RRLoopThree.graphI hc_scenarioR) l = {}\<close>
  by (simp add: hc_scenarioR_def ex_graphR_def RRLoopThree.nodes_def ex_locsR_def cloudR_def 
                   homeR_def sphoneR_def hospitalR_def ex_locR_ass_def ex_credsR_def
                   hospitalR_def)  

lemma outside_dom_empty: \<open>\<forall>I''::RRLoopThree.infrastructure.
       hc_scenarioR \<rightarrow>\<^sub>n* I'' \<longrightarrow>
       (\<forall>l::location.
           l \<notin> RRLoopThree.nodes (RRLoopThree.graphI I'') \<longrightarrow>
           RRLoopThree.lgra (RRLoopThree.graphI I'') l = {})\<close>
  using RRLoopThree.state_transition_in_refl_def outside_dom_empty_hc_scenario outside_dom_empty_step by presburger

lemma rtrancl_imp_step: "(I \<rightarrow>\<^sub>n y) \<Longrightarrow>  (I, y) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* "
by (simp add: r_into_rtrancl)


(*
*)

lemma ledger_to_loc_lemO: \<open>ledger_to_loc ((ledgra (LedgerRRLoopFour.graphI I))(d := None)) = 
                          (\<lambda> l. ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I)) l - {(y, x). x = d })\<close>
  apply (rule ext, simp add: ledger_to_loc_def)
  by fastforce

(* Use the del_data_setOO lemma to show that lambda l. lgra (graphI I) l - {(y, x). x = n } = lgra (graphI I') *)
(* More likely show: (I  \<rightarrow>\<^sub>n* Infrastructure (Lgraph (gra (graphI I))(agra (graphI I))(agra (cgra I))
                               (lambda l. lgra (graphI I) l - {(y, x). x = n }))(delta I)          *)
lemma test_thmOOOO: \<open>hc_scenarioR \<rightarrow>\<^sub>n* I \<Longrightarrow>
               (I :: RRLoopThree.infrastructure,
                    RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (RRLoopThree.gra (RRLoopThree.graphI I))
           (RRLoopThree.agra (RRLoopThree.graphI I)) (RRLoopThree.cgra (RRLoopThree.graphI I))
           (\<lambda> l::location. (RRLoopThree.lgra (RRLoopThree.graphI I)) l - {(y::actor \<times> actor set, x::char list). x = d}))
            (RRLoopThree.delta I )) 
\<in>  {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  apply (rule test_thmOOO)
  apply (rule no_insider)
      prefer 3
      apply (rule no_fake_id)
     apply (rule owner_actors_init, assumption)
  using RRLoopThree.finite_nodes RRLoopThree.state_transition_in_refl_def finite_nodes_hcR apply blast
  using outside_dom_empty by blast

(*
lemma test_thmOOO: \<open>(I :: RRLoopThree.infrastructure,
                    RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (RRLoopThree.gra (RRLoopThree.graphI I))
           (RRLoopThree.agra (RRLoopThree.graphI I)) (RRLoopThree.cgra (RRLoopThree.graphI I))
           (\<lambda> l::location. (RRLoopThree.lgra (RRLoopThree.graphI I)) l - {(y::actor \<times> actor set, x::char list). x = d}))
            (RRLoopThree.delta I )) 
\<in>  {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  by (rule test_thm)
*)
lemma test_thmOOOa: \<open>hc_scenarioR \<rightarrow>\<^sub>n* I \<Longrightarrow>
          (I :: RRLoopThree.infrastructure,
                    RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (RRLoopThree.gra (RRLoopThree.graphI I))
           (RRLoopThree.agra (RRLoopThree.graphI I)) (RRLoopThree.cgra (RRLoopThree.graphI I))
           (\<lambda> l::location. (RRLoopThree.lgra (RRLoopThree.graphI I)) l - {(y::actor \<times> actor set, x::char list). x = d}))
            (RRLoopThree.delta I )) 
\<in>  {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  by (rule test_thmOOOO)

(*
lemma test_thmOO: \<open>I' = (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
                      (ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I))))
   \<Longrightarrow> (RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (RRLoopThree.lgra
                (RRLoopThree.graphI
                  (RRLoopThree.infrastructure.Infrastructure I' L))))
         L,
        RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (\<lambda>l::location.
               RRLoopThree.lgra
                (RRLoopThree.graphI
                  (RRLoopThree.infrastructure.Infrastructure I' L))
                l -
               {(y::actor \<times> actor set, x::char list). x = d}))
         L)
       \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  by (metis RRLoopThree.agra.simps RRLoopThree.cgra.simps RRLoopThree.delta.simps RRLoopThree.gra.simps RRLoopThree.graphI.simps RRLoopThree.lgra.simps test_thmOOO)
*)

lemma test_thmOOa: \<open>(I' = (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
                      (ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I))))) \<Longrightarrow>
hc_scenarioR \<rightarrow>\<^sub>n* (RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (RRLoopThree.lgra
                (RRLoopThree.graphI
                  (RRLoopThree.infrastructure.Infrastructure I' L))))
         L :: RRLoopThree.infrastructure)
   \<Longrightarrow>
       (RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (RRLoopThree.lgra
                (RRLoopThree.graphI
                  (RRLoopThree.infrastructure.Infrastructure I' L))))
         L,
        RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (\<lambda>l::location.
               RRLoopThree.lgra
                (RRLoopThree.graphI
                  (RRLoopThree.infrastructure.Infrastructure I' L))
                l -
               {(y::actor \<times> actor set, x::char list). x = d}))
         L)
       \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  by (metis RRLoopThree.agra.simps RRLoopThree.cgra.simps RRLoopThree.delta.simps RRLoopThree.gra.simps RRLoopThree.graphI.simps RRLoopThree.lgra.simps test_thmOOOa)


lemma test_thmO: \<open>
(RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (RRLoopThree.lgra
                (RRLoopThree.graphI
                  (RRLoopThree.infrastructure.Infrastructure
                    (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
                      (ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I))))
                    local_policiesR))))
         local_policiesR,
        RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (\<lambda>l::location.
               RRLoopThree.lgra
                (RRLoopThree.graphI
                  (RRLoopThree.infrastructure.Infrastructure
                    (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
                      (ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I))))
                    local_policiesR))
                l -
               {(y::actor \<times> actor set, x::char list). x = d}))
         local_policiesR)
       \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  oops

lemma test_thmOa: \<open>hc_scenarioR \<rightarrow>\<^sub>n*
RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (RRLoopThree.lgra
                (RRLoopThree.graphI
                  (RRLoopThree.infrastructure.Infrastructure
                    (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
                      (ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I))))
                    local_policiesR))))
         local_policiesR
\<Longrightarrow>
(RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (RRLoopThree.lgra
                (RRLoopThree.graphI
                  (RRLoopThree.infrastructure.Infrastructure
                    (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
                      (ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I))))
                    local_policiesR))))
         local_policiesR,
        RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (\<lambda>l::location.
               RRLoopThree.lgra
                (RRLoopThree.graphI
                  (RRLoopThree.infrastructure.Infrastructure
                    (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
                      (ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I))))
                    local_policiesR))
                l -
               {(y::actor \<times> actor set, x::char list). x = d}))
         local_policiesR)
       \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  by (rule test_thmOOa, rule refl)

(*
lemma refmapThree_lem_del_dataO: \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (L::location set) (d::char list) (as::actor set)
       I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a \<in> LedgerRRLoopFour.actors_graph G \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l \<in> L \<Longrightarrow>
       ledgra G d = Some ((Actor a, as), L) \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G) (LedgerRRLoopFour.cgra G)
          (LedgerRRLoopFour.lgra G) ((ledgra G)(d := None)))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF s, rmapF s') \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  oops
*)


lemma refmapThree_lem_del_data: \<open>
\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (L::location set) (d::char list) (as::actor set)
       I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioR \<rightarrow>\<^sub>n* rmapF I) \<Longrightarrow>
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a \<in> LedgerRRLoopFour.actors_graph G \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l \<in> L \<Longrightarrow>
       ledgra G d = Some ((Actor a, as), L) \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G) (LedgerRRLoopFour.cgra G)
          (LedgerRRLoopFour.lgra G) ((ledgra G)(d := None)))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF s, rmapF s') \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  apply (simp add: rmapF_def ref_map_def)
  apply (subst ledger_to_loc_lemO)
  apply (subgoal_tac \<open>RRLoopThree.lgra(RRLoopThree.graphI(RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I))))
         local_policiesR)) = (ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I)))\<close>)
   prefer 2
   apply simp
  apply (subgoal_tac \<open>(RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I))))
         local_policiesR,
        RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (\<lambda>l::location. ( 
                    RRLoopThree.lgra(RRLoopThree.graphI(RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I))))
         local_policiesR))
                           ) l - {(y::actor \<times> actor set, x::char list). x = d}))
         local_policiesR)
       \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>)
   apply presburger
  apply (subgoal_tac \<open>hc_scenarioR \<rightarrow>\<^sub>n*
RRLoopThree.infrastructure.Infrastructure
         (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
           (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I)) (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
           (RRLoopThree.lgra
                (RRLoopThree.graphI
                  (RRLoopThree.infrastructure.Infrastructure
                    (RRLoopThree.igraph.Lgraph (LedgerRRLoopFour.gra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.agra (LedgerRRLoopFour.graphI I))
                      (LedgerRRLoopFour.cgra (LedgerRRLoopFour.graphI I))
                      (ledger_to_loc (ledgra (LedgerRRLoopFour.graphI I))))
                    local_policiesR))))
         local_policiesR\<close>)
   apply (drule test_thmOa)
by simp+

lemma rmapF_hc_scenarioF: \<open>rmapF hc_scenarioF = hc_scenarioR\<close>
  apply (auto simp add: LedgerRRLoopFour.ref_map_def rmapF_def hc_scenarioF_def hc_scenarioR_def ex_graphF_def
          ex_graphR_def local_policiesF_def local_policiesR_def homeF_def homeR_def
          cloudF_def cloudR_def sphoneF_def sphoneR_def hospitalF_def hospitalR_def
          ex_locF_ass_def ex_credsF_def ex_locsF_def ex_ledger_def 
          ex_locR_ass_def ex_credsR_def ex_locsR_def ledger_to_loc_def)
   apply (unfold hospitalF_def hospitalR_def, rule refl)
  apply (unfold ledger_to_loc_def)
  apply (rule ext)
  apply (rule equalityI)
   prefer 2
   apply (simp add: cloudF_def)+
  by blast

(* *)
lemma reachability_lem: \<open>\<forall>(s::LedgerRRLoopFour.infrastructure).
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (rmapF hc_scenarioF, rmapF s) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  apply clarify
 apply (erule rtrancl_induct)
  apply (simp add: state_transition_refl_def)
  thm rtrancl_trans
  apply (rule rtrancl_trans, assumption)
(* Looks like recreating the lemma refmap_lem that we need to prove?! *)
(* Lets try the same proof structurean and see the delete case ...*)
proof (clarify, frule same_nodes, frule init_state_policy, erule state_transition_in.cases)
  show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (y::LedgerRRLoopFour.infrastructure)
       (z::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (L::location set)
       (d::char list) (as::actor set) I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, y)
       \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure).
           x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (rmapF hc_scenarioF, rmapF y)
       \<in> {a::RRLoopThree.infrastructure \<times> RRLoopThree.infrastructure.
           case a of
           (x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure) \<Rightarrow> x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI y) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta y \<Longrightarrow>
       y = I \<Longrightarrow>
       z = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a \<in> LedgerRRLoopFour.actors_graph G \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l \<in> L \<Longrightarrow>
       ledgra G d = Some ((Actor a, as), L) \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G)
          (LedgerRRLoopFour.cgra G) (LedgerRRLoopFour.lgra G) ((ledgra G)(d := None)))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF y, rmapF z)
       \<in> {a::RRLoopThree.infrastructure \<times> RRLoopThree.infrastructure.
           case a of
           (x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure) \<Rightarrow> x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
    apply (rule_tac I = I in refmapThree_lem_del_data)
    apply (simp add: rmapF_hc_scenarioF state_transition_in_refl_def)
    using RRLoopThree.state_transition_in_refl_def apply presburger
              prefer 10
    by assumption+
next show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (y::LedgerRRLoopFour.infrastructure)
       (z::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (l'::location)
       I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, y)
       \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure).
           x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (rmapF hc_scenarioF, rmapF y)
       \<in> {a::RRLoopThree.infrastructure \<times> RRLoopThree.infrastructure.
           case a of
           (x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure) \<Rightarrow> x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI y) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta y \<Longrightarrow>
       y = I \<Longrightarrow>
       z = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l' \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       a \<in> LedgerRRLoopFour.actors_graph (LedgerRRLoopFour.graphI I) \<Longrightarrow>
       LedgerRRLoopFour.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.move_graph_a a l l' (LedgerRRLoopFour.graphI I))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF y, rmapF z)
       \<in> {a::RRLoopThree.infrastructure \<times> RRLoopThree.infrastructure.
           case a of
           (x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure) \<Rightarrow> x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
    sorry
next show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (y::LedgerRRLoopFour.infrastructure)
       (z::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (l'::location)
       (d::char list) (a'::char list) (as::actor set) (L::location set)
       I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, y)
       \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure).
           x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (rmapF hc_scenarioF, rmapF y)
       \<in> {a::RRLoopThree.infrastructure \<times> RRLoopThree.infrastructure.
           case a of
           (x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure) \<Rightarrow> x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI y) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta y \<Longrightarrow>
       y = I \<Longrightarrow>
       z = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l' \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       LedgerRRLoopFour.enables I l (Actor a) get \<Longrightarrow>
       ledgra G d = Some ((Actor a', as), L) \<Longrightarrow>
       Actor a \<in> as \<or> a = a' \<Longrightarrow>
       l' \<in> L \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G)
          (LedgerRRLoopFour.cgra G) (LedgerRRLoopFour.lgra G)
          (ledgra G(d \<mapsto> ((Actor a', as), L \<union> {l}))))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF y, rmapF z)
       \<in> {a::RRLoopThree.infrastructure \<times> RRLoopThree.infrastructure.
           case a of
           (x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure) \<Rightarrow> x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
    sorry
next show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (y::LedgerRRLoopFour.infrastructure)
       (z::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (L::location set)
       (d::char list) (a'::char list) (as::actor set) (I'::LedgerRRLoopFour.infrastructure)
       f::char list \<Rightarrow> char list.
       (hc_scenarioF, y)
       \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure).
           x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (rmapF hc_scenarioF, rmapF y)
       \<in> {a::RRLoopThree.infrastructure \<times> RRLoopThree.infrastructure.
           case a of
           (x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure) \<Rightarrow> x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI y) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta y \<Longrightarrow>
       y = I \<Longrightarrow>
       z = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       LedgerRRLoopFour.enables I l (Actor a) eval \<Longrightarrow>
       l \<in> L \<Longrightarrow>
       ledgra G d = Some ((Actor a', as), L) \<Longrightarrow>
       Actor a \<in> as \<or> a = a' \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G)
          (LedgerRRLoopFour.cgra G) (LedgerRRLoopFour.lgra G)
          ((ledgra G)(d := None)(f d \<mapsto> ((Actor a', as), L))))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF y, rmapF z)
       \<in> {a::RRLoopThree.infrastructure \<times> RRLoopThree.infrastructure.
           case a of
           (x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure) \<Rightarrow> x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
    sorry
next show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (y::LedgerRRLoopFour.infrastructure)
       (z::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (d::char list)
       (as::actor set) (L::location set) I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, y)
       \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure).
           x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (rmapF hc_scenarioF, rmapF y)
       \<in> {a::RRLoopThree.infrastructure \<times> RRLoopThree.infrastructure.
           case a of
           (x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure) \<Rightarrow> x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI y) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta y \<Longrightarrow>
       y = I \<Longrightarrow>
       z = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       LedgerRRLoopFour.enables I l (Actor a) put \<Longrightarrow>
       ledgra G d = Some ((Actor a, as), L) \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G)
          (LedgerRRLoopFour.cgra G) (LedgerRRLoopFour.lgra G)
          (ledgra G(d \<mapsto> ((Actor a, as), insert l L))))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF y, rmapF z)
       \<in> {a::RRLoopThree.infrastructure \<times> RRLoopThree.infrastructure.
           case a of
           (x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure) \<Rightarrow> x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
    sorry
qed

(* This is now the same as refmapThree_lem_del_data but with the reachability of
   \<open>(hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
   \<close>  left out because this can be proved with the above general reachability theorem 
    reachability_lem *)
lemma refmapThree_lem_del_dataO: \<open>
\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (L::location set) (d::char list) (as::actor set)
       I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a \<in> LedgerRRLoopFour.actors_graph G \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l \<in> L \<Longrightarrow>
       ledgra G d = Some ((Actor a, as), L) \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G) (LedgerRRLoopFour.cgra G)
          (LedgerRRLoopFour.lgra G) ((ledgra G)(d := None)))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF s, rmapF s') \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
  using RRLoopThree.state_transition_in_refl_def reachability_lem refmapThree_lem_del_data rmapF_hc_scenarioF by force


(* Attempting to prove with the refinement lemma strong_mt'''a  does allow to use the 
   reachability at the abstract level as premise but this does not help as in the other
   premise we then have \<rightarrow>* so we cannot directly case analysis but have to apply induction
   which makes somehow reappear the problem of reachability *)
lemma refmapThree_lemO: \<open>\<forall>(s::LedgerRRLoopFour.infrastructure).
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (rmapF hc_scenarioF, rmapF s) \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (s \<rightarrow>\<^sub>n* s' \<longrightarrow> (rmapF s, rmapF s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*)\<close>
  apply  (rule allI, rule impI)
   apply (simp add: state_transition_in_refl_def)
  oops




lemma refmapThree_lem': \<open>\<forall>(s::LedgerRRLoopFour.infrastructure).
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>s'. s \<rightarrow>\<^sub>n s' \<longrightarrow> (rmapF s, rmapF s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*)\<close>
proof (clarify, frule same_nodes, frule init_state_policy, erule state_transition_in.cases)
(* move case *)
  show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (l'::location)
       I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l' \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       a \<in> LedgerRRLoopFour.actors_graph (LedgerRRLoopFour.graphI I) \<Longrightarrow>
       LedgerRRLoopFour.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure (LedgerRRLoopFour.move_graph_a a l l' (LedgerRRLoopFour.graphI I))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF s, rmapF s') \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
proof (rule rtrancl_imp_step, rule_tac I = "rmapF s" and I' = "rmapF s'" and l = l and l' = l' and h = a
       in RRLoopThree.state_transition_in.move, rule refl, simp add: rmapF_def ref_map_def atI_def RRLoopThree.atI_def,
       simp add: rmapF_def ref_map_def nodes_def RRLoopThree.nodes_def, simp add: rmapF_def ref_map_def nodes_def RRLoopThree.nodes_def,
       simp add: rmapF_def ref_map_def actors_graph_def RRLoopThree.actors_graph_def, rule_tac x = l in exI,
       simp add: nodes_def RRLoopThree.nodes_def atI_def)
  show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (l'::location)
       I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l' \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       a \<in> LedgerRRLoopFour.actors_graph (LedgerRRLoopFour.graphI I) \<Longrightarrow>
       LedgerRRLoopFour.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure (LedgerRRLoopFour.move_graph_a a l l' (LedgerRRLoopFour.graphI I))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       rmapF s' =
       RRLoopThree.infrastructure.Infrastructure (RRLoopThree.move_graph_a a l l' (RRLoopThree.graphI (rmapF s)))
        (RRLoopThree.delta (rmapF s))\<close>
    by (simp add: rmapF_def ref_map_def move_graph_a_def RRLoopThree.move_graph_a_def)
next show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (l'::location)
       I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l' \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       a \<in> LedgerRRLoopFour.actors_graph (LedgerRRLoopFour.graphI I) \<Longrightarrow>
       LedgerRRLoopFour.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure (LedgerRRLoopFour.move_graph_a a l l' (LedgerRRLoopFour.graphI I))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       RRLoopThree.enables (rmapF s) l' (Actor a) move\<close>
  apply (simp add: rmapF_def ref_map_def enables_def RRLoopThree.enables_def)
        apply (erule bexE)
  apply (rule_tac x = x in bexI, assumption)
  apply(simp add: local_policiesR_def local_policiesF_def hospitalR_def sphoneF_def
                  homeT_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def
                 atI_def RRLoopThree.atI_def)
        apply (rule conjI)
        apply (rule impI)
        apply (drule sym)
  apply (drule sym)
  apply (simp add: hc_scenarioF_def local_policiesR_def local_policiesF_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def ledger_to_loc_def)
         apply (simp add: has_def RRLoopThree.has_def atI_def 
                RRLoopThree.credentials_def LedgerRRLoopFour.credentials_def)
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
                RRLoopThree.credentials_def LedgerRRLoopFour.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioF_def local_policiesF_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
         apply (simp add: has_def RRLoopTwo.has_def atI_def 
                RRLoopThree.credentials_def LedgerRRLoopFour.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioF_def local_policiesF_def)
        apply (simp add: hc_scenarioF_def local_policiesF_def ex_graphF_def LedgerRRLoopFour.nodes_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
  apply (subgoal_tac "LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: local_policiesF_def ex_graphF_def LedgerRRLoopFour.nodes_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
  apply (simp add: hospitalR_def sphoneR_def LedgerRRLoopFour.nodes_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
   apply (simp add: local_policiesF_def ex_graphF_def LedgerRRLoopFour.nodes_def)
   apply (simp add: hospitalR_def sphoneR_def LedgerRRLoopFour.nodes_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
  by blast
qed
(* get *)
next show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (l'::location) (d::char list) (a'::char list)
       (as::actor set) (L::location set) I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l' \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       LedgerRRLoopFour.enables I l (Actor a) get \<Longrightarrow>
       ledgra G d = Some ((Actor a', as), L) \<Longrightarrow>
       Actor a \<in> as \<or> a = a' \<Longrightarrow>
       l' \<in> L \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G) (LedgerRRLoopFour.cgra G)
          (LedgerRRLoopFour.lgra G) (ledgra G(d \<mapsto> ((Actor a', as), L \<union> {l}))))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF s, rmapF s') \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
proof (rule rtrancl_imp_step, rule_tac I = "rmapF s" and I' = "rmapF s'" and l = l and h = a and h' = a' and l' = l' and n = d
       in RRLoopThree.state_transition_in.get_data, rule refl, simp add: rmapF_def ref_map_def atI_def RRLoopThree.atI_def,
       simp add: rmapF_def ref_map_def nodes_def RRLoopThree.nodes_def, simp add: rmapF_def ref_map_def nodes_def RRLoopThree.nodes_def)
  show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (l'::location) (d::char list) (a'::char list)
       (as::actor set) (L::location set) I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l' \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       LedgerRRLoopFour.enables I l (Actor a) get \<Longrightarrow>
       ledgra G d = Some ((Actor a', as), L) \<Longrightarrow>
       Actor a \<in> as \<or> a = a' \<Longrightarrow>
       l' \<in> L \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G) (LedgerRRLoopFour.cgra G)
          (LedgerRRLoopFour.lgra G) (ledgra G(d \<mapsto> ((Actor a', as), L \<union> {l}))))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       ((Actor a',as), d) \<in> RRLoopThree.lgra (RRLoopThree.graphI (rmapF s)) l'\<close> 
    by (simp add: rmapF_def ref_map_def ledger_to_loc_def)
next show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (l'::location) (d::char list) (a'::char list)
       (as::actor set) (L::location set) I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l' \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       LedgerRRLoopFour.enables I l (Actor a) get \<Longrightarrow>
       ledgra G d = Some ((Actor a', as), L) \<Longrightarrow>
       Actor a \<in> as \<or> a = a' \<Longrightarrow>
       l' \<in> L \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G) (LedgerRRLoopFour.cgra G)
          (LedgerRRLoopFour.lgra G) (ledgra G(d \<mapsto> ((Actor a', as), L \<union> {l}))))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       Actor a \<in> as \<or> a = a'\<close> .
next show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (l'::location) (d::char list) (a'::char list)
       (as::actor set) (L::location set) I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l' \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       LedgerRRLoopFour.enables I l (Actor a) get \<Longrightarrow>
       ledgra G d = Some ((Actor a', as), L) \<Longrightarrow>
       Actor a \<in> as \<or> a = a' \<Longrightarrow>
       l' \<in> L \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G) (LedgerRRLoopFour.cgra G)
          (LedgerRRLoopFour.lgra G) (ledgra G(d \<mapsto> ((Actor a', as), L \<union> {l}))))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       rmapF s' =
       RRLoopThree.infrastructure.Infrastructure
        (RRLoopThree.igraph.Lgraph (RRLoopThree.gra (RRLoopThree.graphI (rmapF s)))
          (RRLoopThree.agra (RRLoopThree.graphI (rmapF s))) (RRLoopThree.cgra (RRLoopThree.graphI (rmapF s)))
          ((RRLoopThree.lgra (RRLoopThree.graphI (rmapF s)))
           (l := RRLoopThree.lgra (RRLoopThree.graphI (rmapF s)) l \<union> {((Actor a', as), d)})))
        (RRLoopThree.delta (rmapF s))\<close>
     apply (simp add: rmapF_def ref_map_def ledger_to_loc_def)
      apply (unfold ledger_to_loc_def)
      apply (rule ext, simp)
      apply (case_tac \<open>la = l\<close>, simp)
         apply (rule equalityI)
          prefer 2
          apply fastforce
    apply fastforce
     by auto[1]
 next show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (l'::location) (d::char list) (a'::char list)
       (as::actor set) (L::location set) I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l' \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       LedgerRRLoopFour.enables I l (Actor a) get \<Longrightarrow>
       ledgra G d = Some ((Actor a', as), L) \<Longrightarrow>
       Actor a \<in> as \<or> a = a' \<Longrightarrow>
       l' \<in> L \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G) (LedgerRRLoopFour.cgra G)
          (LedgerRRLoopFour.lgra G) (ledgra G(d \<mapsto> ((Actor a', as), L \<union> {l}))))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       RRLoopThree.enables (rmapF s) l (Actor a) get\<close>
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
  apply (simp add: hc_scenarioF_def local_policiesF_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
         apply (simp add: has_def RRLoopThree.has_def atI_def 
                RRLoopThree.credentials_def LedgerRRLoopFour.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioF_def local_policiesF_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
         apply (simp add: has_def RRLoopThree.has_def atI_def 
                RRLoopThree.credentials_def LedgerRRLoopFour.credentials_def)
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
                RRLoopThree.credentials_def LedgerRRLoopFour.credentials_def)
         apply (rule impI)+
        apply (rule conjI)
        apply (rule impI)+
        apply (drule sym)
  apply (drule sym)
        apply (simp add: hc_scenarioF_def local_policiesF_def)
        apply (simp add: hc_scenarioF_def local_policiesF_def ex_graphF_def LedgerRRLoopFour.nodes_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
  apply (subgoal_tac "LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI I) = {Location 0, Location 1, Location 2, Location 3}")
  apply simp
  apply (drule sym)
  apply (simp add: hc_scenarioF_def local_policiesF_def ex_graphF_def LedgerRRLoopFour.nodes_def)
  apply (simp add: hospitalR_def sphoneR_def
                  homeR_def cloudR_def cloudF_def homeF_def sphoneF_def hospitalF_def hc_scenarioF_def)
    by blast 
qed
(* process case: here we need to unify several steps on all l at abstract level to achieve the global conistency
   of data processing in the blockchain at the refined level. *)
next show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (L::location set) (d::char list) (a'::char list)
       (as::actor set) (I'::LedgerRRLoopFour.infrastructure) f::char list \<Rightarrow> char list.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       LedgerRRLoopFour.enables I l (Actor a) eval \<Longrightarrow>
       l \<in> L \<Longrightarrow>
       ledgra G d = Some ((Actor a', as), L) \<Longrightarrow>
       Actor a \<in> as \<or> a = a' \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G) (LedgerRRLoopFour.cgra G)
          (LedgerRRLoopFour.lgra G) ((ledgra G)(d := None)(f d \<mapsto> ((Actor a', as), L))))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF s, rmapF s') \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
    by (simp add: LedgerRRLoopFour.state_transition_in.process refmapThree_lemO rtrancl_imp_step)
(* delete *)
(* In this case it is similar -- albeit simpler -- as in the process case: the ledger immediately
   permits to delete all occurrences in the refined model while in the abstract model one del_data
   action only deletes the data in one location. So we need to do several del_data steps in the abstract
   model to achieve the same effect. Luckily because the way refinement is defined, this is a permissable
   refinement as well. *)
next show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (L::location set) (d::char list) (as::actor set)
       I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a \<in> LedgerRRLoopFour.actors_graph G \<Longrightarrow>
       l \<in> LedgerRRLoopFour.nodes G \<Longrightarrow>
       l \<in> L \<Longrightarrow>
       ledgra G d = Some ((Actor a, as), L) \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G) (LedgerRRLoopFour.cgra G)
          (LedgerRRLoopFour.lgra G) ((ledgra G)(d := None)))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF s, rmapF s') \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
    by (simp add: refmapThree_lem_del_dataO)
(* put case *)
next show \<open>\<And>(s::LedgerRRLoopFour.infrastructure) (s'::LedgerRRLoopFour.infrastructure) (G::LedgerRRLoopFour.igraph)
       (I::LedgerRRLoopFour.infrastructure) (a::char list) (l::location) (d::char list) (as::actor set) (L::location set)
       I'::LedgerRRLoopFour.infrastructure.
       (hc_scenarioF, s) \<in> {(x::LedgerRRLoopFour.infrastructure, y::LedgerRRLoopFour.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI hc_scenarioF) =
       LedgerRRLoopFour.nodes (LedgerRRLoopFour.graphI s) \<Longrightarrow>
       LedgerRRLoopFour.delta hc_scenarioF = LedgerRRLoopFour.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = LedgerRRLoopFour.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       LedgerRRLoopFour.enables I l (Actor a) put \<Longrightarrow>
       ledgra G d = Some ((Actor a, as), L) \<Longrightarrow>
       I' =
       LedgerRRLoopFour.infrastructure.Infrastructure
        (LedgerRRLoopFour.igraph.Lgraph (LedgerRRLoopFour.gra G) (LedgerRRLoopFour.agra G) (LedgerRRLoopFour.cgra G)
          (LedgerRRLoopFour.lgra G) (ledgra G(d \<mapsto> ((Actor a, as), insert l L))))
        (LedgerRRLoopFour.delta I) \<Longrightarrow>
       (rmapF s, rmapF s') \<in> {(x::RRLoopThree.infrastructure, y::RRLoopThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*\<close>
    by (meson LedgerRRLoopFour.state_transition_in.put refmapThree_lemO rtrancl_imp_step)
  qed





(* Now with the ledger, data privacy is a global property*)
lemma ledger_guarantees_privacy: 
\<open>hc_KripkeF \<turnstile> AG {x. \<forall> d :: data. \<forall> d' :: data. d = d' \<longrightarrow> ledgra (graphI x) d = ledgra (graphI x) d'}\<close>
  apply (simp add: check_def)
  apply (rule subsetI)
  by (simp add: AG_all_sO hc_KripkeF_def hc_statesF_def state_transition_refl_def)


end
(* This result can also be generalized easily from the locale to the global level*)
lemma ledger_guarantees_privacy_gen:  
\<open>Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I \<turnstile> AG {x. \<forall> d :: data. \<forall> d' :: data. d = d' \<longrightarrow> ledgra (graphI x) d = ledgra (graphI x) d'}\<close>
  apply (simp add: check_def)
  apply (rule subsetI)
  using AG_all_sO AG_in_lem UNIV_I by blast


end