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

theorem refmapOne: "hc_Kripke  \<sqsubseteq>\<^sub>rmapT hc_KripkeT" 
  apply (rule strong_mt)
  sorry

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
