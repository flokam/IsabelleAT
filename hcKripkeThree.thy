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
defines global_policyR_def: "global_policyR I a \<equiv> a \<notin> hc_actors 
                 \<longrightarrow> \<not>(enables I cloud (Actor a) put)"  

fixes ex_credsR :: "actor \<Rightarrow> (string set * string set)"
defines ex_credsR_def: "ex_credsR \<equiv> (\<lambda> x. if x = Actor ''Patient'' then 
                         ({''PIN'',''skey''}, {}) else 
                            (if x = Actor ''Doctor'' then
                                ({''PIN''},{}) else ({},{})))"

fixes ex_locsR :: "location \<Rightarrow> string * acond"
defines "ex_locsR \<equiv>  (\<lambda> x.  if x = cloudT then
             (''free'',{((Actor ''Patient'',{Actor ''Doctor''}),42)}) 
             else ('''',{}))"

fixes ex_locR_ass :: "location \<Rightarrow> identity set"
defines ex_locR_ass_def: "ex_locR_ass \<equiv>
          (\<lambda> x.  if x = homeT then {''Patient''}  
                 else (if x = hospitalT then {''Doctor'', ''Eve''} 
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


begin

theorem refmapTwo: "hc_KripkeT  \<sqsubseteq>\<^sub>rmapR hc_KripkeR" 
  apply (rule strong_mt)
  sorry

(* show attack "Eve can do put at cloud"  *)
theorem hc_EFR: "hc_KripkeR \<turnstile> EF shcR"  
  sorry

end
end
 