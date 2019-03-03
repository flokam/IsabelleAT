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
defines global_policyT_def: "global_policyT I a \<equiv> a \<notin> hc_actors 
                 \<longrightarrow> \<not>(enables I cloud (Actor a) eval)"  

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
theorem hc_EFT: "hc_KripkeT \<turnstile> EF shcT"  
  sorry

end
end
