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
          (\<lambda> (l, d). if (d = ''42'' \<and> l = (''Patient'',{''Doctor''})) then {homeV} else {}))"


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

theorem refmapFour: "hc_KripkeF  \<sqsubseteq>\<^sub>rmapV hc_KripkeV" 
  apply (rule strong_mt')

  sorry

(* show attack "Eve can still do put at cloud and since we haven't
   forbidden it, she can overwrite Bob's entry "  *)
theorem hc_EFV: "hc_KripkeV \<turnstile> EF shcV"  
  sorry

(* See hcKripkeFour
theorem Ledger_con: "h \<in> hc_actorsV \<Longrightarrow> h' \<in> hc_actorsV \<Longrightarrow> l \<in> hc_locationsV \<Longrightarrow>
    l' \<in> hc_locationsV \<Longrightarrow> 
    l \<in> (ledgra G \<nabla> ((h, hs),n)) \<Longrightarrow> l' \<in> (ledgra G \<nabla> ((h', hs'),n)) \<Longrightarrow> 
    (h, hs) = (h', hs')"
  sorry
*)

end

end
 