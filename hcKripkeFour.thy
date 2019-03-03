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
          (\<lambda> (l, d). if (d = 42 \<and> l = (''Patient'',{''Doctor''})) then {homeF} else {}))"


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


begin

theorem refmapThree: "hc_KripkeR  \<sqsubseteq>\<^sub>rmapF hc_KripkeF" 
  apply (rule strong_mt)
  sorry

(* show attack "Eve can still do put at cloud and since we haven't
   forbidden it, she can overwrite Bob's entry "  *)
theorem hc_EFF: "hc_KripkeF \<turnstile> EF shcF"  
  sorry

end

end
 