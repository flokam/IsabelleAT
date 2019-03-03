theory hcKripkeOne 
imports RRLoopOne
begin

locale scenarioHCKripkeOne =
fixes hc_actors :: "identity set"
defines hc_actors_def: "hc_actors \<equiv> {''Patient'', ''Doctor''}"
fixes hc_locations :: "location set"
defines hc_locations_def: "hc_locations \<equiv> 
          {Location 0, Location 1, Location 2, Location 3}"

fixes sphone :: "location"
defines sphone_def: "sphone \<equiv> Location 0"
fixes home :: "location"
defines home_def: "home \<equiv> Location 1"
fixes hospital :: "location"
defines hospital_def: "hospital \<equiv> Location 2"
fixes cloud :: "location"
defines cloud_def: "cloud \<equiv> Location 3"

fixes global_policy :: "[infrastructure, identity] \<Rightarrow> bool"
defines global_policy_def: "global_policy I a \<equiv> a \<notin> hc_actors 
                 \<longrightarrow> \<not>(enables I cloud (Actor a) get)"  

fixes ex_creds :: "actor \<Rightarrow> (string set * string set)"
defines ex_creds_def: "ex_creds \<equiv> (\<lambda> x. if x = Actor ''Patient'' then 
                         ({''PIN'',''skey''}, {}) else 
                            (if x = Actor ''Doctor'' then
                                ({''PIN''},{}) else ({},{})))"


fixes ex_locs :: "location \<Rightarrow> string set"
defines "ex_locs \<equiv> (\<lambda> x.  if x = cloud then
             {''free''}  
             else ({''''}))"


fixes ex_loc_ass :: "location \<Rightarrow> identity set"
defines ex_loc_ass_def: "ex_loc_ass \<equiv>
          (\<lambda> x.  if x = home then {''Patient''}  
                 else (if x = hospital then {''Doctor'', ''Eve''} 
                       else {}))"

fixes ex_graph :: "igraph"
defines ex_graph_def: "ex_graph \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
     ex_loc_ass
     ex_creds ex_locs"
  
fixes ex_graph' :: "igraph"
defines ex_graph'_def: "ex_graph' \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
       (\<lambda> x. if x = cloud then {''Patient''} else 
           (if x = hospital then {''Doctor'',''Eve''} else {})) 
     ex_creds ex_locs"
  
fixes ex_graph'' :: "igraph"
defines ex_graph''_def: "ex_graph'' \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
       (\<lambda> x. if x = cloud then {''Patient'', ''Eve''} else 
           (if x = hospital then {''Doctor''} else {})) 
     ex_creds ex_locs"

fixes local_policies :: "[igraph, location] \<Rightarrow> policy set"
defines local_policies_def: "local_policies G \<equiv> 
    (\<lambda> x. if x = home then
        {(\<lambda> y. True, {put,get,move,eval})}
          else (if x = sphone then 
             {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
                else (if x = cloud then
                {(\<lambda> y. True, {put,get,move,eval})}
                       else (if x = hospital then
                {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospital) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} else {}))))"

fixes hc_scenario :: "infrastructure"
defines hc_scenario_def:
"hc_scenario \<equiv> Infrastructure ex_graph local_policies"

fixes Ihc :: "infrastructure set"
defines Ihc_def:
  "Ihc \<equiv> {hc_scenario}"

fixes hc_scenario' :: "infrastructure"
defines hc_scenario'_def:
"hc_scenario' \<equiv> Infrastructure ex_graph' local_policies"

fixes HC' :: "infrastructure set"
defines HC'_def:
  "HC' \<equiv> {hc_scenario'}"

fixes hc_scenario'' :: "infrastructure"
defines hc_scenario''_def:
"hc_scenario'' \<equiv> Infrastructure ex_graph'' local_policies"

fixes HC'' :: "infrastructure set"
defines HC''_def:
  "HC'' \<equiv> {hc_scenario''}"

fixes hc_states
defines hc_states_def: "hc_states \<equiv> { I. hc_scenario \<rightarrow>\<^sub>i* I }"

fixes hc_Kripke
defines "hc_Kripke \<equiv> Kripke hc_states {hc_scenario}"

fixes shc 
defines "shc \<equiv> {x. \<not> (global_policy x ''Eve'')}"  

begin
theorem hc_EF: "hc_Kripke \<turnstile> EF shc"  
  sorry

(* The CTL statement can now be directly translated into Attack Trees using
   the meta-theory, i.e. Correctness and Completeness theorems. *)  
theorem hc_AT: "\<exists> A. \<turnstile> A \<and> attack A = (Ihc,shc)"
proof -
  have a: "hc_Kripke \<turnstile> EF shc " by (rule hc_EF)
  have b: "Ihc \<noteq> {}" by (simp add: Ihc_def)
  thus "\<exists>A::infrastructure attree. \<turnstile>A \<and> attack A = (Ihc, shc)" 
    apply (rule Completeness)
    apply (simp add: Ihc_def)
    apply (insert a)
    by (simp add: hc_Kripke_def Ihc_def hc_states_def)
qed

end
end