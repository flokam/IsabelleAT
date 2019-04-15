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
             {''42''}  
             else ({}))"


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

lemma step1: "hc_scenario \<rightarrow>\<^sub>n hc_scenario'"
proof (rule_tac l = home and a = "''Patient''" and l' = cloud in move)
  show "graphI hc_scenario = graphI hc_scenario" by (rule refl)
next show "''Patient'' @\<^bsub>graphI hc_scenario\<^esub> home" 
    by (simp add: hc_scenario_def ex_graph_def ex_loc_ass_def atI_def nodes_def)
next show "home \<in> nodes (graphI hc_scenario)"
    by (simp add: hc_scenario_def ex_graph_def ex_loc_ass_def atI_def nodes_def, blast)
next show "cloud \<in> nodes (graphI hc_scenario)"
    by (simp add: hc_scenario_def nodes_def ex_graph_def, blast)
next show "''Patient'' \<in> actors_graph (graphI hc_scenario)"
    by (simp add: actors_graph_def hc_scenario_def ex_graph_def ex_loc_ass_def nodes_def, blast)
next show "enables hc_scenario cloud (Actor ''Patient'') move"
    by (simp add: enables_def hc_scenario_def ex_graph_def local_policies_def
                    ex_creds_def ex_locs_def has_def credentials_def)
next show "hc_scenario' =
    Infrastructure (move_graph_a ''Patient'' home cloud (graphI hc_scenario)) (delta hc_scenario)"
    apply (simp add: hc_scenario'_def ex_graph'_def move_graph_a_def 
                   hc_scenario_def ex_graph_def home_def cloud_def hospital_def
                    ex_loc_ass_def ex_creds_def)
    apply (rule ext)
    by (simp add: hospital_def)
qed

lemma step1r: "hc_scenario  \<rightarrow>\<^sub>n* hc_scenario'"
proof (simp add: state_transition_in_refl_def)
  show " (hc_scenario, hc_scenario') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  by (insert step1, auto)
qed

lemma step2: "hc_scenario'  \<rightarrow>\<^sub>n hc_scenario''"
proof (rule_tac l = hospital and a = "''Eve''" and l' = cloud in move, rule refl)
  show "''Eve'' @\<^bsub>graphI hc_scenario'\<^esub> hospital"
   by (simp add: hc_scenario'_def ex_graph'_def hospital_def cloud_def atI_def nodes_def)
next show "hospital \<in> nodes (graphI hc_scenario')"
    by (simp add: hc_scenario'_def ex_graph'_def hospital_def cloud_def atI_def nodes_def, blast)
next show "cloud \<in> nodes (graphI hc_scenario')"
    by (simp add: hc_scenario'_def nodes_def ex_graph'_def, blast)
next show "''Eve'' \<in> actors_graph (graphI hc_scenario')"
    by (simp add: actors_graph_def hc_scenario'_def ex_graph'_def nodes_def
                     hospital_def cloud_def, blast)
next show "enables hc_scenario' cloud (Actor ''Eve'') move"
    by (simp add: enables_def hc_scenario'_def ex_graph_def local_policies_def
                  ex_creds_def ex_locs_def has_def credentials_def cloud_def sphone_def)
next show "hc_scenario'' =
    Infrastructure (move_graph_a ''Eve'' hospital cloud (graphI hc_scenario')) (delta hc_scenario')"
    apply (simp add: hc_scenario'_def ex_graph''_def move_graph_a_def hc_scenario''_def 
                     ex_graph'_def home_def cloud_def hospital_def ex_creds_def)
    apply (rule ext)
    apply (simp add: hospital_def)
    by blast
qed

lemma step2r: "hc_scenario'  \<rightarrow>\<^sub>n* hc_scenario''"
proof (simp add: state_transition_in_refl_def)
  show "(hc_scenario', hc_scenario'') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step2, auto)
qed

(* First attack: Eve can get onto cloud and get Patient's data 
   because the policy allows Eve to get on cloud. *)
(* Note the first bunch of lemmas develops the attack refinement *)
lemma hc_ref: "[\<N>\<^bsub>(Ihc,shc)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Ihc,shc)\<^esup> \<sqsubseteq>
                  [\<N>\<^bsub>(Ihc,HC')\<^esub>, \<N>\<^bsub>(HC',shc)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Ihc,shc)\<^esup>"  
proof (rule_tac l = "[]" and l' = "[\<N>\<^bsub>(Ihc,HC')\<^esub>, \<N>\<^bsub>(HC',shc)\<^esub>]" and
                  l'' = "[]" and si = Ihc and si' = Ihc and 
                  si'' = shc and si''' = shc in refI, simp, rule refl)
  show "([\<N>\<^bsub>(Ihc, HC')\<^esub>, \<N>\<^bsub>(HC', shc)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Ihc, shc)\<^esup>) =
    ([] @ [\<N>\<^bsub>(Ihc, HC')\<^esub>, \<N>\<^bsub>(HC', shc)\<^esub>] @ [] \<oplus>\<^sub>\<and>\<^bsup>(Ihc, shc)\<^esup>)"
  by simp
qed

lemma att_hc: "\<turnstile>[\<N>\<^bsub>(Ihc,HC')\<^esub>, \<N>\<^bsub>(HC',shc)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Ihc,shc)\<^esup>"
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(Ihc, HC')\<^esub>"
   apply (simp add: Ihc_def HC'_def att_base)
   apply (subst state_transition_infra_def)
   by (rule step1)
next show "\<turnstile>[\<N>\<^bsub>(HC', shc)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(HC', shc)\<^esup>"
   apply (subst att_and, simp)
   apply (simp add: HC'_def shc_def att_base)
   apply (subst state_transition_infra_def)
   apply (rule_tac x = hc_scenario'' in exI)
   apply (rule conjI)
   apply (simp add: global_policy_def hc_scenario''_def hc_actors_def 
                    enables_def local_policies_def cloud_def sphone_def)
    by (rule step2)
qed

lemma hc_abs_att: "\<turnstile>\<^sub>V [\<N>\<^bsub>(Ihc,shc)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Ihc,shc)\<^esup>"
proof (rule ref_valI, rule hc_ref, rule att_hc)
qed

lemma hc_att: "hc_Kripke \<turnstile> EF {x. \<not>(global_policy x ''Eve'')}"
proof -
  have a: " \<turnstile>[\<N>\<^bsub>(Ihc, HC')\<^esub>, \<N>\<^bsub>(HC', shc)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Ihc, shc)\<^esup>"
    by (rule att_hc)
  hence "(Ihc,shc) = attack ([\<N>\<^bsub>(Ihc, HC')\<^esub>, \<N>\<^bsub>(HC', shc)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Ihc, shc)\<^esup>)"
    by simp
  hence "Kripke {s::infrastructure. \<exists>i::infrastructure\<in>Ihc. i \<rightarrow>\<^sub>i* s} Ihc \<turnstile> EF shc"
    apply (insert a)
    apply (erule AT_EF)
    by simp
  thus  "hc_Kripke \<turnstile> EF {x::infrastructure. \<not> global_policy x ''Eve''}"
    by (simp add: hc_Kripke_def hc_states_def Ihc_def shc_def)
qed

theorem hc_EF: "hc_Kripke \<turnstile> EF shc"  
proof (insert hc_att, simp add: shc_def)
qed


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