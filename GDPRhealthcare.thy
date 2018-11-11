theory GDPRhealthcare
imports Infrastructure
begin

locale scenarioGDPR = 
fixes gdpr_actors :: "identity set"
defines gdpr_actors_def: "gdpr_actors \<equiv> {''Patient'', ''Doctor''}"

fixes gdpr_locations :: "location set"
defines gdpr_locations_def: "gdpr_locations \<equiv> 
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
defines global_policy_def: "global_policy I a \<equiv> a \<noteq> ''Doctor'' 
                 \<longrightarrow> \<not>(enables I hospital (Actor a) eval)"

fixes global_policy' :: "[infrastructure, identity] \<Rightarrow> bool"
defines global_policy'_def: "global_policy' I a \<equiv> a \<notin> gdpr_actors 
                 \<longrightarrow> \<not>(enables I cloud (Actor a) get)"  
  
fixes ex_creds :: "actor \<Rightarrow> (string set * string set)"
defines ex_creds_def: "ex_creds \<equiv> (\<lambda> x. if x = Actor ''Patient'' then 
                         ({''PIN'',''skey''}, {}) else 
                            (if x = Actor ''Doctor'' then
                                ({''PIN''},{}) else ({},{})))"


fixes ex_locs :: "location \<Rightarrow> string * acond"
defines "ex_locs \<equiv> (\<lambda> x.  if x = cloud then
             (''free'',{((Actor ''Patient'',{Actor ''Doctor''}),42)}) 
             else ('''',{}))"


fixes ex_loc_ass :: "location \<Rightarrow> identity set"
defines ex_loc_ass_def: "ex_loc_ass \<equiv>
          (\<lambda> x.  if x = home then {''Patient''}  
                 else (if x = hospital then {''Doctor'', ''Eve''} 
                       else {}))"

(* The nicer representation with case suffers from
   not so nice presentation in the cases (need to unfold the syntax) *) 
fixes ex_loc_ass_alt :: "location \<Rightarrow> identity set"
defines ex_loc_ass_alt_def: "ex_loc_ass_alt \<equiv>
          (\<lambda> x.  (case x of 
             Location (Suc 0) \<Rightarrow> {''Patient''}  
           | Location (Suc (Suc 0)) \<Rightarrow> {''Doctor'', ''Eve''} 
           |  _ \<Rightarrow> {}))"
  

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

(* Same as above: the nicer representation with case suffers from
   not so nice presentation in the cases (need to unfold the syntax) *) 
fixes local_policies_alt :: "[igraph, location] \<Rightarrow> policy set"
defines local_policies_alt_def: "local_policies_alt G \<equiv> 
    (\<lambda> x. case x of 
         Location (Suc 0) \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
       | Location 0 \<Rightarrow> {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
       | Location (Suc (Suc (Suc 0))) \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
       | Location (Suc (Suc 0)) \<Rightarrow>
                {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospital) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} 
       | _ \<Rightarrow>  {})"


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
(* problems with case in locales?
defines local_policies_def: "local_policies G x \<equiv> 
     (case x of 
       home \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
     | sphone \<Rightarrow> {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
     | cloud \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
     | hospital \<Rightarrow> {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospital) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} 
     | _ \<Rightarrow>  {})"
*)
  
fixes gdpr_scenario :: "infrastructure"
defines gdpr_scenario_def:
"gdpr_scenario \<equiv> Infrastructure ex_graph local_policies"

fixes Igdpr :: "infrastructure set"
defines Igdpr_def:
  "Igdpr \<equiv> {gdpr_scenario}"

(* other states of scenario *)

(* First step: Patient goes onto cloud *)
fixes gdpr_scenario' :: "infrastructure"
defines gdpr_scenario'_def:
"gdpr_scenario' \<equiv> Infrastructure ex_graph' local_policies"

fixes GDPR' :: "infrastructure set"
defines GDPR'_def:
  "GDPR' \<equiv> {gdpr_scenario'}"

(* Second step: Eve goes onto cloud from where she'll be able to get the data *)
fixes gdpr_scenario'' :: "infrastructure"
defines gdpr_scenario''_def:
"gdpr_scenario'' \<equiv> Infrastructure ex_graph'' local_policies"

fixes GDPR'' :: "infrastructure set"
defines GDPR''_def:
  "GDPR'' \<equiv> {gdpr_scenario''}"

fixes gdpr_states
defines gdpr_states_def: "gdpr_states \<equiv> { I. gdpr_scenario \<rightarrow>\<^sub>i* I }"

fixes gdpr_Kripke
defines "gdpr_Kripke \<equiv> Kripke gdpr_states {gdpr_scenario}"

fixes sgdpr 
defines "sgdpr \<equiv> {x. \<not> (global_policy' x ''Eve'')}"  
  
begin

lemma step1: "gdpr_scenario  \<rightarrow>\<^sub>n gdpr_scenario'"
proof (rule_tac l = home and a = "''Patient''" and l' = cloud in move)
  show "graphI gdpr_scenario = graphI gdpr_scenario" by (rule refl)
next show "''Patient'' @\<^bsub>graphI gdpr_scenario\<^esub> home" 
    by (simp add: gdpr_scenario_def ex_graph_def ex_loc_ass_def atI_def nodes_def)
next show "home \<in> nodes (graphI gdpr_scenario)"
    by (simp add: gdpr_scenario_def ex_graph_def ex_loc_ass_def atI_def nodes_def, blast)
next show "cloud \<in> nodes (graphI gdpr_scenario)"
    by (simp add: gdpr_scenario_def nodes_def ex_graph_def, blast)
next show "''Patient'' \<in> actors_graph (graphI gdpr_scenario)"
    by (simp add: actors_graph_def gdpr_scenario_def ex_graph_def ex_loc_ass_def nodes_def, blast)
next show "enables gdpr_scenario cloud (Actor ''Patient'') move"
    by (simp add: enables_def gdpr_scenario_def ex_graph_def local_policies_def
                    ex_creds_def ex_locs_def has_def credentials_def)
next show "gdpr_scenario' =
    Infrastructure (move_graph_a ''Patient'' home cloud (graphI gdpr_scenario)) (delta gdpr_scenario)"
    apply (simp add: gdpr_scenario'_def ex_graph'_def move_graph_a_def 
                   gdpr_scenario_def ex_graph_def home_def cloud_def hospital_def
                    ex_loc_ass_def ex_creds_def)
    apply (rule ext)
    by (simp add: hospital_def)
qed

lemma step1r: "gdpr_scenario  \<rightarrow>\<^sub>n* gdpr_scenario'"
proof (simp add: state_transition_in_refl_def)
  show " (gdpr_scenario, gdpr_scenario') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  by (insert step1, auto)
qed

lemma step2: "gdpr_scenario'  \<rightarrow>\<^sub>n gdpr_scenario''"
proof (rule_tac l = hospital and a = "''Eve''" and l' = cloud in move, rule refl)
  show "''Eve'' @\<^bsub>graphI gdpr_scenario'\<^esub> hospital"
   by (simp add: gdpr_scenario'_def ex_graph'_def hospital_def cloud_def atI_def nodes_def)
next show "hospital \<in> nodes (graphI gdpr_scenario')"
    by (simp add: gdpr_scenario'_def ex_graph'_def hospital_def cloud_def atI_def nodes_def, blast)
next show "cloud \<in> nodes (graphI gdpr_scenario')"
    by (simp add: gdpr_scenario'_def nodes_def ex_graph'_def, blast)
next show "''Eve'' \<in> actors_graph (graphI gdpr_scenario')"
    by (simp add: actors_graph_def gdpr_scenario'_def ex_graph'_def nodes_def
                     hospital_def cloud_def, blast)
next show "enables gdpr_scenario' cloud (Actor ''Eve'') move"
    by (simp add: enables_def gdpr_scenario'_def ex_graph_def local_policies_def
                  ex_creds_def ex_locs_def has_def credentials_def cloud_def sphone_def)
next show "gdpr_scenario'' =
    Infrastructure (move_graph_a ''Eve'' hospital cloud (graphI gdpr_scenario')) (delta gdpr_scenario')"
    apply (simp add: gdpr_scenario'_def ex_graph''_def move_graph_a_def gdpr_scenario''_def 
                     ex_graph'_def home_def cloud_def hospital_def ex_creds_def)
    apply (rule ext)
    apply (simp add: hospital_def)
    by blast
qed

lemma step2r: "gdpr_scenario'  \<rightarrow>\<^sub>n* gdpr_scenario''"
proof (simp add: state_transition_in_refl_def)
  show "(gdpr_scenario', gdpr_scenario'') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step2, auto)
qed
     
(* Attack example: Eve can get onto cloud and get Patient's data 
   because the policy allows Eve to get on cloud.
   This attack can easily be fixed by disabling Eve to "get"
   in the policy (just change the "True" for cloud to a set with no 
   Eve in it).
   However, it would not prevent Insider attacks (where Eve is 
   impersonating the Doctor, for example). Insider attacks can
   be checked using the UasI predicate.
*)
lemma gdpr_ref: "[\<N>\<^bsub>(Igdpr,sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr,sgdpr)\<^esup> \<sqsubseteq>
                  [\<N>\<^bsub>(Igdpr,GDPR')\<^esub>, \<N>\<^bsub>(GDPR',sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr,sgdpr)\<^esup>"  
proof (rule_tac l = "[]" and l' = "[\<N>\<^bsub>(Igdpr,GDPR')\<^esub>, \<N>\<^bsub>(GDPR',sgdpr)\<^esub>]" and
                  l'' = "[]" and si = Igdpr and si' = Igdpr and 
                  si'' = sgdpr and si''' = sgdpr in refI, simp, rule refl)
  show "([\<N>\<^bsub>(Igdpr, GDPR')\<^esub>, \<N>\<^bsub>(GDPR', sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr, sgdpr)\<^esup>) =
    ([] @ [\<N>\<^bsub>(Igdpr, GDPR')\<^esub>, \<N>\<^bsub>(GDPR', sgdpr)\<^esub>] @ [] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr, sgdpr)\<^esup>)"
  by simp
qed

lemma att_gdpr: "\<turnstile>[\<N>\<^bsub>(Igdpr,GDPR')\<^esub>, \<N>\<^bsub>(GDPR',sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr,sgdpr)\<^esup>"
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(Igdpr, GDPR')\<^esub>"
   apply (simp add: Igdpr_def GDPR'_def att_base)
   apply (subst state_transition_infra_def)
   by (rule step1)
next show "\<turnstile>[\<N>\<^bsub>(GDPR', sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(GDPR', sgdpr)\<^esup>"
   apply (subst att_and, simp)
   apply (simp add: GDPR'_def sgdpr_def att_base)
   apply (subst state_transition_infra_def)
   apply (rule_tac x = gdpr_scenario'' in exI)
   apply (rule conjI)
   apply (simp add: global_policy'_def gdpr_scenario''_def gdpr_actors_def 
                    enables_def local_policies_def cloud_def sphone_def)
    by (rule step2)
qed

lemma gdpr_abs_att: "\<turnstile>\<^sub>V [\<N>\<^bsub>(Igdpr,sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr,sgdpr)\<^esup>"
proof (rule ref_valI, rule gdpr_ref, rule att_gdpr)
qed

lemma gdpr_att: "gdpr_Kripke \<turnstile> EF {x. \<not>(global_policy' x ''Eve'')}"
proof -
  have a: " \<turnstile>[\<N>\<^bsub>(Igdpr, GDPR')\<^esub>, \<N>\<^bsub>(GDPR', sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr, sgdpr)\<^esup>"
    by (rule att_gdpr)
  hence "(Igdpr,sgdpr) = attack ([\<N>\<^bsub>(Igdpr, GDPR')\<^esub>, \<N>\<^bsub>(GDPR', sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr, sgdpr)\<^esup>)"
    by simp
  hence "Kripke {s::infrastructure. \<exists>i::infrastructure\<in>Igdpr. i \<rightarrow>\<^sub>i* s} Igdpr \<turnstile> EF sgdpr"
    apply (insert a)
    apply (erule AT_EF)
    by simp
  thus  "gdpr_Kripke \<turnstile> EF {x::infrastructure. \<not> global_policy' x ''Eve''}"
    by (simp add: gdpr_Kripke_def gdpr_states_def Igdpr_def sgdpr_def)
qed

theorem gdpr_EF: "gdpr_Kripke \<turnstile> EF sgdpr"  
proof (insert gdpr_att, simp add: sgdpr_def)
qed

(* The CTL statement can now be directly translated into Attack Trees *)  
theorem gdpr_AT: "\<exists> A. \<turnstile> A \<and> attack A = (Igdpr,sgdpr)"
proof -
  have a: "gdpr_Kripke \<turnstile> EF sgdpr " by (rule gdpr_EF)
  have b: "Igdpr \<noteq> {}" by (simp add: Igdpr_def)
  thus "\<exists>A::infrastructure attree. \<turnstile>A \<and> attack A = (Igdpr, sgdpr)" 
    apply (rule Completeness)
    apply (simp add: Igdpr_def)
    apply (insert a)
    by (simp add: gdpr_Kripke_def Igdpr_def gdpr_states_def)
qed

(* Conversely, if we had the attack given, we could immediately 
   infer EF s *)
theorem gdpr_EF': "gdpr_Kripke \<turnstile> EF sgdpr"
proof -
  have a: "\<exists>A::infrastructure attree. \<turnstile>A \<and> attack A = (Igdpr, sgdpr)" by (rule gdpr_AT)
  thus "gdpr_Kripke \<turnstile> EF sgdpr"
    apply (insert a)
    apply (erule exE)
    apply (erule conjE)
    apply (drule AT_EF)
    apply assumption
by (simp add: gdpr_Kripke_def gdpr_states_def Igdpr_def)
qed
(* However, when integrating DLM into the model and hence labeling 
   information becomes part of the conditions of the get_data rule this isn't
   possible any more: gdpr_EF is not true any more *)  
  
(** GDPR properties  for the illustration of the DLM labeling **)    

(* GDPR three: Processing preserves ownership in any location *)    
lemma gdpr_three: "h \<in> gdpr_actors \<Longrightarrow> l \<in> gdpr_locations \<Longrightarrow>
         owns (Igraph gdpr_scenario) l (Actor h) d \<Longrightarrow>
         gdpr_Kripke \<turnstile> AG {x. \<forall> l \<in> gdpr_locations. owns (Igraph x) l (Actor h) d }"  
proof (simp add: gdpr_Kripke_def check_def, rule conjI)
  show "gdpr_scenario \<in> gdpr_states" by (simp add: gdpr_states_def state_transition_refl_def)
next show "h \<in> gdpr_actors \<Longrightarrow>
    l \<in> gdpr_locations \<Longrightarrow>
    owns (Igraph gdpr_scenario) l (Actor h) d \<Longrightarrow>
    gdpr_scenario \<in> AG {x::infrastructure. \<forall>l::location\<in>gdpr_locations. owns (Igraph x) l (Actor h) d}"
      apply (unfold AG_def)
      apply (simp add: gfp_def)
      apply (rule_tac x = "{x::infrastructure. \<forall>l::location\<in>gdpr_locations. owns (Igraph x) l (Actor h) d}" in exI)
      apply (rule conjI)
      apply (rule subset_refl)
      apply (rule conjI)
      apply (unfold AX_def)
      apply (simp add: owns_def)
      by (simp add: gdpr_scenario_def owns_def)
  qed

(* Application example of Correctness and Completeness: 
   show that there is no attack to ownership possible *)  
theorem no_attack_gdpr_three: 
"h \<in> gdpr_actors \<Longrightarrow> l \<in> gdpr_locations \<Longrightarrow> 
 owns (Igraph gdpr_scenario) l (Actor h) d \<Longrightarrow>
attack A = (Igdpr, -{x. \<forall> l \<in> gdpr_locations. owns (Igraph x) l (Actor h) d })
\<Longrightarrow> \<not> (\<turnstile> A::infrastructure attree)"
proof (rule_tac I = Igdpr and 
           s = "-{x::infrastructure. \<forall>l::location\<in>gdpr_locations. owns (Igraph x) l (Actor h) d}" 
       in contrapos_corr)
  show "h \<in> gdpr_actors \<Longrightarrow>
    l \<in> gdpr_locations \<Longrightarrow>
    owns (Igraph gdpr_scenario) l (Actor h) d \<Longrightarrow>
    attack A = (Igdpr, - {x::infrastructure. \<forall>l::location\<in>gdpr_locations. owns (Igraph x) l (Actor h) d}) \<Longrightarrow>
    \<not> Kripke {s::infrastructure. \<exists>i::infrastructure\<in>Igdpr. i \<rightarrow>\<^sub>i* s}
        Igdpr \<turnstile> EF (- {x::infrastructure. \<forall>l::location\<in>gdpr_locations. owns (Igraph x) l (Actor h) d})"
      apply (rule AG_imp_notnotEF)
      apply (simp add: gdpr_Kripke_def Igdpr_def gdpr_states_def)
      apply (drule gdpr_three, assumption, assumption)
    by (simp add: gdpr_Kripke_def Igdpr_def gdpr_states_def)
qed
  
end