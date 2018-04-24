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

fixes ex_creds' :: "actor \<Rightarrow> (string set * string set)"
defines ex_creds'_def: "ex_creds' \<equiv> (\<lambda> x. if x = Actor ''Patient'' then 
                         ({''PIN'',''skey''}, {}) else 
                            (if x = Actor ''Doctor'' then
                                ({''PIN'',''skey''}, {}) else ({},{})))"

fixes ex_locs :: "location \<Rightarrow> string * acond"
defines "ex_locs \<equiv> (\<lambda> x.  if x = cloud then
             (''free'',{((Actor ''Patient'',{Actor ''Doctor''}),42)}) 
             else ('''',{}))"

  
fixes ex_graph :: "igraph"
defines ex_graph_def: "ex_graph \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
     (\<lambda> x. if x = home then {''Patient''} else 
           (if x = hospital then {''Doctor''} else {})) 
     ex_creds ex_locs"
  
fixes ex_graph' :: "igraph"
defines ex_graph'_def: "ex_graph' \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
       (\<lambda> x. if x = cloud then {''Patient''} else 
           (if x = hospital then {''Doctor''} else {})) 
     ex_creds' ex_locs"
  
fixes ex_graph'' :: "igraph"
defines ex_graph''_def: "ex_graph'' \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
       (\<lambda> x. if x = cloud then {''Patient'', ''Eve''} else 
           (if x = hospital then {''Doctor''} else {})) 
     ex_creds' ex_locs"


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


(* Second step: Eve goes onto cloud from where she'' be able to get the data *)
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
defines "sgdpr \<equiv> {x. \<not> (global_policy x ''Eve'')}"  
  
begin

(* Attack example: Eve can get onto cloud and get Patient's data 
 for the naive version of get_data (with no use of DLM) 
Attention: the following lemmas up to and including GDPR_AT
only work when the premises 
"((Actor a', as), n) \<in> snd (lgra G l') \<Longrightarrow> Actor a \<in> as \<Longrightarrow>"
in rule get_data in Infrastructure.thy are omitted
(thus switching of the DLM-IFC  
*)
lemma gdpr_att: "gdpr_Kripke \<turnstile> EF {x. \<not>(global_policy' x ''Eve'')}"
sorry  
 

theorem gdpr_EF: "gdpr_Kripke \<turnstile> EF sgdpr"  
  sorry
(* The CTL statement can now be directly translated into Attack Trees *)  
  
theorem gdpr_AT: "\<exists> A. \<turnstile> A \<and> attack A = (Igdpr,sgdpr)"
  apply (insert gdpr_EF)
  thm Completeness
    apply (subgoal_tac "Igdpr \<noteq> {}")
   apply (drule Completeness)
     apply (simp add: Igdpr_def)
    apply (simp add: gdpr_Kripke_def Igdpr_def gdpr_states_def)
   apply simp
by (simp add: Igdpr_def)

(* Conversely, if we had the attack given, we could immediately 
   infer EF s *)
theorem gdpr_EF': "gdpr_Kripke \<turnstile> EF sgdpr"
  apply (insert gdpr_AT)
  apply (erule exE)
    apply (erule conjE)
    apply (drule AT_EF)
  apply (erule sym)
by (simp add: gdpr_Kripke_def gdpr_states_def Igdpr_def)

    
(* However, when integrating DLM info into the get_data rule this isn't
   possible any more: gdpr_EF is not true any more *)  
  
  
  
(* Other examples illustrating the GDPR rules *)  
(* Positive example: Only the Doctor can use data processing in hospital *)  
lemma gdpr_zero: "gdpr_Kripke \<turnstile> AG {x. (global_policy x ''Doctor'')}"
  oops

(** GDPR properties  **)    
(* GDPR one: Owner and listed readers can access*)
lemma gdpr_one: "h \<in> gdpr_actors \<Longrightarrow> l \<in> gdpr_locations \<Longrightarrow>
                 Actor h \<in> {owner d} \<union> readers d \<Longrightarrow>
                 gdpr_Kripke \<turnstile> AG {x. has_access (graphI x) l (Actor h) d}"
oops
(* All actors in the infrastructure can delete their data at all times 
   and at all locations -- this could be moved to the Infrastructure
   since it holds for all applications *)    
lemma gdpr_two: "h \<in> gdpr_actors \<Longrightarrow> l \<in> gdpr_locations \<Longrightarrow>
                 gdpr_Kripke \<turnstile> AG (EX' {x. actor_can_delete x (Actor h) l})"    
  sorry

theorem GDPR_two: "\<forall> h \<in> gdpr_actors. \<forall> l \<in> gdpr_locations.
                 gdpr_Kripke \<turnstile> AG (EX' {x. actor_can_delete x (Actor h) l})"    
  by (simp add: gdpr_two)
    
    
(* GDPR three: Processing preserves ownership in any location *)    
lemma gdpr_three: "h \<in> gdpr_actors \<Longrightarrow> l \<in> gdpr_locations \<Longrightarrow>
         owns (Igraph gdpr_scenario) l (Actor h) d \<Longrightarrow>
         gdpr_Kripke \<turnstile> AG {x. \<forall> l \<in> gdpr_locations. owns (Igraph x) l (Actor h) d }"  
sorry
  

end