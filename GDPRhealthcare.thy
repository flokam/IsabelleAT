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
defines "ex_locs \<equiv> (\<lambda> x.  (''free'',{((Actor ''Patient'',{Actor ''Doctor''}),42)}))"

  
fixes ex_graph :: "igraph"
defines ex_graph_def: "ex_graph \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
     (\<lambda> x. if x = home then {''Patient''} else 
           (if x = hospital then {''Doctor''} else {})) 
     ex_creds ex_locs"
  
fixes ex_graph' :: "igraph"
defines ex_graph'_def: "ex_graph' \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
       (\<lambda> x. if x = home then {''Patient''} else 
           (if x = hospital then {''Doctor''} else {})) 
     ex_creds' ex_locs"
  
fixes ex_graph'' :: "igraph"
defines ex_graph''_def: "ex_graph'' \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
       (\<lambda> x. if x = home then {''Patient''} else 
           (if x = hospital then {''Doctor''} else {})) 
     ex_creds' ex_locs"

fixes ex_graph''' :: "igraph"
 defines ex_graph'''_def: "ex_graph''' \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
       (\<lambda> x. if x = home then {''Patient''} else 
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

fixes gdpr_scenario :: "infrastructure"
defines gdpr_scenario_def:
"gdpr_scenario \<equiv> Infrastructure ex_graph local_policies"

fixes Igdpr :: "infrastructure set"
defines Igdpr_def:
  "Igdpr \<equiv> {gdpr_scenario}"

(* other states of scenario *)


(* First step: Carer is in room with Patient and takes the skey *)
fixes gdpr_scenario' :: "infrastructure"
defines gdpr_scenario'_def:
"gdpr_scenario' \<equiv> Infrastructure ex_graph' local_policies"

fixes GDPR' :: "infrastructure set"
defines GDPR'_def:
  "GDPR' \<equiv> {gdpr_scenario'}"


(* Second step: Carer goes onto sphone and takes the money by eval on bankapp *)
fixes gdpr_scenario'' :: "infrastructure"
defines gdpr_scenario''_def:
"gdpr_scenario'' \<equiv> Infrastructure ex_graph'' local_policies"

fixes GDPR'' :: "infrastructure set"
defines GDPR''_def:
  "GDPR'' \<equiv> {gdpr_scenario''}"


(* Third step: Carer goes onto bankapp and can then get money *)
fixes gdpr_scenario''' :: "infrastructure"
defines gdpr_scenario'''_def:
"gdpr_scenario''' \<equiv> Infrastructure ex_graph''' local_policies"

fixes GDPR''' :: "infrastructure set"
defines GDPR'''_def:
  "GDPR''' \<equiv> {gdpr_scenario'''}"


fixes gdpr_states
defines gdpr_states_def: "gdpr_states \<equiv> { I. gdpr_scenario \<rightarrow>\<^sub>i* I }"

fixes gdpr_Kripke
defines "gdpr_Kripke \<equiv> Kripke gdpr_states {gdpr_scenario}"

fixes sgdpr 
defines "sgdpr \<equiv> {x. \<not> (global_policy x ''Carer'')}"  
  
begin

(* Base example: Only the Doctor can use data processing in hospital *)  
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
  
    
lemma step1: "gdpr_scenario  \<rightarrow>\<^sub>n gdpr_scenario'"
  apply (rule_tac l = home and a' = "''Doctor''" and a = "''Patient''" and z = "''skey''" in get)
  apply (rule refl)
  apply (simp add: hc_scenario_def atI_def ex_graph_def)+
      apply (simp add: ex_graph_def hc_scenario_def ex_creds_def has_def credentials_def)
  apply (simp add: hc_scenario_def enables_def local_policies_def ex_creds_def)
  apply (simp add: hc_scenario'_def hc_scenario_def ex_creds'_def 
         ex_graph'_def ex_graph_def ex_creds_def)
    apply (rule conjI)
    apply (rule impI)
   apply (rule ext)
   apply simp
   apply (rule impI)
   apply (rule equalityI)
    apply simp+
    apply (rule impI)
    apply (rule ext)
   apply simp
   apply (rule impI)+
   apply (rule equalityI)
by simp+
   
lemma step1r: "hc_scenario \<rightarrow>\<^sub>n*  hc_scenario'"
apply (simp add: state_transition_in_refl_def)
  apply (insert step1)    
by auto

lemma step2: "hc_scenario' \<rightarrow>\<^sub>n hc_scenario''"
  apply (rule_tac l = room and a = "''Carer''" and l' = sphone in move)
  apply (rule refl)
       apply (simp add: hc_scenario'_def atI_def nodes_def ex_graph_def room_def sphone_def
               ex_graph'_def bankapp_def healthapp_def)+
     apply blast
    apply (simp add: hc_scenario'_def actors_graph_def ex_graph_def ex_graph'_def
                nodes_def sphone_def room_def healthapp_def bankapp_def)
   apply (simp add: hc_scenario'_def enables_def local_policies_def ex_graph'_def 
                    ex_creds'_def has_def credentials_def)
  apply (simp add: hc_scenario''_def hc_scenario'_def ex_creds'_def ex_creds_def
                   ex_graph'_def ex_graph''_def move_graph_a_def ex_graph_def sphone_def
                   room_def has_def credentials_def)
  apply (rule ext)
  apply (simp add: sphone_def)
by blast

lemma step2r: "hc_scenario'  \<rightarrow>\<^sub>n* hc_scenario''"
apply (simp add: state_transition_in_refl_def)
apply (insert step2)
by auto


lemma step3: "hc_scenario''  \<rightarrow>\<^sub>n hc_scenario'''"
  apply (rule_tac l = sphone and a = "''Carer''" and l' = bankapp in move)
  apply (rule refl)
       apply (simp add: hc_scenario''_def atI_def nodes_def ex_graph'_def room_def sphone_def
               ex_graph''_def bankapp_def healthapp_def)+
     apply blast
    apply (simp add: hc_scenario''_def actors_graph_def ex_graph'_def
                ex_graph''_def nodes_def sphone_def room_def healthapp_def bankapp_def)+
              apply blast
   apply (simp add: hc_scenario''_def enables_def local_policies_def ex_creds'_def
                  bankapp_def healthapp_def sphone_def room_def sphone_def 
                  atI_def ex_locs_def ex_graph'_def ex_graph''_def has_def 
                  credentials_def)
  apply (simp add: hc_scenario''_def hc_scenario'''_def ex_creds'_def ex_creds_def
                   ex_graph'_def move_graph_a_def ex_graph''_def sphone_def
                   room_def bankapp_def has_def credentials_def ex_graph'''_def
          )
        apply (rule ext)
by (simp add: sphone_def bankapp_def)
  
lemma step3r: "hc_scenario''  \<rightarrow>\<^sub>n* hc_scenario'''"
apply (simp add: state_transition_in_refl_def)
apply (insert step3)
by auto
  
  
lemma stepr: "hc_scenario   \<rightarrow>\<^sub>n* hc_scenario'''"
apply (insert step1r step2r step3r)
by (simp add: state_transition_in_refl_def)
  
    
(* The following attacks can be shown without using the 
   strong impersonation property of Insider *) 

lemma in_danger: "\<not> (global_policy hc_scenario''' ''Carer'')"
  apply (unfold global_policy_def)
    apply simp
  by (simp add: hc_scenario'''_def
                  ex_graph''_def ex_graph'''_def ex_locs_def ex_creds'_def
                  atI_def local_policies_def enables_def
                  bankapp_def healthapp_def sphone_def room_def has_def credentials_def)
                  
                
lemma att_hc: "\<turnstile>[\<N>\<^bsub>(Ihc,HC')\<^esub>, \<N>\<^bsub>(HC',HC'')\<^esub>, \<N>\<^bsub>(HC'',shc)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Ihc,shc)\<^esup>"
  apply (simp add: att_and)
    apply (rule conjI)
   apply (simp add: Ihc_def HC'_def att_base) 
    (* instantiation should give that for free 
    apply (rule step1) *)
  sorry
    

theorem hc_EF: "hc_Kripke \<turnstile> EF shc"
  apply (insert att_hc)
    apply (subgoal_tac "(Ihc, shc) = attack ([\<N>\<^bsub>(Ihc,HC')\<^esub>, \<N>\<^bsub>(HC',HC'')\<^esub>, \<N>\<^bsub>(HC'',shc)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Ihc,shc)\<^esup>)")
  apply (drule AT_EF)
    apply simp
   apply  (simp add: hc_Kripke_def hc_states_def Ihc_def)
  by simp
    
    
(* similar to IoT-MC. Not needed any more because of AT_EF theorem 
theorem hc_Kripke_policy_fail: 
  "hc_Kripke \<turnstile> AG ({x. global_policy x ''Carer''})"
(* fails *)
oops

(* similar to IoT-MC  *)
theorem hc_Kripke_attack:
  "hc_Kripke \<turnstile> EF ({x. \<not> global_policy x ''Carer''})"
sorry

theorem hc_find_attack:
  "hc_Kripke \<turnstile> EF ({x. enables x bankapp (Actor ''Carer'') eval})"
sorry                                      
*)

(* Now the attack tree lemmas *)
(*  Update this later
lemma ref_lem_b: "([\<N>\<^bsub>Goto bankapp\<^esub>, \<N>\<^bsub>Perform eval\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(''getmovemoveeval'')\<^esup> )
               \<sqsubseteq>\<^sub>hc_scenario ([\<N>\<^bsub>Perform get\<^esub>, \<N>\<^bsub>Goto sphone\<^esub>, \<N>\<^bsub>Goto bankapp\<^esub>, \<N>\<^bsub>Perform eval\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(''getmovemoveeval'')\<^esup>)"
apply (rule_tac l = "[Perform get, Goto sphone, Goto bankapp]" and
                a = "Goto bankapp" and I' = hc_scenario 
                and I'' = hc_scenario''' in refI)
apply (simp add: state_transition_refl_def)
(* prefer 4
apply simp *)
prefer 3
apply simp
prefer 2
apply simp
apply (rule transf_trans3)
apply (rule step1t)
apply (rule step2t)
apply (rule step3t)
by simp
*)

                
                
                
(* old version now very different see above                
lemma final_attack_a: "hc_scenario, Actor ''Carer'' \<turnstile> 
([\<N>\<^bsub>Perform get\<^esub>, \<N>\<^bsub>Goto sphone\<^esub>, \<N>\<^bsub>Goto bankapp\<^esub>, \<N>\<^bsub>Perform eval\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(''getmovemoveeval'')\<^esup>)"
(*  
apply (subgoal_tac "[\<N>\<^bsub>Perform get\<^esub>, \<N>\<^bsub>Goto sphone\<^esub>, \<N>\<^bsub>Goto bankapp\<^esub>, \<N>\<^bsub>Perform eval\<^esub>]
                 = [\<N>\<^bsub>Perform get\<^esub>] @  [\<N>\<^bsub>Goto sphone\<^esub>, \<N>\<^bsub>Goto bankapp\<^esub>, \<N>\<^bsub>Perform eval\<^esub>]")
apply (erule ssubst) *)   
apply (rule_tac s = "''getmovemoveeval''"  in att_comp_and_cons)
apply (rule_tac l = room in att_act)
apply (simp add: hc_scenario_def local_policies_def ex_locs_def ex_graph_def ex_creds_def enables_def)
apply (rule_tac I = hc_scenario' in att_comp_and_cons)
apply (rule_tac l = sphone in att_goto)
apply (simp add: hc_scenario'_def local_policies_def ex_locs_def ex_graph_def ex_creds'_def enables_def)
apply (rule_tac I = hc_scenario'' in att_comp_and_cons)
apply (rule_tac l = bankapp in att_goto)
apply (simp add: hc_scenario''_def local_policies_def ex_locs_def ex_graph'_def 
       ex_creds'_def enables_def atI_def sphone_def room_def)
apply (rule_tac I = hc_scenario'' in att_and_one)
apply (rule_tac l = bankapp in att_act)
apply (simp add: hc_scenario''_def local_policies_def ex_locs_def ex_graph'_def 
       ex_creds'_def enables_def atI_def sphone_def room_def bankapp_def)
(*     
apply (rule_tac I = hc_scenario'' in att_and_nil)
apply (simp add: state_transition_refl_def) *)
(* simplified rule for att_comp_and has no condition on the string, therefore
   less subgoals.
prefer 7
apply simp
apply simp
*)
apply (simp add: state_transition_refl_def) 
(* apply simp *) 
apply (rule step2r)
(* apply (simp add: get_attack_def) *)
by (rule step1r)

    

theorem hc_attack:"hc_scenario, Actor ''Carer'' \<turnstile> ([\<N>\<^bsub>Goto bankapp\<^esub>, \<N>\<^bsub>Perform eval\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(''getmovemoveeval'')\<^esup>)"
apply (rule_tac A' = "([\<N>\<^bsub>Perform get\<^esub>, \<N>\<^bsub>Goto sphone\<^esub>, \<N>\<^bsub>Goto bankapp\<^esub>, \<N>\<^bsub>Perform eval\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(''getmovemoveeval'')\<^esup>)" in att_ref)
apply (rule ref_lem_b)
by (rule final_attack_a)
*)

end