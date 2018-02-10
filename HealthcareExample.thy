theory HealthcareExample
imports Insider 
begin

locale scenarioHealthcare = 
fixes healthcare_actors :: "identity set"
defines healthcare_actors_def: "healthcare_actors \<equiv> {''Patient''}"

fixes hc_locations :: "location set"
defines hc_locations_def: "hc_locations \<equiv> 
          {Location 0, Location 1, Location 2, Location 3}"

fixes sphone :: "location"
defines sphone_def: "sphone \<equiv> Location 0"
fixes room :: "location"
defines room_def: "room \<equiv> Location 1"
fixes bankapp :: "location"
defines bankapp_def: "bankapp \<equiv> Location 2"
fixes healthapp :: "location"
defines healthapp_def: "healthapp \<equiv> Location 3"

fixes global_policy :: "[infrastructure, identity] \<Rightarrow> bool"
defines global_policy_def: "global_policy I a \<equiv> a \<noteq> ''Patient'' 
                 \<longrightarrow> \<not>(enables I bankapp (Actor a) eval)"

fixes ex_creds :: "actor \<Rightarrow> (string set * string set)"
defines ex_creds_def: "ex_creds \<equiv> (\<lambda> x. if x = Actor ''Patient'' then 
                         ({''PIN'',''skey''}, {}) else 
                            (if x = Actor ''Carer'' then
                                ({''PIN''},{}) else ({},{})))"

fixes ex_creds' :: "actor \<Rightarrow> (string set * string set)"
defines ex_creds'_def: "ex_creds' \<equiv> (\<lambda> x. if x = Actor ''Patient'' then 
                         ({''PIN'',''skey''}, {}) else 
                            (if x = Actor ''Carer'' then
                                ({''PIN'',''skey''}, {}) else ({},{})))"

fixes ex_locs :: "location \<Rightarrow> string set"
defines "ex_locs \<equiv> (\<lambda> x.  {})"

  
fixes ex_graph :: "igraph"
defines ex_graph_def: "ex_graph \<equiv> Lgraph 
     {(room, sphone), (sphone, healthapp), (sphone,bankapp)}
     (\<lambda> x. if x = room then {''Patient'', ''Carer''} else {}) 
     ex_creds ex_locs"
  
fixes ex_graph' :: "igraph"
defines ex_graph'_def: "ex_graph' \<equiv> Lgraph 
     {(room, sphone), (sphone, healthapp), (sphone,bankapp)}
     (\<lambda> x. if x = room then {''Patient'', ''Carer''} else {}) 
     ex_creds' ex_locs"
  
fixes ex_graph'' :: "igraph"
defines ex_graph''_def: "ex_graph'' \<equiv> Lgraph 
     {(room, sphone), (sphone, healthapp), (sphone,bankapp)}
     (\<lambda> x. if x = room then {''Patient''} else 
           (if x = sphone then {''Carer''} else {})) 
     ex_creds' ex_locs"

fixes ex_graph''' :: "igraph"
 defines ex_graph'''_def: "ex_graph''' \<equiv> Lgraph 
     {(room, sphone), (sphone, healthapp), (sphone,bankapp)}
     (\<lambda> x. if x = room then {''Patient''} else 
              (if x = bankapp then {''Carer''} else {})) 
     ex_creds' ex_locs"
 
fixes local_policies :: "[igraph, location] \<Rightarrow> policy set"
defines local_policies_def: "local_policies G \<equiv> 
    (\<lambda> x. if x = room then
        {(\<lambda> y. True, {put,get,move,eval})}
          else (if x = sphone then 
             {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
                else (if x = healthapp then
                {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> sphone) \<and> Actor n = y)), {put,get,move,eval})}
                       else (if x = bankapp then
                {((\<lambda> y. (\<exists> n. ((n  @\<^bsub>G\<^esub> sphone)\<or>(n  @\<^bsub>G\<^esub> bankapp )) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} else {}))))"


fixes hc_scenario :: "infrastructure"
defines hc_scenario_def:
"hc_scenario \<equiv> Infrastructure ex_graph local_policies"

fixes Ihc :: "infrastructure set"
defines Ihc_def:
  "Ihc \<equiv> {hc_scenario}"

(* other states of scenario *)


(* First step: Carer is in room with Patient and takes the skey *)
fixes hc_scenario' :: "infrastructure"
defines hc_scenario'_def:
"hc_scenario' \<equiv> Infrastructure ex_graph' local_policies"

fixes HC' :: "infrastructure set"
defines HC'_def:
  "HC' \<equiv> {hc_scenario'}"


(* Second step: Carer goes onto sphone and takes the money by eval on bankapp *)
fixes hc_scenario'' :: "infrastructure"
defines hc_scenario''_def:
"hc_scenario'' \<equiv> Infrastructure ex_graph'' local_policies"

fixes HC'' :: "infrastructure set"
defines HC''_def:
  "HC'' \<equiv> {hc_scenario''}"


(* Third step: Carer goes onto bankapp and can then get money *)
fixes hc_scenario''' :: "infrastructure"
defines hc_scenario'''_def:
"hc_scenario''' \<equiv> Infrastructure ex_graph''' local_policies"

fixes HC''' :: "infrastructure set"
defines HC'''_def:
  "HC''' \<equiv> {hc_scenario'''}"


fixes hc_states
defines hc_states_def: "hc_states \<equiv> { I. hc_scenario \<rightarrow>\<^sub>i* I }"

fixes hc_Kripke
defines "hc_Kripke \<equiv> Kripke hc_states {hc_scenario}"

fixes shc 
defines "shc \<equiv> {x. \<not> (global_policy x ''Carer'')}"  
  
begin

lemma step1: "hc_scenario  \<rightarrow>\<^sub>n hc_scenario'"
  apply (rule_tac l = room and a' = "''Carer''" and a = "''Patient''" and z = "''skey''" in get)
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
    (* instantiation gives that for free *)
by (rule step1) 

    

theorem hc_EF: "hc_Kripke \<turnstile> EF shc"
  apply (insert att_hc)
    apply (subgoal_tac "(Ihc, shc) = attack ([\<N>\<^bsub>(Ihc,HC')\<^esub>, \<N>\<^bsub>(HC',HC'')\<^esub>, \<N>\<^bsub>(HC'',shc)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Ihc,shc)\<^esup>)")
  apply (drule AT_EF)
    apply simp
   apply  (simp add: hc_Kripke_def hc_states_def Ihc_def)
  by simp
    
    



end