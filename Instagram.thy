theory Instagram
  imports UnintentionalInsider
begin

locale scenarioSN = 
fixes friends :: "identity set"
defines friends_def: "friends \<equiv> {''Alice'', ''Bob''}"
fixes sn_locations :: "location set"
defines sn_locations_def: "sn_locations \<equiv> 
          {Location 0, Location 1, Location 2}"

fixes aphone :: "location"
defines aphone_def: "aphone \<equiv> Location 0"
fixes bphone :: "location"
defines bphone_def: "bphone \<equiv> Location 1"
fixes instagram :: "location"
defines instagram_def: "instagram \<equiv> Location 2"

fixes global_policy :: "[infrastructure, identity] \<Rightarrow> bool"
defines global_policy_def: "global_policy I a \<equiv> a \<notin> friends 
                 \<longrightarrow> \<not>(enables I instagram (Actor a) get)"  

fixes ex_creds :: "actor \<Rightarrow> (string set * string set)"
defines ex_creds_def: "ex_creds \<equiv> (\<lambda> x. if x = Actor ''Alice'' then 
                         ({''aPIN''}, {}) else 
                            (if x = Actor ''Bob'' then
                                ({''bPIN''},{}) else ({},{})))"

fixes ex_psys :: "identity \<Rightarrow> actor_state"
defines "ex_psys \<equiv> (\<lambda> x. Actor_state happy {approval_hungry})"

fixes ex_locs :: "location \<Rightarrow>  (dlm * data)set"
defines "ex_locs \<equiv>  (\<lambda> x. {})"

fixes ex_locs' :: "location \<Rightarrow>  (dlm * data)set"
defines "ex_locs' \<equiv>  (\<lambda> x.  if x = instagram then
             ({((Actor ''Alice'',{Actor ''Bob''}),''Alice's_diary'')}) 
             else ({}))"

fixes ex_locs'' :: "location \<Rightarrow>  (dlm * data)set"
defines "ex_locs'' \<equiv>  (\<lambda> x.  if x = instagram then
             ({((Actor ''Alice'',{Actor ''Bob''}),''Alice's_diary'')}) 
             else (if x = bphone then ({((Actor ''Alice'',{Actor ''Bob''}),''Alice's_diary'')})  else {}))"


fixes ex_loc_ass :: "location \<Rightarrow> identity set"
defines ex_loc_ass_def: "ex_loc_ass \<equiv>
          (\<lambda> x.  if x = aphone then {''Alice''}  
                 else (if x = bphone then {''Bob''} 
                       else (if x = instagram then {''Eve''}
                             else {})))"

fixes ex_graph :: "igraph"
defines ex_graph_def: "ex_graph \<equiv> Lgraph 
     {(aphone, instagram), (bphone, instagram)}
     ex_loc_ass
     ex_creds ex_psys ex_locs"

fixes ex_graph' :: "igraph"
defines ex_graph'_def: "ex_graph' \<equiv> Lgraph 
     {(aphone, instagram), (bphone, instagram)}
       (\<lambda> x. if x = instagram then {''Alice'',''Eve''} else 
           (if x = bphone then {''Bob''} else {})) 
     ex_creds ex_psys ex_locs"

fixes ex_graph'' :: "igraph"
defines ex_graph''_def: "ex_graph'' \<equiv> Lgraph 
     {(aphone, instagram), (bphone, instagram)}
       (\<lambda> x. if x = instagram then {''Alice'',''Eve''} else 
           (if x = bphone then {''Bob''} else {})) 
     ex_creds ex_psys ex_locs'"

fixes ex_graph''' :: "igraph"
defines ex_graph'''_def: "ex_graph''' \<equiv> Lgraph 
     {(aphone, instagram), (bphone, instagram)}
       (\<lambda> x. if x = instagram then {''Alice'',''Eve''} else 
           (if x = bphone then {''Bob''} else {})) 
     ex_creds ex_psys ex_locs''"


fixes local_policies :: "[igraph, location] \<Rightarrow> apolicy set"
defines local_policies_def: "local_policies G \<equiv> 
    (\<lambda> x. if x = aphone then
        {((\<lambda> y. has G (y, ''aPIN'')), {put,get,move,eval})}
          else (if x = bphone then 
                {((\<lambda> y. has G (y, ''bPIN'')), {put,get,move,eval})} 
                else (if x = instagram then
                {(\<lambda> y. y \<in> {Actor ''Alice'', Actor ''Bob''}, {put,get,move,eval})}
                       else  {})))"

fixes sn_scenario :: "infrastructure"
defines sn_scenario_def:
"sn_scenario \<equiv> Infrastructure ex_graph local_policies"


fixes Isn :: "infrastructure set"
defines Isn_def:
  "Isn \<equiv> {sn_scenario}"

fixes sn_scenario' :: "infrastructure"
defines sn_scenario'_def:
"sn_scenario' \<equiv> Infrastructure ex_graph' local_policies"

fixes SN' :: "infrastructure set"
defines SN'_def:
  "SN' \<equiv> {sn_scenario'}"

fixes sn_scenario'' :: "infrastructure"
defines sn_scenario''_def:
"sn_scenario'' \<equiv> Infrastructure ex_graph'' local_policies"

fixes SN'' :: "infrastructure set"
defines SN''_def:
  "SN'' \<equiv> {sn_scenario''}"

fixes sn_scenario''' :: "infrastructure"
defines sn_scenario'''_def:
"sn_scenario''' \<equiv> Infrastructure ex_graph''' local_policies"

fixes SN''' :: "infrastructure set"
defines SN'''_def:
  "SN''' \<equiv> {sn_scenario'''}"


fixes sn_states
defines sn_states_def: "sn_states \<equiv> { I. sn_scenario \<rightarrow>\<^sub>i* I }"

fixes sn_Kripke
defines "sn_Kripke \<equiv> Kripke sn_states {sn_scenario}"

fixes bsn 
defines "bsn \<equiv> {x. enables x instagram (Actor ''Bob'') get}"

fixes ssn 
defines "ssn \<equiv> {x. \<not> (global_policy x ''Eve'')}"  

(* If we want to show without Insider: Assumption that there is no insider 
assumes no_insider: "inj Actor" *)
assumes insider_Alice: "Insider ''Alice'' {''Eve''} ex_psys"

begin
lemma step1: "sn_scenario \<rightarrow>\<^sub>n sn_scenario'"
proof (rule_tac l = aphone and a = "''Alice''" and l' = instagram in move)
  show "graphI sn_scenario = graphI sn_scenario" by (rule refl)
next show "''Alice'' @\<^bsub>graphI sn_scenario\<^esub> aphone"
by (simp add: sn_scenario_def ex_graph_def ex_loc_ass_def atI_def nodes_def)
next show "aphone \<in> nodes (graphI sn_scenario)"
    by (simp add: sn_scenario_def ex_graph_def ex_loc_ass_def atI_def nodes_def, blast)
next show "instagram \<in> nodes (graphI sn_scenario)"
    by (simp add: sn_scenario_def nodes_def ex_graph_def, blast)
next show "''Alice'' \<in> actors_graph (graphI sn_scenario)"
    by (simp add: actors_graph_def sn_scenario_def ex_graph_def ex_loc_ass_def nodes_def, auto)
next show "enables sn_scenario instagram (Actor ''Alice'') move"
    by (simp add: enables_def sn_scenario_def ex_graph_def local_policies_def
                    ex_creds_def ex_locs_def has_def credentials_def instagram_def bphone_def)
next show "sn_scenario' =
    Infrastructure (move_graph_a ''Alice'' aphone instagram (graphI sn_scenario)) (delta sn_scenario)"
    apply (simp add: sn_scenario'_def ex_graph'_def move_graph_a_def 
                   sn_scenario_def ex_graph_def aphone_def instagram_def bphone_def
                    ex_loc_ass_def ex_creds_def)
    apply (rule ext)
    by (simp add: bphone_def instagram_def)
qed

lemma step1r: "sn_scenario  \<rightarrow>\<^sub>n* sn_scenario'"
proof (simp add: state_transition_in_refl_def)
  show " (sn_scenario, sn_scenario') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  by (insert step1, auto)
qed

lemma step2: "sn_scenario'  \<rightarrow>\<^sub>n sn_scenario''"
proof (rule_tac l = instagram and h = "''Alice''" and hs = "{Actor ''Bob''}" and
        n = "''Alice's_diary''" in put, rule refl)
  show "''Alice'' @\<^bsub>graphI sn_scenario'\<^esub> instagram"
   by (simp add: sn_scenario'_def ex_graph'_def instagram_def aphone_def atI_def nodes_def)
next show "instagram \<in> nodes (graphI sn_scenario')"
    by (simp add: sn_scenario'_def ex_graph'_def aphone_def instagram_def atI_def nodes_def, blast)
next show "enables sn_scenario' instagram (Actor ''Alice'') put"
    by (simp add: enables_def sn_scenario'_def ex_graph_def local_policies_def
           ex_creds_def ex_locs_def has_def credentials_def instagram_def aphone_def bphone_def)
next show "unaware (pgra (graphI sn_scenario') ''Alice'')"
    by (simp add: ex_graph'_def ex_psys_def sn_scenario'_def unaware_def)
next show "sn_scenario'' =
    Infrastructure
     (Lgraph (gra (graphI sn_scenario')) (agra (graphI sn_scenario')) (cgra (graphI sn_scenario'))
       (pgra (graphI sn_scenario'))
       ((lgra (graphI sn_scenario'))
        (instagram := lgra (graphI sn_scenario') instagram \<union> {((Actor ''Alice'',{Actor ''Bob''}),''Alice's_diary'')})))
     (delta sn_scenario')"
    apply (simp add: sn_scenario'_def ex_graph''_def move_graph_a_def sn_scenario''_def 
                     ex_graph'_def instagram_def aphone_def bphone_def ex_creds_def ex_locs_def
                     ex_locs'_def)
    by (rule ext, simp)
qed

lemma step2r: "sn_scenario'  \<rightarrow>\<^sub>n* sn_scenario''"
proof (simp add: state_transition_in_refl_def)
  show "(sn_scenario', sn_scenario'') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step2, auto)
qed

lemma step3: "sn_scenario''  \<rightarrow>\<^sub>n sn_scenario'''"
proof (rule_tac l = bphone and l' = instagram and h' = "''Alice''" and h = "''Bob''" and hs = "{Actor ''Bob''}" and
        n = "''Alice's_diary''" in get_data, rule refl)
  show "''Bob'' @\<^bsub>graphI sn_scenario''\<^esub> bphone"
   by (simp add: sn_scenario''_def ex_graph''_def instagram_def bphone_def atI_def nodes_def)
next show "bphone \<in> nodes (graphI sn_scenario'')"
    by (simp add: sn_scenario''_def ex_graph''_def bphone_def instagram_def atI_def nodes_def, blast)
next show "instagram \<in> nodes (graphI sn_scenario'')"
    by (simp add: sn_scenario''_def ex_graph''_def bphone_def instagram_def atI_def nodes_def, blast)
next show "enables sn_scenario'' instagram (Actor ''Bob'') get"
    by (simp add: enables_def sn_scenario''_def ex_graph_def local_policies_def
           ex_creds_def ex_locs_def has_def credentials_def instagram_def aphone_def bphone_def)
next show "((Actor ''Alice'',{Actor ''Bob''}),''Alice's_diary'') \<in> lgra (graphI sn_scenario'') instagram"
    by (simp add: sn_scenario''_def instagram_def ex_graph''_def ex_locs'_def)
next show "Actor ''Bob'' \<in> {Actor ''Bob''} \<or> ''Bob'' = ''Alice''" by simp
next show "sn_scenario''' =
    Infrastructure
     (Lgraph (gra (graphI sn_scenario'')) (agra (graphI sn_scenario'')) (cgra (graphI sn_scenario''))
       (pgra (graphI sn_scenario''))
       ((lgra (graphI sn_scenario''))
        (bphone :=
           lgra (graphI sn_scenario'') bphone \<union>
           {((Actor ''Alice'', {Actor ''Bob''}),
             [CHR ''A'', CHR ''l'', CHR ''i'', CHR ''c'', CHR ''e'', CHR 0x27, CHR ''s'', CHR ''_'', CHR ''d'', CHR ''i'',
              CHR ''a'', CHR ''r'', CHR ''y''])})))
     (delta sn_scenario'')"
    apply (simp add: sn_scenario''_def ex_graph'''_def move_graph_a_def sn_scenario'''_def 
                     ex_graph''_def instagram_def aphone_def bphone_def ex_creds_def ex_locs''_def
                     ex_locs'_def)
    apply (rule ext)
    by (simp add: bphone_def)
qed

lemma step3r: "sn_scenario''  \<rightarrow>\<^sub>n* sn_scenario'''"
proof (simp add: state_transition_in_refl_def)
  show "(sn_scenario'', sn_scenario''') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step3, auto)
qed

(* Simple without insider possible: if Alice is unaware, she'll upload her data
   and her friend Bob can read it *)

(* TODO *)
lemma bsn_ref: "[\<N>\<^bsub>(Isn,bsn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Isn,bsn)\<^esup> \<sqsubseteq>
                  [\<N>\<^bsub>(Isn,SN')\<^esub>, \<N>\<^bsub>(SN',SN'')\<^esub>, \<N>\<^bsub>(SN'',bsn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Isn,bsn)\<^esup>"
by (metis append_Cons append_Nil refI)  

lemma att_bsn: "\<turnstile> [\<N>\<^bsub>(Isn,SN')\<^esub>, \<N>\<^bsub>(SN',SN'')\<^esub>, \<N>\<^bsub>(SN'',bsn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Isn,bsn)\<^esup>"
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(Isn, SN')\<^esub>"
   apply (simp add: Isn_def SN'_def att_base)
   apply (subst state_transition_infra_def)
   by (rule step1)
next show "\<turnstile>[\<N>\<^bsub>(SN', SN'')\<^esub>, \<N>\<^bsub>(SN'', bsn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(SN', bsn)\<^esup>"
    apply (subst att_and, simp)
    apply (rule conjI)
     apply (simp add: SN'_def SN''_def att_base)
     apply (subst state_transition_infra_def, rule step2)
    apply (subst att_and, simp)
    apply (simp add: SN''_def bsn_def att_base)
    apply (rule_tac x = sn_scenario''' in exI)
    apply (rule conjI)
     apply (simp add: sn_scenario'''_def friends_def 
                    enables_def local_policies_def instagram_def bphone_def aphone_def)
    by (subst state_transition_infra_def, rule step3)
qed

lemma bsn_abs_att: "\<turnstile>\<^sub>V [\<N>\<^bsub>(Isn,bsn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Isn,bsn)\<^esup>"
proof (rule ref_valI, rule bsn_ref, rule att_bsn)
qed

lemma bsn_att: "sn_Kripke \<turnstile> EF bsn"
proof -
  have a: "\<turnstile>[\<N>\<^bsub>(Isn,SN')\<^esub>, \<N>\<^bsub>(SN',SN'')\<^esub>, \<N>\<^bsub>(SN'',bsn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Isn,bsn)\<^esup>"
    by (rule att_bsn)
  hence "(Isn,bsn) = attack([\<N>\<^bsub>(Isn,SN')\<^esub>, \<N>\<^bsub>(SN',SN'')\<^esub>, \<N>\<^bsub>(SN'',ssn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Isn,bsn)\<^esup>)"
    by simp
  hence "Kripke {s::infrastructure. \<exists>i::infrastructure\<in>Isn. i \<rightarrow>\<^sub>i* s} Isn \<turnstile> EF bsn"
    apply (insert a)
    apply (erule AT_EF)
    by simp
  thus  "sn_Kripke \<turnstile> EF bsn"
    by (simp add: sn_Kripke_def sn_states_def Isn_def bsn_def)
qed

theorem bsn_EF: "sn_Kripke \<turnstile> EF bsn"  
proof (rule bsn_att)
qed


(* The CTL statement can now be directly translated into Attack Trees using
   the meta-theory, i.e. Correctness and Completeness theorems. *)  
theorem bsn_AT: "\<exists> A. \<turnstile> A \<and> attack A = (Isn,bsn)"
proof -
  have a: "sn_Kripke \<turnstile> EF bsn" by (rule bsn_EF)
  have b: "Isn \<noteq> {}" by (simp add: Isn_def)
  thus "\<exists>A::infrastructure attree. \<turnstile>A \<and> attack A = (Isn, bsn)" 
    apply (rule Completeness)
    apply (simp add: Isn_def)
    apply (insert a)
    by (simp add: sn_Kripke_def Isn_def sn_states_def)
qed


(* So far this has just shown that Bob - who is a friend of Alice -- can get
   her data from instagram because she labeled it with him as a reader. The
   reason is her unawareness which is a condition to the put rule.
   Now, if Bob is an insider he could be impersonated by Eve and Eve could
   thus get it. This is already possible in the "old" malicious insider model.
   However, now with the Unintentional Insiders, Eve can already impersonate Alice and
   can thus get the information straight from her, without the need to go via Bob!*)

(* The global policy is broken because it is also possible for Eve to
   access Alice's diary. For this we need that the Insider assumption holds.
   Now, we can prove this without Bob being malicious but because Alice is unaware
   and thus is an unintentional insider. *)
lemma Alice_unintentional_insider: "UasI ''Alice'' ''Eve''"
  using Insider_def ex_psys_def insider_Alice unaware_def by auto

lemma sn_ref: "[\<N>\<^bsub>(Isn,ssn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Isn,ssn)\<^esup> \<sqsubseteq>
                  [\<N>\<^bsub>(Isn,SN')\<^esub>, \<N>\<^bsub>(SN',SN'')\<^esub>, \<N>\<^bsub>(SN'',ssn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Isn,ssn)\<^esup>"
by (metis append_Cons append_Nil refI)  

lemma att_sn: "\<turnstile> [\<N>\<^bsub>(Isn,SN')\<^esub>, \<N>\<^bsub>(SN',SN'')\<^esub>, \<N>\<^bsub>(SN'',ssn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Isn,ssn)\<^esup>"
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(Isn, SN')\<^esub>"
   apply (simp add: Isn_def SN'_def att_base)
   apply (subst state_transition_infra_def)
   by (rule step1)
next show "\<turnstile>[\<N>\<^bsub>(SN', SN'')\<^esub>, \<N>\<^bsub>(SN'', ssn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(SN', ssn)\<^esup>"
    apply (subst att_and, simp)
    apply (rule conjI)
     apply (simp add: SN'_def SN''_def att_base)
     apply (subst state_transition_infra_def, rule step2)
    apply (subst att_and, simp)
    apply (simp add: SN''_def ssn_def att_base)
    apply (rule_tac x = sn_scenario''' in exI)
    apply (rule conjI)
    apply (simp add: global_policy_def)
     apply (simp add: global_policy_def sn_scenario'''_def friends_def 
                    enables_def local_policies_def instagram_def bphone_def aphone_def)
    using Alice_unintentional_insider UasI_def apply auto[1]
    by (subst state_transition_infra_def, rule step3)
qed

lemma sn_abs_att: "\<turnstile>\<^sub>V [\<N>\<^bsub>(Isn,ssn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Isn,ssn)\<^esup>"
proof (rule ref_valI, rule sn_ref, rule att_sn)
qed

lemma sn_att: "sn_Kripke \<turnstile> EF {x. \<not>(global_policy x ''Eve'')}"
proof -
  have a: "\<turnstile>[\<N>\<^bsub>(Isn,SN')\<^esub>, \<N>\<^bsub>(SN',SN'')\<^esub>, \<N>\<^bsub>(SN'',ssn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Isn,ssn)\<^esup>"
    by (rule att_sn)
  hence "(Isn,ssn) = attack([\<N>\<^bsub>(Isn,SN')\<^esub>, \<N>\<^bsub>(SN',SN'')\<^esub>, \<N>\<^bsub>(SN'',ssn)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Isn,ssn)\<^esup>)"
    by simp
  hence "Kripke {s::infrastructure. \<exists>i::infrastructure\<in>Isn. i \<rightarrow>\<^sub>i* s} Isn \<turnstile> EF ssn"
    apply (insert a)
    apply (erule AT_EF)
    by simp
  thus  "sn_Kripke \<turnstile> EF {x::infrastructure. \<not> global_policy x ''Eve''}"
    by (simp add: sn_Kripke_def sn_states_def Isn_def ssn_def)
qed

theorem sn_EF: "sn_Kripke \<turnstile> EF ssn"  
proof (insert sn_att, simp add: ssn_def)
qed


(* The CTL statement can now be directly translated into Attack Trees using
   the meta-theory, i.e. Correctness and Completeness theorems. *)  
theorem sn_AT: "\<exists> A. \<turnstile> A \<and> attack A = (Isn,ssn)"
proof -
  have a: "sn_Kripke \<turnstile> EF ssn" by (rule sn_EF)
  have b: "Isn \<noteq> {}" by (simp add: Isn_def)
  thus "\<exists>A::infrastructure attree. \<turnstile>A \<and> attack A = (Isn, ssn)" 
    apply (rule Completeness)
    apply (simp add: Isn_def)
    apply (insert a)
    by (simp add: sn_Kripke_def Isn_def sn_states_def)
qed





end