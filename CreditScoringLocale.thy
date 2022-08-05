section \<open>Application example from IoT healthcare\<close> 
text \<open>\<close>
theory CreditScoringLocale
  imports CreditScoringInfrastructure
begin
locale CreditScoring = 
  fixes CreditScoring_actors ::\<open>identity set\<close>
  defines CreditScoring_actors_def: \<open>CreditScoring_actors \<equiv> {''Alice'',''Bob'',''CI''}\<close>

fixes CreditScoring_locations :: "location set"
defines CreditScoring_locations_def: "CreditScoring_locations \<equiv> {Location 0, Location 1, Location 2}"
fixes N3 :: "location"
defines N3_def: "N3 \<equiv> Location 0"
fixes SE1 :: "location"
defines SE1_def: "SE1 \<equiv> Location 1"
fixes E1 :: "location"
defines E1_def: "E1 \<equiv> Location 2"


fixes ex_loc_ass :: "location \<Rightarrow> identity set"
defines ex_loc_ass_def: "ex_loc_ass \<equiv>
          (\<lambda> x. if x = N3 then {''Bob''}  
                 else (if x = SE1 then {''Alice''} 
                       else (if x = E1 then {''CI''}
                        else {})))"
fixes ex_loc_ass' :: "location \<Rightarrow> identity set"
defines ex_loc_ass'_def: "ex_loc_ass' \<equiv>
          (\<lambda> x. if x = N3 then {''Bob'', ''Alice''}  
                 else (if x = SE1 then {} 
                       else (if x = E1 then {''CI''}
                        else {})))"
(* data *)
fixes ex_data :: "identity \<Rightarrow> (dlm \<times> data)"
defines ex_data_def: \<open>ex_data \<equiv> (\<lambda> x :: identity. 
                                     (if x = ''Bob'' then ((Actor ''Bob'',{Actor ''CI''}),(N3, 35000, 1968, white))
                                      else (if x = ''Alice'' then 
                                                 ((Actor ''Alice'',{Actor ''CI''}),(SE1, 40000,1982, black))
                                            else (if x = ''CI'' then 
                                                 ((Actor ''CI'',{}), (E1, 1000000,1900,white))
                                                  else 
                                                    ((Actor '''',{}),(E1,0,0,white))))))\<close>

fixes ex_data' :: "identity \<Rightarrow> (dlm \<times> data)"
defines ex_data'_def: \<open>ex_data' \<equiv> (\<lambda> x :: identity. 
                                     (if x = ''Bob'' then ((Actor ''Bob'',{Actor ''CI''}),(N3, 40000, 1968, white))
                                      else (if x = ''Alice'' then 
                                                 ((Actor ''Alice'',{Actor ''CI''}),(SE1, 40000,1982, black))
                                            else (if x = ''CI'' then 
                                                 ((Actor ''CI'',{}), (E1, 1000000,1900,white))
                                                  else 
                                                    ((Actor '''',{}),(E1,0,0,white))))))\<close>
fixes ex_data'' :: "identity \<Rightarrow> (dlm \<times> data)"
defines ex_data''_def: \<open>ex_data'' \<equiv> (\<lambda> x :: identity. 
                                     (if x = ''Bob'' then ((Actor ''Bob'',{Actor ''CI''}),(N3, 40000, 1968, white))
                                      else (if x = ''Alice'' then 
                                                 ((Actor ''Alice'',{Actor ''CI''}),(N3, 40000,1982, black))
                                            else (if x = ''CI'' then 
                                                 ((Actor ''CI'',{}), (E1, 1000000,1900,white))
                                                  else 
                                                    ((Actor '''',{}),(E1,0,0,white))))))\<close>


fixes black_box::  "(data \<Rightarrow> bool)"
defines black_box_def: \<open>black_box \<equiv> (\<lambda> (d :: data). 
                            (if (fst d = N3) then (fst(snd d) \<ge> 40000)
                             else (if (fst d = SE1) then (fst(snd d) \<ge> 50000) else False)))\<close>

fixes ex_requests:: \<open>(identity \<times> bool option)set\<close>
defines ex_requests_def: \<open>ex_requests \<equiv> {}\<close>

fixes ex_requests':: \<open>(identity \<times> bool option)set\<close>
defines ex_requests'_def: \<open>ex_requests' \<equiv> {(''Bob'', None)}\<close>

fixes ex_requests'':: \<open>(identity \<times> bool option)set\<close>
defines ex_requests''_def: \<open>ex_requests'' \<equiv> {(''Bob'', Some(False))}\<close>

fixes ex_requests''a:: \<open>(identity \<times> bool option)set\<close>
defines ex_requests''a_def: \<open>ex_requests''a \<equiv> {(''Bob'', None), (''Bob'', Some(False))}\<close>


fixes ex_requests''':: \<open>(identity \<times> bool option)set\<close>
defines ex_requests'''_def: \<open>ex_requests''' \<equiv> {(''Bob'', Some(True)), (''Bob'', Some(False))}\<close>

fixes ex_requests'''':: \<open>(identity \<times> bool option)set\<close>
defines ex_requests''''_def: \<open>ex_requests'''' \<equiv> {(''Alice'', None),(''Bob'', Some(True)), (''Bob'', Some(False))}\<close>

fixes ex_requestsV:: \<open>(identity \<times> bool option)set\<close>
defines ex_requestsV_def: \<open>ex_requestsV \<equiv> {(''Alice'', Some(False)),(''Bob'', Some(True)), (''Bob'', Some(False))}\<close>

fixes ex_requestsV':: \<open>(identity \<times> bool option)set\<close>
defines ex_requestsV'_def: \<open>ex_requestsV' \<equiv> {(''Alice'', None), (''Alice'', Some(False)),(''Bob'', Some(True)), (''Bob'', Some(False))}\<close>

fixes ex_requestsV'':: \<open>(identity \<times> bool option)set\<close>
defines ex_requestsV''_def: \<open>ex_requestsV'' \<equiv> {(''Alice'', Some(True)), (''Alice'', Some(False)),(''Bob'', Some(True)), (''Bob'', Some(False))}\<close>

(* Graphs for the various states: initial*)
fixes ex_graph :: "igraph"
defines ex_graph_def: "ex_graph \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data black_box ex_requests"

(* Bob puts credit application in *)
fixes ex_graph' :: "igraph"
defines ex_graph'_def: "ex_graph' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data black_box ex_requests'"

(* CI evaluates Bob's application negatively *)
fixes ex_graph'' :: "igraph"
defines ex_graph''_def: "ex_graph'' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data black_box ex_requests''"


(* Next try: now from previous state Bob actions a get to get a salary increase *)
fixes ex_graph''' :: "igraph"
defines ex_graph'''_def: "ex_graph''' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data' black_box ex_requests''"


(* Bob puts in a credit application *)
fixes ex_graph'''' :: "igraph"
defines ex_graph''''_def: "ex_graph'''' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data' black_box ex_requests''a"


(* CI evaluates Bob's application - this time positive *)
fixes ex_graphV :: "igraph"
defines ex_graphV_def: "ex_graphV \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data' black_box ex_requests'''"

(* Now, Alice puts in a credit application *)
fixes ex_graphV' :: "igraph"
defines ex_graphV'_def: "ex_graphV' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data' black_box ex_requests''''"

(* Alice's application is evaluated by CI to negative *)
fixes ex_graphV'' :: "igraph"
defines ex_graphV''_def: "ex_graphV'' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data' black_box ex_requestsV"

(* Alice now moves to N3 *)
fixes ex_graphV''' :: "igraph"
defines ex_graphV'''_def: "ex_graphV''' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass' ex_data'' black_box ex_requestsV"

(* Alice now puts in an application from N3 *)
fixes ex_graphV'''' :: "igraph"
defines ex_graphV''''_def: "ex_graphV'''' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass' ex_data'' black_box ex_requestsV'"

(* This time, CI evaluates to positive *)
fixes ex_graphX :: "igraph"
defines ex_graphX_def: "ex_graphX \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass' ex_data'' black_box ex_requestsV''"


fixes local_policies :: "[igraph, location] \<Rightarrow> policy set"
defines local_policies_def: "local_policies G \<equiv> 
    (\<lambda> x. if x = N3 then  {(\<lambda> y. True, {get,move,put,eval})}
          else (if x = SE1 then {(\<lambda> y. True, {get,move,put,eval})} 
                else (if x = E1 then {(\<lambda> y. True, {get,move,put,eval})} 
                      else {})))"

(* scenario states *)
fixes Ini :: \<open>infrastructure\<close>
defines Ini_def: \<open>Ini \<equiv> Infrastructure ex_graph local_policies\<close>

fixes C :: \<open>infrastructure\<close>
defines C_def: \<open>C \<equiv> Infrastructure ex_graph' local_policies\<close>

fixes CC :: \<open>infrastructure\<close>
defines CC_def: \<open>CC \<equiv> Infrastructure ex_graph'' local_policies\<close>

fixes Ca :: \<open>infrastructure\<close>
defines Ca_def: \<open>Ca \<equiv> Infrastructure ex_graph''' local_policies\<close>

fixes CCa :: \<open>infrastructure\<close>
defines CCa_def: \<open>CCa \<equiv> Infrastructure ex_graph'''' local_policies\<close>

fixes CCCa :: \<open>infrastructure\<close>
defines CCCa_def: \<open>CCCa \<equiv> Infrastructure ex_graphV local_policies\<close>

fixes Cb :: \<open>infrastructure\<close>
defines Cb_def: \<open>Cb \<equiv> Infrastructure ex_graphV' local_policies\<close>

fixes CCb :: \<open>infrastructure\<close>
defines CCb_def: \<open>CCb \<equiv> Infrastructure ex_graphV'' local_policies\<close>

fixes Cc :: \<open>infrastructure\<close>
defines Cc_def: \<open>Cc \<equiv> Infrastructure ex_graphV''' local_policies\<close>

fixes CCc :: \<open>infrastructure\<close>
defines CCc_def: \<open>CCc \<equiv> Infrastructure ex_graphV'''' local_policies\<close>

fixes CCCc :: \<open>infrastructure\<close>
defines CCCc_def: \<open>CCCc \<equiv> Infrastructure ex_graphX local_policies\<close>

(* The Credit scoring Kripke structure *)
fixes Credit_states
defines Credit_states_def: \<open>Credit_states \<equiv> {s. Ini \<rightarrow>\<^sub>i* s }\<close>
fixes Credit_Kripke
defines Credit_Kripke_def: \<open>Credit_Kripke \<equiv> Kripke Credit_states {Ini}\<close>
fixes M
defines M_def: \<open>M \<equiv> Credit_Kripke\<close>

(* The desirable outcome DO *)
fixes DO :: \<open>identity \<Rightarrow> infrastructure \<Rightarrow> bool\<close>
defines DO_def: \<open>DO a s \<equiv> (a, Some True) \<in> requests (graphI s)\<close>


fixes ndobob
defines ndobob_def: \<open>ndobob \<equiv> {(s :: infrastructure). \<not>(DO ''Bob''  s)}\<close>

fixes salary :: "identity \<Rightarrow> infrastructure \<Rightarrow> nat"
defines salary_def: \<open>(salary a s) \<equiv> (fst(snd(snd(dgra (graphI s) a))))\<close>

fixes pc0 
defines pc0_def: \<open>pc0 A s \<equiv> (salary A s \<ge> 40000)\<close>

fixes ndoalice
defines ndoalice_def: \<open>ndoalice \<equiv> {(s :: infrastructure). (pc0 ''Alice'' s) \<and> \<not>(DO ''Alice''  s)}\<close>

fixes pc1
defines pc1_def: \<open>pc1 A s \<equiv> (salary A s \<ge> 40000 \<and> (A  @\<^bsub>(graphI s)\<^esub> N3))\<close>

begin 

(* lemmas for the state transitions: a bit tedious but almost all done by sledgehammer automatically*)
lemma stepI_C: "Ini  \<rightarrow>\<^sub>n C"
proof (rule_tac l = N3 and a = "''Bob''" in put)
  show "graphI Ini = graphI Ini" by (rule refl)
next show "''Bob'' @\<^bsub>graphI Ini\<^esub> N3"
    by (simp add: Ini_def atI_def ex_graph_def ex_loc_ass_def)
next show "N3 \<in> nodes (graphI Ini)"
    using Ini_def ex_graph_def nodes_def by auto
next show \<open>enables Ini N3 (Actor ''Bob'') put\<close>
    by (simp add: Ini_def enables_def local_policies_def)
next show \<open>C = Infrastructure (put_graph_a ''Bob'' N3 (graphI Ini)) (delta Ini)\<close>
    by (simp add: C_def Ini_def ex_graph'_def ex_graph_def ex_requests'_def ex_requests_def put_graph_a_def)
qed

lemma stepC_CC: "C  \<rightarrow>\<^sub>n CC"
proof (rule_tac l = N3 and a = "''Bob''" and c = "''CI''" in eval)
  show \<open>graphI C = graphI C\<close> by (rule refl)
next show \<open>''Bob'' @\<^bsub>graphI C\<^esub> N3\<close>
    by (simp add: C_def atI_def ex_graph'_def ex_loc_ass_def)
next show \<open>N3 \<in> nodes (graphI C)\<close>
    using C_def ex_graph'_def nodes_def by auto
next show \<open>''CI'' \<in> actors_graph (graphI C)\<close>
    apply (simp add: actors_graph_def)
    by (metis (no_types, lifting) C_def E1_def N3_def One_nat_def SE1_def Suc_n_not_le_n agra.simps ex_graph'_def ex_loc_ass_def gra.simps graphI.simps insertCI location.inject mem_Collect_eq nat_le_linear nodes_def numeral_2_eq_2)
next show "(''Bob'', None) \<in> requests (graphI C)"
    by (simp add: C_def ex_graph'_def ex_requests'_def)
next show \<open> Actor ''CI'' \<in> readers (dgra (graphI C) ''Bob'') \<or> Actor ''CI'' = owner (dgra (graphI C) ''Bob'')\<close>
    by (simp add: readers_def C_def ex_graph'_def ex_data_def)
next show \<open>enables C N3 (Actor ''CI'') eval\<close>
    by (simp add: C_def enables_def local_policies_def)
next show "CC = Infrastructure (eval_graph_a ''Bob'' N3 (graphI C)) (delta C)"
    by (simp add: eval_graph_a_def C_def CC_def ex_graph'_def ex_graph''_def black_box_def 
                    ex_requests''_def ex_requests'_def ex_data_def)
qed

lemma stepCC_Ca: "CC  \<rightarrow>\<^sub>n Ca"
proof (rule_tac l = N3 and a = "''Bob''" and m = "40000" in get)
  show "graphI CC = graphI CC" by (rule refl)
next show "''Bob'' @\<^bsub>graphI CC\<^esub> N3"
    by (simp add: CC_def atI_def ex_graph''_def ex_loc_ass_def) 
next show \<open>N3 \<in> nodes (graphI CC)\<close>
    using CC_def ex_graph''_def nodes_def by auto
next show \<open>enables CC N3 (Actor ''Bob'') get\<close>
    by (simp add: CC_def enables_def local_policies_def)
next show \<open>Ca = Infrastructure (get_graph_a ''Bob'' N3 40000 (graphI CC)) (delta CC) \<close>
    apply (simp add: get_graph_a_def CC_def Ca_def ex_graph''_def ex_graph'''_def ex_data_def ex_data'_def)
    apply (rule ext)
    by force
qed

lemma stepCa_CCa: "Ca  \<rightarrow>\<^sub>n CCa"
proof (rule_tac l = N3 and a = "''Bob''" in put)
  show "graphI Ca = graphI Ca" by (rule refl)
next show \<open>''Bob'' @\<^bsub>graphI Ca\<^esub> N3\<close>
    by (simp add: Ca_def atI_def ex_graph'''_def ex_loc_ass_def)
next show \<open>N3 \<in> nodes (graphI Ca)\<close>
    using Ca_def ex_graph'''_def nodes_def by auto
next show \<open>enables Ca N3 (Actor ''Bob'') put\<close>
    by (simp add: Ca_def enables_def local_policies_def)
next show \<open>CCa = Infrastructure (put_graph_a ''Bob'' N3 (graphI Ca)) (delta Ca)\<close>
    by (simp add: put_graph_a_def CCa_def Ca_def ex_graph''''_def ex_graph'''_def ex_requests''_def ex_requests''a_def)
qed

lemma stepCCa_CCCa: "CCa  \<rightarrow>\<^sub>n CCCa"
proof (rule_tac l = N3 and a = "''Bob''" and c = \<open>''CI''\<close> in eval)
  show \<open>graphI CCa = graphI CCa\<close> by (rule refl)
next show \<open>''Bob'' @\<^bsub>graphI CCa\<^esub> N3\<close>
    by (simp add: CCa_def atI_def ex_graph''''_def ex_loc_ass_def)
next show \<open>N3 \<in> nodes (graphI CCa)\<close>
    using CCa_def ex_graph''''_def nodes_def by auto
next show \<open>''CI'' \<in> actors_graph (graphI CCa)\<close>
    apply (simp add: actors_graph_def)
    by (metis (no_types, lifting) CCa_def E1_def N3_def One_nat_def SE1_def Suc_n_not_le_n agra.simps ex_graph''''_def ex_loc_ass_def gra.simps graphI.simps insertCI location.inject mem_Collect_eq nat_le_linear nodes_def numeral_2_eq_2)
next show \<open>(''Bob'', None) \<in> requests (graphI CCa)\<close>
    by (simp add: CCa_def ex_graph''''_def ex_requests''a_def)
next show \<open>Actor ''CI'' \<in> readers (dgra (graphI CCa) ''Bob'') \<or> Actor ''CI'' = owner (dgra (graphI CCa) ''Bob'')\<close>
    by (simp add: readers_def CCa_def ex_graph''''_def ex_data'_def)
next show \<open>enables CCa N3 (Actor ''CI'') eval\<close>
    by (simp add: CCa_def enables_def local_policies_def)
next show \<open>CCCa = Infrastructure (eval_graph_a ''Bob'' N3 (graphI CCa)) (delta CCa)  \<close>
    by (simp add: eval_graph_a_def CCCa_def ex_graphV_def CCa_def ex_graph''''_def 
          ex_requests'''_def black_box_def ex_requests''a_def ex_data'_def)
qed

lemma stepCCCa_Cb: "CCCa  \<rightarrow>\<^sub>n Cb"
proof (rule_tac l = SE1 and a = "''Alice''"  in put)
  show \<open>graphI CCCa = graphI CCCa\<close> by (rule refl)
next show \<open>''Alice'' @\<^bsub>graphI CCCa\<^esub> SE1\<close>
    by (simp add: CCCa_def N3_def SE1_def atI_def ex_graphV_def ex_loc_ass_def)
next show \<open>SE1 \<in> nodes (graphI CCCa)\<close>
    using CCCa_def ex_graphV_def nodes_def by auto
next show \<open>enables CCCa SE1 (Actor ''Alice'') put\<close>
    by (simp add: CCCa_def enables_def local_policies_def)
next show \<open>Cb = Infrastructure (put_graph_a ''Alice'' SE1 (graphI CCCa)) (delta CCCa)\<close>
    by (simp add: put_graph_a_def CCCa_def Cb_def ex_graphV'_def ex_graphV_def ex_requests''''_def ex_requests'''_def)
qed

lemma stepCb_CCb: "Cb  \<rightarrow>\<^sub>n CCb"
proof (rule_tac l = SE1 and a = "''Alice''"  and c = "''CI''" in eval)
  show \<open>graphI Cb = graphI Cb\<close> by (rule refl)
next show \<open>''Alice'' @\<^bsub>graphI Cb\<^esub> SE1\<close>
    by (simp add: Cb_def N3_def SE1_def atI_def ex_graphV'_def ex_loc_ass_def)
next show \<open>SE1 \<in> nodes (graphI Cb)\<close>
    using Cb_def ex_graphV'_def nodes_def by auto
next show \<open>''CI'' \<in> actors_graph (graphI Cb)\<close>
    apply (simp add: actors_graph_def)
    by (metis (no_types, lifting) Cb_def E1_def N3_def One_nat_def SE1_def Suc_n_not_le_n agra.simps ex_graphV'_def ex_loc_ass_def gra.simps graphI.simps insertCI location.inject mem_Collect_eq nat_le_linear nodes_def numeral_2_eq_2)
next show \<open>(''Alice'', None) \<in> requests (graphI Cb)\<close>
    by (simp add: Cb_def ex_graphV'_def ex_requests''''_def)
next show \<open>Actor ''CI'' \<in> readers (dgra (graphI Cb) ''Alice'') \<or> Actor ''CI'' = owner (dgra (graphI Cb) ''Alice'')\<close>
    by (simp add: readers_def Cb_def ex_graphV'_def ex_data'_def)
next show \<open>enables Cb SE1 (Actor ''CI'') eval\<close>
    by (simp add: Cb_def enables_def local_policies_def) 
next show \<open>CCb = Infrastructure (eval_graph_a ''Alice'' SE1 (graphI Cb)) (delta Cb) \<close>
    by (simp add: eval_graph_a_def CCb_def ex_graphV''_def Cb_def ex_graphV'_def ex_requestsV_def ex_requests''''_def
                     black_box_def SE1_def N3_def ex_data'_def)
qed

lemma stepCCb_Cc: "CCb  \<rightarrow>\<^sub>n Cc"
proof (rule_tac l = SE1 and l' = N3 and a = "''Alice''"  in move)
  show \<open>graphI CCb = graphI CCb\<close> by (rule refl)
next show \<open>''Alice'' @\<^bsub>graphI CCb\<^esub> SE1\<close>
    by (simp add: CCb_def N3_def SE1_def atI_def ex_graphV''_def ex_loc_ass_def)
next show \<open>SE1 \<in> nodes (graphI CCb)\<close>
    using CCb_def ex_graphV''_def nodes_def by auto
next show \<open>N3 \<in> nodes (graphI CCb)\<close>
    using CCb_def ex_graphV''_def nodes_def by auto
next show \<open>''Alice'' \<in> actors_graph (graphI CCb)\<close>
    apply (simp add: actors_graph_def CCb_def ex_graphV''_def ex_loc_ass_def E1_def SE1_def N3_def nodes_def)
    by (metis loc.simps n_not_Suc_n numeral_2_eq_2)
  next show \<open>enables CCb N3 (Actor ''Alice'') move\<close>
    by (simp add: CCb_def enables_def local_policies_def)
next show \<open>Cc = Infrastructure (move_graph_a ''Alice'' SE1 N3 (graphI CCb)) (delta CCb)\<close>
    apply (simp add: move_graph_a_def Cc_def ex_graphV'''_def CCb_def ex_graphV''_def ex_loc_ass_def
             ex_loc_ass'_def ex_data'_def ex_data''_def SE1_def N3_def)
    apply (rule conjI)
    apply (rule ext)
     apply (simp add: SE1_def insert_commute)
    apply (rule ext)
    by (simp add: N3_def)
qed

lemma stepCc_CCc: "Cc  \<rightarrow>\<^sub>n CCc"
proof (rule_tac l = N3 and a = "''Alice''"  in put)
  show \<open>graphI Cc = graphI Cc\<close> by (rule refl)
next show \<open>''Alice'' @\<^bsub>graphI Cc\<^esub> N3\<close>
    by (simp add: Cc_def atI_def ex_graphV'''_def ex_loc_ass'_def) 
next show \<open> N3 \<in> nodes (graphI Cc)\<close>
    using Cc_def ex_graphV'''_def nodes_def by auto
next show \<open> enables Cc N3 (Actor ''Alice'') put\<close>
    by (simp add: Cc_def enables_def local_policies_def)
next show \<open>CCc = Infrastructure (put_graph_a ''Alice'' N3 (graphI Cc)) (delta Cc)\<close>
    by (simp add: put_graph_a_def CCc_def ex_graphV'''_def ex_loc_ass'_def Cc_def ex_graphV''''_def ex_requestsV_def
                     ex_requestsV'_def)
qed

lemma stepCCc_CCCc: "CCc  \<rightarrow>\<^sub>n CCCc"
proof (rule_tac l = N3 and a = "''Alice''" and c = "''CI''" in eval)
  show \<open>graphI CCc = graphI CCc\<close> by (rule refl)
next show \<open>''Alice'' @\<^bsub>graphI CCc\<^esub> N3\<close>
    by (simp add: CCc_def atI_def ex_graphV''''_def ex_loc_ass'_def)
next show \<open>N3 \<in> nodes (graphI CCc)\<close>
    using CCc_def ex_graphV''''_def nodes_def by auto
next show \<open>''CI'' \<in> actors_graph (graphI CCc)\<close>
    apply (simp add: actors_graph_def CCc_def ex_graphV''''_def nodes_def ex_loc_ass'_def E1_def SE1_def N3_def)
    by blast 
next show \<open> (''Alice'', None) \<in> requests (graphI CCc)\<close>
    by (simp add: CCc_def ex_graphV''''_def ex_requestsV'_def)
next show \<open> Actor ''CI'' \<in> readers (dgra (graphI CCc) ''Alice'') \<or> Actor ''CI'' = owner (dgra (graphI CCc) ''Alice'')\<close> 
    by (simp add: readers_def CCc_def ex_graphV''''_def ex_data''_def)
next show \<open>enables CCc N3 (Actor ''CI'') eval\<close>
    by (simp add: CCc_def enables_def local_policies_def)
next show \<open>CCCc = Infrastructure (eval_graph_a ''Alice'' N3 (graphI CCc)) (delta CCc)\<close>
    by (simp add: eval_graph_a_def CCCc_def ex_graphX_def CCc_def ex_graphV''''_def ex_requestsV'_def ex_requestsV''_def
                     black_box_def ex_data''_def)
qed

(* Application of PCR cycle *)

(* Step 1: find an attack *)
lemma att_ndobob_Kripke: \<open>\<turnstile>([\<N>\<^bsub>({Ini},{C})\<^esub>, \<N>\<^bsub>({C},ndobob)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({Ini},ndobob)\<^esup>)\<close>
proof (subst att_and, simp, rule conjI)
  show \<open>\<turnstile>\<N>\<^bsub>({Ini}, {C})\<^esub>\<close>
    apply (simp add: att_base)
    using state_transition_infra_def stepI_C by fastforce
next show \<open>\<turnstile>[\<N>\<^bsub>({C}, ndobob)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({C}, ndobob)\<^esup>\<close>
    apply (subst att_and, simp)
    apply (simp add: ndobob_def is_attack_tree.simps(1) state_transition_infra_def)
    apply (rule_tac x = CC in exI)
    apply (rule conjI)
    prefer 2
    using stepC_CC apply blast
    by (simp add: DO_def CC_def ex_graph''_def ex_requests''_def)
qed

(* The attack gives us the CTL formula by Correctness of AT *)
lemma Credit_att: "M \<turnstile> EF ndobob"
proof -
  have a: \<open>\<turnstile>([\<N>\<^bsub>({Ini},{C})\<^esub>, \<N>\<^bsub>({C},ndobob)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({Ini},ndobob)\<^esup>)\<close> by (rule att_ndobob_Kripke)
  hence "({Ini}, ndobob) = attack (([\<N>\<^bsub>({Ini},{C})\<^esub>, \<N>\<^bsub>({C},ndobob)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({Ini},ndobob)\<^esup>))" by simp
  hence \<open>Kripke {s::infrastructure. \<exists>i::infrastructure\<in> {Ini}. i \<rightarrow>\<^sub>i* s} {Ini} \<turnstile> EF ndobob\<close>
    using AT_EF att_ndobob_Kripke by fastforce
  thus \<open>M \<turnstile> EF ndobob\<close>
    by (simp add: Credit_Kripke_def Credit_states_def M_def)
qed

(* Step 2: Now, apply counterfactuals to find a close state with DO and first precondition:
  Find an initial precondition that yields the desirable outcome DO 
  in a closest state using counterfactuals. *) 

(* Application of counterfactuals to find that closest state with DO is CCCa *)
lemma counterfactual_CCCa: \<open>CCCa \<in> (counterfactuals CC (\<lambda> s. DO ''Bob'' s))\<close>
  apply (simp add: counterfactuals_def)
  apply (rule conjI)
   apply (simp add: CCCa_def DO_def ex_graphV_def ex_requests'''_def)
  apply (rule_tac x = CC in exI)
  apply (rule conjI)
   apply (subgoal_tac \<open>CC \<rightarrow>\<^sub>n* Ca\<close>)
  apply (subgoal_tac \<open>Ca \<rightarrow>\<^sub>n* CCa\<close>)
  apply (subgoal_tac \<open>CCa \<rightarrow>\<^sub>n* CCCa\<close>)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCCa_CCCa)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCa_CCa)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCC_Ca)
(* *)
  apply (simp add: closest_def)
  apply (rule conjI)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
    apply (subgoal_tac \<open>CC \<rightarrow>\<^sub>n* Ca\<close>)
  apply (subgoal_tac \<open>Ca \<rightarrow>\<^sub>n* CCa\<close>)
  apply (subgoal_tac \<open>CCa \<rightarrow>\<^sub>n* CCCa\<close>)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCCa_CCCa)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCa_CCa)
by (simp add: r_into_rtrancl state_transition_in_refl_def stepCC_Ca)

(* As a result the new (first) precondition is pc0 \<equiv> salary A \<ge> 40000 *)

(* Step 3: Generalisation *)
(* Try to generalize over all actors, that is, try to show for all actors A
    AG {w. pc0 \<longrightarrow> DO A s }*)
(* Attack tree analysis shows that this fails because for Alice there is a path to
   a failure state where pc0 holds but not DO. *)

lemma att_nodoalice_Kripke: \<open>\<turnstile>([\<N>\<^bsub>({Ini},{C})\<^esub>, \<N>\<^bsub>({C},{CC})\<^esub>,\<N>\<^bsub>({CC},{Ca})\<^esub>,\<N>\<^bsub>({Ca},{CCa})\<^esub>, 
                        \<N>\<^bsub>({CCa},{CCCa})\<^esub>, \<N>\<^bsub>({CCCa},{Cb})\<^esub>,\<N>\<^bsub>({Cb},ndoalice)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({Ini},ndoalice)\<^esup>)\<close>
proof (subst att_and, simp, rule conjI)
  show \<open>\<turnstile>\<N>\<^bsub>({Ini}, {C})\<^esub>\<close>
    by (simp add: AT.att_base state_transition_infra_def stepI_C)
next show \<open> \<turnstile>[\<N>\<^bsub>({C}, {CC})\<^esub>, \<N>\<^bsub>({CC}, {Ca})\<^esub>, \<N>\<^bsub>({Ca}, {CCa})\<^esub>, \<N>\<^bsub>({CCa}, {CCCa})\<^esub>, \<N>\<^bsub>({CCCa}, {Cb})\<^esub>, 
              \<N>\<^bsub>({Cb}, ndoalice)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({C}, ndoalice)\<^esup>\<close>
    apply (subst att_and, simp, rule conjI)
     apply (simp add: att_base)
     apply (simp add: state_transition_infra_def stepC_CC)
    apply (subst att_and, simp, rule conjI)
     apply (simp add: att_base)
     apply (simp add: state_transition_infra_def stepCC_Ca)
    apply (subst att_and, simp, rule conjI)
     apply (simp add: att_base)
     apply (simp add: state_transition_infra_def stepCa_CCa)
    apply (subst att_and, simp, rule conjI)
     apply (simp add: att_base)
     apply (simp add: state_transition_infra_def stepCCa_CCCa)
    apply (subst att_and, simp, rule conjI)
     apply (simp add: att_base)
     apply (simp add: state_transition_infra_def stepCCCa_Cb)
    apply (subst att_and, simp add: ndoalice_def)
    apply (simp add: att_base)
    apply (rule_tac x = CCb in exI)
    apply (rule conjI)
     apply (simp add: CCb_def ex_graphV''_def pc0_def salary_def ex_data'_def)
    apply (rule conjI)
     apply (simp add: DO_def CCb_def ex_graphV''_def ex_requestsV_def)
    by (simp add: state_transition_infra_def stepCb_CCb)
qed

(* Application of counterfactuals to find that the closest state to  CCb where DO holds is CCc.
   This isnpires the next precondition pc1 as in CCCc we have 
   salary A s \<ge> 40000 \<and> A  @\<^bsub>(graphI s)\<^esub> N3) *)
lemma counterfactual_CCCc: \<open>CCCc \<in> (counterfactuals CCb (\<lambda> s. DO ''Alice'' s))\<close>
  apply (simp add: counterfactuals_def)
  apply (rule conjI)
  apply (simp add: CCCc_def DO_def ex_graphX_def ex_requestsV''_def)
  apply (rule_tac x = CCb in exI)
  apply (rule conjI)
   apply (subgoal_tac \<open>CCb \<rightarrow>\<^sub>n* Cc\<close>)
   apply (subgoal_tac \<open>Cc \<rightarrow>\<^sub>n* CCc\<close>)
   apply (subgoal_tac \<open>CCc \<rightarrow>\<^sub>n* CCCc\<close>)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
     apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCCc_CCCc)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCc_CCc)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCCb_Cc)
  apply (simp add: closest_def)
  apply (rule conjI)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
   apply (subgoal_tac \<open>CCb \<rightarrow>\<^sub>n* Cc\<close>)
   apply (subgoal_tac \<open>Cc \<rightarrow>\<^sub>n* CCc\<close>)
   apply (subgoal_tac \<open>CCc \<rightarrow>\<^sub>n* CCCc\<close>)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
     apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCCc_CCCc)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCc_CCc)
  by (simp add: r_into_rtrancl state_transition_in_refl_def stepCCb_Cc)

(* The attack gives us the CTL formula of reachability of the failure state by Correctness of AT *)
lemma Credit_att': "M \<turnstile> EF ndoalice"
proof -
  have a: \<open>\<turnstile>([\<N>\<^bsub>({Ini},{C})\<^esub>, \<N>\<^bsub>({C},{CC})\<^esub>,\<N>\<^bsub>({CC},{Ca})\<^esub>,\<N>\<^bsub>({Ca},{CCa})\<^esub>, 
                        \<N>\<^bsub>({CCa},{CCCa})\<^esub>, \<N>\<^bsub>({CCCa},{Cb})\<^esub>,\<N>\<^bsub>({Cb},ndoalice)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({Ini},ndoalice)\<^esup>)\<close> 
    by (rule att_nodoalice_Kripke)
  hence "({Ini}, ndoalice) = attack ([\<N>\<^bsub>({Ini},{C})\<^esub>, \<N>\<^bsub>({C},{CC})\<^esub>,\<N>\<^bsub>({CC},{Ca})\<^esub>,\<N>\<^bsub>({Ca},{CCa})\<^esub>, 
                        \<N>\<^bsub>({CCa},{CCCa})\<^esub>, \<N>\<^bsub>({CCCa},{Cb})\<^esub>,\<N>\<^bsub>({Cb},ndoalice)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({Ini},ndoalice)\<^esup>)" by simp
  hence \<open>Kripke {s::infrastructure. \<exists>i::infrastructure\<in> {Ini}. i \<rightarrow>\<^sub>i* s} {Ini} \<turnstile> EF ndoalice\<close>
    using AT_EF att_nodoalice_Kripke by fastforce
  thus \<open>M \<turnstile> EF ndoalice\<close>
    by (simp add: Credit_Kripke_def Credit_states_def M_def)
qed

(* Next iteration: go back to 2 with the new precondition 
   pc1 A s  \<equiv>  (salary A s \<ge> 40000 \<and> (A  @\<^bsub>(graphI s)\<^esub> N3)).
   Now thgeneralisation step succeeds. *)
lemma Alice_Bob_in_Credit_Kripke: "s \<in> states(Credit_Kripke)  \<Longrightarrow> 
      actors_graph (graphI s) = {''Alice'',''Bob'',''CI''}"
  apply (subgoal_tac \<open>(Ini, s) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<close>)
  prefer 2
   apply (smt (verit, del_insts) CollectD Collect_cong Credit_Kripke_def Credit_states_def split_cong state_transition_infra_def state_transition_refl_def states.simps)
  apply (subgoal_tac \<open>actors_graph (graphI Ini) =  {''Alice'',''Bob'',''CI''}\<close>)
   apply (erule subst)
   apply (rule sym)
   apply (erule same_actors)
  apply (simp add: Ini_def ex_graph_def actors_graph_def ex_loc_ass_def E1_def SE1_def N3_def nodes_def)
  apply (rule equalityI)
   apply fastforce
  apply (rule subsetI)
  apply (rule CollectI)
  apply (subgoal_tac \<open>x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''CI''\<close>)
   apply (metis (no_types, lifting) location.inject n_not_Suc_n numeral_2_eq_2 zero_neq_numeral)
  by force

lemma step_rtrancl: \<open>a \<rightarrow>\<^sub>n b \<Longrightarrow> a \<rightarrow>\<^sub>i* b\<close>
  by (simp add: r_into_rtrancl state_transition_infra_def state_transition_refl_def)

lemma enables_move0: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> 
     \<forall> a \<in> actors_graph (graphI y). \<forall> l \<in> nodes (graphI y). enables y l (Actor a) move\<close>
proof (erule rtrancl_induct)
  show \<open>\<forall>a\<in>actors_graph (graphI Ini). \<forall>l\<in>nodes (graphI Ini). enables Ini l (Actor a) move\<close>
  proof (clarify, simp add: Ini_def ex_graph_def local_policies_def  nodes_def enables_def
         E1_def N3_def SE1_def, erule exE, blast)
  qed
next show \<open>\<And>y z. (Ini, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI y). \<forall>l\<in>nodes (graphI y). enables y l (Actor a) move \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI z). \<forall>l\<in>nodes (graphI z). enables z l (Actor a) move\<close>
    apply (clarify, simp add: Ini_def ex_graph_def local_policies_def  nodes_def enables_def
         E1_def N3_def SE1_def, erule exE)
    apply (erule state_transition_in.cases)
    apply (smt (z3) delta.simps gra.simps graphI.simps init_state_policy local_policies_def put put_graph_a_def same_actors0)
    apply (smt (z3) case_prodI delta.simps empty_iff eval_graph_a_def gra.simps graphI.simps init_state_policy insert_iff local_policies_def)
     apply (simp add: enables_def)
    apply (erule bexE)
     apply (rule_tac x = x in bexI)
proof -
  fix yb :: infrastructure and z :: infrastructure and a :: "char list" and l :: location and ya :: location and G :: igraph and I :: infrastructure and aa :: "char list" and la :: location and l' :: location and I' :: infrastructure and x :: "(actor \<Rightarrow> bool) \<times> action set"
  assume a1: "case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor aa)"
assume a2: "x \<in> delta I (graphI I) l'"
  assume a3: "(Infrastructure (Lgraph {(Location 0, Location (Suc 0)), (Location 0, Location 2), (Location (Suc 0), Location 2)} ex_loc_ass ex_data black_box ex_requests) local_policies, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  then have "local_policies (graphI I) l' = {(\<lambda>a. True, {get, move, put, eval})}"
    using a2 by (metis (no_types) delta.simps empty_iff init_state_policy local_policies_def)
    then show "case x of (p, A) \<Rightarrow> move \<in> A \<and> p (Actor a)"
using a3 a2 a1 init_state_policy by fastforce
next show \<open>\<And>y z a l ya G I aa la l' I' x.
       (Infrastructure
         (Lgraph {(Location 0, Location (Suc 0)), (Location 0, Location 2), (Location (Suc 0), Location 2)} ex_loc_ass
           ex_data black_box ex_requests)
         local_policies,
        I)
       \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       \<forall>a\<in>actors_graph (graphI I).
          \<forall>l. (\<exists>y. (l, y) \<in> gra (graphI I) \<or> (y, l) \<in> gra (graphI I)) \<longrightarrow>
              (\<exists>x\<in>delta I (graphI I) l. case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor a)) \<Longrightarrow>
       a \<in> actors_graph (move_graph_a aa la l' (graphI I)) \<Longrightarrow>
       (l, ya) \<in> gra (move_graph_a aa la l' (graphI I)) \<or> (ya, l) \<in> gra (move_graph_a aa la l' (graphI I)) \<Longrightarrow>
       y = I \<Longrightarrow>
       z = Infrastructure (move_graph_a aa la l' (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       aa @\<^bsub>graphI I\<^esub> la \<Longrightarrow>
       la \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       I' = Infrastructure (move_graph_a aa la l' (graphI I)) (delta I) \<Longrightarrow>
       x \<in> delta I (graphI I) l' \<Longrightarrow>
       case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor aa) \<Longrightarrow> x \<in> delta I (move_graph_a aa la l' (graphI I)) l\<close>
    apply (simp add: move_graph_a_def local_policies_def init_state_policy)
    by (smt (z3) delta.simps empty_iff init_state_policy local_policies_def)
next show \<open>\<And>y z a l ya G I aa la I' m.
       (Infrastructure
         (Lgraph {(Location 0, Location (Suc 0)), (Location 0, Location 2), (Location (Suc 0), Location 2)} ex_loc_ass
           ex_data black_box ex_requests)
         local_policies,
        y)
       \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       \<forall>a\<in>actors_graph (graphI y).
          \<forall>l. (\<exists>ya. (l, ya) \<in> gra (graphI y) \<or> (ya, l) \<in> gra (graphI y)) \<longrightarrow>
              (\<exists>x\<in>delta y (graphI y) l. case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor a)) \<Longrightarrow>
       a \<in> actors_graph (graphI z) \<Longrightarrow>
       (l, ya) \<in> gra (graphI z) \<or> (ya, l) \<in> gra (graphI z) \<Longrightarrow>
       y = I \<Longrightarrow>
       z = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> nodes G \<Longrightarrow>
       enables I la (Actor aa) get \<Longrightarrow>
       I' = Infrastructure (get_graph_a aa la m G) (delta I) \<Longrightarrow>
       \<exists>x\<in>delta z (graphI z) l. case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor a) \<close>
     apply (simp add: enables_def)
    apply (erule bexE)
     apply (rule_tac x = x in bexI)
proof -
fix yb :: infrastructure and z :: infrastructure and a :: "char list" and l :: location and ya :: location and G :: igraph and I :: infrastructure and aa :: "char list" and la :: location and I' :: infrastructure and m :: nat and x :: "(actor \<Rightarrow> bool) \<times> action set"
  assume "G = graphI I"
  assume a1: "x \<in> delta I (graphI I) la"
assume "(Infrastructure (Lgraph {(Location 0, Location (Suc 0)), (Location 0, Location 2), (Location (Suc 0), Location 2)} ex_loc_ass ex_data black_box ex_requests) local_policies, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  then have f2: "delta I = local_policies"
    by (smt (z3) delta.simps init_state_policy)
  have "\<forall>p pa. \<exists>paa A. ((case p of (x::actor \<Rightarrow> bool, xa::action set) \<Rightarrow> pa x xa) \<or> (paa, A) = p) \<and> (\<not> pa paa A \<or> (case p of (x, xa) \<Rightarrow> pa x xa))"
  by auto
then show "case x of (p, A) \<Rightarrow> move \<in> A \<and> p (Actor a)"
  using f2 a1 by (smt (z3) empty_iff fst_conv insertI1 insert_iff local_policies_def snd_conv)
next show \<open>\<And>y z a l ya G I aa la I' m x.
       (Infrastructure
         (Lgraph {(Location 0, Location (Suc 0)), (Location 0, Location 2), (Location (Suc 0), Location 2)} ex_loc_ass
           ex_data black_box ex_requests)
         local_policies,
        I)
       \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       \<forall>a\<in>actors_graph (graphI I).
          \<forall>l. (\<exists>ya. (l, ya) \<in> gra (graphI I) \<or> (ya, l) \<in> gra (graphI I)) \<longrightarrow>
              (\<exists>x\<in>delta I (graphI I) l. case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor a)) \<Longrightarrow>
       a \<in> actors_graph (get_graph_a aa la m (graphI I)) \<Longrightarrow>
       (l, ya) \<in> gra (get_graph_a aa la m (graphI I)) \<or> (ya, l) \<in> gra (get_graph_a aa la m (graphI I)) \<Longrightarrow>
       y = I \<Longrightarrow>
       z = Infrastructure (get_graph_a aa la m (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       aa @\<^bsub>graphI I\<^esub> la \<Longrightarrow>
       la \<in> nodes (graphI I) \<Longrightarrow>
       I' = Infrastructure (get_graph_a aa la m (graphI I)) (delta I) \<Longrightarrow>
       x \<in> delta I (graphI I) la \<Longrightarrow>
       case x of (p, e) \<Rightarrow> get \<in> e \<and> p (Actor aa) \<Longrightarrow> x \<in> delta I (get_graph_a aa la m (graphI I)) l \<close>
    apply (simp add: get_graph_a_def init_state_policy local_policies_def actors_graph_def atI_def, erule exE)
    by (smt (z3) delta.simps empty_iff init_state_policy local_policies_def)
qed
qed
qed

lemma enables_move: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> a \<in> actors_graph (graphI y)
                   \<Longrightarrow> l \<in> nodes (graphI y) \<Longrightarrow>  enables y l (Actor a) move\<close>
  using enables_move0 by blast

lemma enables_get0: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           \<forall> a \<in> actors_graph (graphI y). \<forall> l \<in> nodes (graphI y). enables y l (Actor a) get\<close>
proof (erule rtrancl_induct)
  show \<open>\<forall>a\<in>actors_graph (graphI Ini). \<forall>l\<in>nodes (graphI Ini). enables Ini l (Actor a) get\<close>
    by (simp add: Ini_def enables_def ex_graph_def local_policies_def nodes_def)
next show \<open>\<And>y z. (Ini, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI y). \<forall>l\<in>nodes (graphI y). enables y l (Actor a) get \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI z). \<forall>l\<in>nodes (graphI z). enables z l (Actor a) get \<close>
    apply (clarify, simp add: Ini_def ex_graph_def local_policies_def  nodes_def enables_def
         E1_def N3_def SE1_def, erule exE)
    apply (erule state_transition_in.cases)
    apply (smt (z3) N3_def delta.simps gra.simps graphI.simps init_state_policy local_policies_def put put_graph_a_def same_actors0)
    apply (smt (z3) E1_def N3_def One_nat_def SE1_def delta.simps empty_iff eval eval_graph_a_def ex_graph_def gra.simps graphI.simps init_state_policy local_policies_def same_actors0)
     apply (simp add: enables_def)
    apply (erule bexE)
     apply (rule_tac x = x in bexI)
    apply (smt (z3) bex_empty case_prodI2 delta.simps fst_conv init_state_policy insert_iff local_policies_def snd_conv)
    apply (simp add: move_graph_a_def local_policies_def init_state_policy)
    apply (smt (z3) all_not_in_conv delta.simps init_state_policy local_policies_def)
     apply (simp add: enables_def)
    apply (erule bexE)
     apply (rule_tac x = x in bexI)
    apply (smt (z3) Pair_inject bex_empty case_prodE case_prodI2 delta.simps init_state_policy insertE local_policies_def)
    apply (simp add: get_graph_a_def local_policies_def init_state_policy)
proof -
fix yb :: infrastructure and z :: infrastructure and a :: "char list" and l :: location and ya :: location and G :: igraph and I :: infrastructure and aa :: "char list" and la :: location and I' :: infrastructure and m :: nat and x :: "(actor \<Rightarrow> bool) \<times> action set"
  assume a1: "G = graphI I"
  assume a2: "x \<in> delta I (graphI I) la"
  assume a3: "(l, ya) \<in> gra (graphI I) \<or> (ya, l) \<in> gra (graphI I)"
  assume a4: "\<forall>a\<in>actors_graph (graphI I). \<forall>l. (\<exists>y. (l, y) \<in> gra (graphI I) \<or> (y, l) \<in> gra (graphI I)) \<longrightarrow> (\<exists>x\<in>delta I (graphI I) l. case x of (p, e) \<Rightarrow> get \<in> e \<and> p (Actor a))"
  assume a5: "(Infrastructure (Lgraph {(Location 0, Location (Suc 0)), (Location 0, Location 2), (Location (Suc 0), Location 2)} ex_loc_ass ex_data black_box ex_requests) local_policies, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  assume a6: "a \<in> actors_graph (Lgraph (gra (graphI I)) (agra (graphI I)) ((dgra (graphI I)) (aa := (fst (dgra (graphI I) aa), fst (snd (dgra (graphI I) aa)), m, snd (snd (snd (dgra (graphI I) aa)))))) (bb (graphI I)) (requests (graphI I)))"
  assume "I' = Infrastructure (Lgraph (gra (graphI I)) (agra (graphI I)) ((dgra (graphI I)) (aa := (fst (dgra (graphI I) aa), fst (snd (dgra (graphI I) aa)), m, snd (snd (snd (dgra (graphI I) aa)))))) (bb (graphI I)) (requests (graphI I))) (delta I)"
  have f7: "a \<in> {cs. \<exists>l. l \<in> {l. \<exists>la. (l, la) \<in> gra G \<or> (la, l) \<in> gra G} \<and> cs \<in> agra G l}"
    using a6 a1 by (simp add: actors_graph_def nodes_def)
  have "\<forall>l cs. \<exists>p. \<forall>la lb. ((l, la) \<notin> gra (graphI I) \<or> cs \<notin> actors_graph (graphI I) \<or> p \<in> delta I (graphI I) l) \<and> ((lb, l) \<notin> gra (graphI I) \<or> cs \<notin> actors_graph (graphI I) \<or> p \<in> delta I (graphI I) l)"
    using a4 by blast
  then obtain pp :: "location \<Rightarrow> char list \<Rightarrow> (actor \<Rightarrow> bool) \<times> action set" where
    f8: "\<And>l la cs lb. ((l, la) \<notin> gra (graphI I) \<or> cs \<notin> actors_graph (graphI I) \<or> pp l cs \<in> delta I (graphI I) l) \<and> ((lb, l) \<notin> gra (graphI I) \<or> cs \<notin> actors_graph (graphI I) \<or> pp l cs \<in> delta I (graphI I) l)"
    by (metis (no_types))
  then have f9: "\<And>l la. (l, la) \<notin> gra G \<or> pp la a \<in> delta I G la"
    using f7 a1 actors_graph_def nodes_def by blast
  have "\<And>l la. (l, la) \<notin> gra G \<or> pp l a \<in> delta I G l"
    using f8 f7 a1 actors_graph_def nodes_def by blast
  then show "x \<in> delta I (Lgraph (gra (graphI I)) (agra (graphI I)) ((dgra (graphI I)) (aa := (fst (dgra (graphI I) aa), fst (snd (dgra (graphI I) aa)), m, snd (snd (snd (dgra (graphI I) aa)))))) (bb (graphI I)) (requests (graphI I))) l"
    using f9 a5 a3 a2 a1 by (smt (z3) delta.simps empty_iff init_state_policy local_policies_def)
qed
qed
  
lemma enables_get: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> a \<in> actors_graph (graphI y)
                   \<Longrightarrow> l \<in> nodes (graphI y) \<Longrightarrow>  enables y l (Actor a) get\<close>
  using enables_get0 by blast

lemma enables_put: \<open>(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> a \<in> actors_graph (graphI y)
                   \<Longrightarrow> l \<in> nodes (graphI y) \<Longrightarrow>  enables y l (Actor a) put\<close>
  sorry

lemma enables_eval: \<open>(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> a \<in> actors_graph (graphI y)
                   \<Longrightarrow> l \<in> nodes (graphI y) \<Longrightarrow>  enables y l (Actor a) eval\<close>
  sorry

lemma dgra_inv: \<open>(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
                   \<Longrightarrow> dgra (graphI I) = dgra (graphI y)\<close>
  sorry


lemma pc1_AG_OO: \<open>\<forall> A \<in> CreditScoring_actors. M \<turnstile> AG (EF {s. pc1 A s \<longrightarrow> DO A s})\<close>
proof (simp add: CreditScoring_actors_def M_def pc1_def Credit_Kripke_def check_def, rule conjI)
  show \<open>Ini \<in> Credit_states\<close>
    by (simp add: Credit_states_def state_transition_refl_def)
next show \<open>Ini \<in> AG (EF {s. 40000 \<le> salary ''Alice'' s \<and> ''Alice'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''Alice'' s}) \<and>
    Ini \<in> Credit_states \<and>
    Ini \<in> AG (EF {s. 40000 \<le> salary ''Bob'' s \<and> ''Bob'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''Bob'' s}) \<and>
    Ini \<in> Credit_states \<and> Ini \<in> AG (EF {s. 40000 \<le> salary ''CI'' s \<and> ''CI'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''CI'' s})\<close>
  proof
    show \<open>Ini \<in> AG (EF {s. 40000 \<le> salary ''Alice'' s \<and> ''Alice'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''Alice'' s})\<close>
    proof (unfold AG_def, simp add: gfp_def,
        rule_tac x = \<open>{s. s \<in> states(Credit_Kripke)}\<close> in exI,
        rule conjI)
      show \<open>{s. s \<in> states Credit_Kripke} \<subseteq> 
            EF {s. 40000 \<le> salary ''Alice'' s \<and> ''Alice'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''Alice'' s}\<close>
        apply (rule subsetI)
        apply (drule CollectD)
        apply (simp add: Credit_Kripke_def Credit_states_def)
        apply (subgoal_tac \<open>\<exists> l \<in> nodes (graphI x). ''Alice'' @\<^bsub> graphI x\<^esub> l\<close>)
         prefer 2
         apply (rule_tac I = Ini and y = x and l = SE1 in actor_has_location)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
           apply (simp add: actors_graph_def Ini_def nodes_def ex_graph_def ex_loc_ass_def SE1_def N3_def E1_def, force)
        apply (simp add: nodes_def Ini_def ex_graph_def SE1_def E1_def N3_def, blast)
         apply (simp add: Ini_def ex_graph_def ex_loc_ass_def atI_def SE1_def N3_def)
        apply (erule bexE)
        apply (rule_tac y = \<open>Infrastructure (
                             eval_graph_a ''Alice'' N3 (
                             put_graph_a ''Alice'' N3 (
                             get_graph_a ''Alice'' N3 40000 (
                             move_graph_a ''Alice'' l N3 (graphI x)))))
                             (delta x)\<close> in EF_step_star)
         prefer 2
         apply (simp add: eval_graph_a_def put_graph_a_def get_graph_a_def move_graph_a_def DO_def 
               salary_def N3_def same_bb)
         apply (subgoal_tac \<open>bb (graphI x) = bb(graphI Ini)\<close>)
        apply (subgoal_tac \<open>bb (graphI x) = black_box\<close>)
        apply (simp add: black_box_def)
        apply (smt (z3) N3_def fst_conv order_refl snd_conv)
        using Ini_def bb.simps ex_graph_def graphI.simps apply presburger
         apply (rule sym, rule same_bb)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
(* *)
        apply (subgoal_tac \<open>x \<rightarrow>\<^sub>i* Infrastructure (move_graph_a ''Alice'' l N3 (graphI x))(delta x)\<close>)
        apply (subgoal_tac \<open>Infrastructure (move_graph_a ''Alice'' l N3 (graphI x))(delta x) \<rightarrow>\<^sub>i*
                            Infrastructure (get_graph_a ''Alice'' N3 40000 (
                                            move_graph_a ''Alice'' l N3 (graphI x)))(delta x)\<close>)
        apply (subgoal_tac \<open>Infrastructure (get_graph_a ''Alice'' N3 40000 (
                                            move_graph_a ''Alice'' l N3 (graphI x)))(delta x) \<rightarrow>\<^sub>i*
                            Infrastructure (put_graph_a ''Alice'' N3 (
                                            (get_graph_a ''Alice'' N3 40000 (
                                            move_graph_a ''Alice'' l N3 (graphI x)))))(delta x)\<close>)
        apply (subgoal_tac \<open> Infrastructure (put_graph_a ''Alice'' N3 (
                                            (get_graph_a ''Alice'' N3 40000 (
                                            move_graph_a ''Alice'' l N3 (graphI x)))))(delta x)\<rightarrow>\<^sub>i*
                             Infrastructure (eval_graph_a ''Alice'' N3 (
                                            (put_graph_a ''Alice'' N3 (
                                            (get_graph_a ''Alice'' N3 40000 (
                                            move_graph_a ''Alice'' l N3 (graphI x)))))))(delta x)\<close>)
            apply (simp add: state_transition_infra_def state_transition_refl_def)    
           prefer 4
        apply (rule step_rtrancl)
           apply (rule_tac G = \<open>graphI x\<close> and a = \<open>''Alice''\<close> and l = l and l' = N3 in state_transition_in.move)
        apply (rule refl)
                apply assumption
               apply assumption
              apply (subst same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
        apply (simp add: same_nodes Ini_def ex_graph_def nodes_def, blast)
             apply (simp add: actors_graph_def atI_def, blast)
        apply (rule enables_move)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
              apply (simp add: actors_graph_def atI_def, force)
              apply (subst same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
            apply (simp add: same_nodes Ini_def ex_graph_def nodes_def, blast)
           apply (rule refl)
(* 3 *)
          prefer 3
        apply (rule step_rtrancl)
        apply (rule_tac G = \<open>(move_graph_a ''Alice'' l N3 (graphI x))\<close> and a = \<open>''Alice''\<close> and
                        l = N3 in state_transition_in.get)
              apply simp
             apply (simp add: atI_def move_graph_a_def)
         apply (smt (verit, ccfv_SIG) CollectI Collect_cong Ini_def ex_graph_def gra.simps graphI.simps insertCI nodes_def same_nodes split_cong state_transition_infra_def state_transition_refl_def)
           apply (rule enables_get)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
        apply (smt (verit, best) Alice_Bob_in_Credit_Kripke CollectI Collect_cong Credit_Kripke_def Credit_states_def insertCI same_actors split_cong state_transition_infra_def state_transition_refl_def states.simps)
        apply (smt (verit, ccfv_SIG) CollectI Collect_cong Ini_def ex_graph_def gra.simps graphI.simps insertCI nodes_def same_nodes split_cong state_transition_infra_def state_transition_refl_def)
          apply (subgoal_tac \<open>(delta (Infrastructure (move_graph_a ''Alice'' l N3 (graphI x)) (delta x))) = delta x\<close>)
        apply simp
        using delta.simps apply blast
(* 2 *)
         prefer 2
        apply (rule step_rtrancl)
        apply (rule_tac G = \<open>(get_graph_a ''Alice'' N3 40000 (move_graph_a ''Alice'' l N3 (graphI x)))\<close> and
                        a = \<open>''Alice''\<close> and l = \<open>N3\<close> in state_transition_in.put)
             apply simp
             apply (simp add: atI_def move_graph_a_def get_graph_a_def)
        apply (smt (verit, ccfv_SIG) CollectI Collect_cong Ini_def ex_graph_def gra.simps graphI.simps insertCI nodes_def same_nodes split_cong state_transition_infra_def state_transition_refl_def)
          apply (rule enables_put)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
        apply (smt (verit, ccfv_SIG) Alice_Bob_in_Credit_Kripke CollectI Collect_cong Credit_Kripke_def Credit_states_def insertCI same_actors split_cong state_transition_infra_def state_transition_refl_def states.simps)
        apply (smt (verit, ccfv_SIG) CollectI Collect_cong Ini_def ex_graph_def gra.simps graphI.simps insertCI nodes_def same_nodes split_cong state_transition_infra_def state_transition_refl_def)
        apply (subgoal_tac \<open>(delta (Infrastructure (get_graph_a ''Alice'' N3 40000 (move_graph_a ''Alice'' l N3 (graphI x))) (delta x))) = delta x\<close>)
          apply simp
        using delta.simps apply blast
(* *)
       apply (rule step_rtrancl)
        apply (rule_tac G = \<open>(put_graph_a ''Alice'' N3 (get_graph_a ''Alice'' N3 40000 (move_graph_a ''Alice'' l N3 (graphI x))))\<close>
                     and a = \<open>''Alice''\<close> and l = \<open>N3\<close> and c = \<open>''CI''\<close> in state_transition_in.eval)
            apply simp
             apply (simp add: atI_def move_graph_a_def get_graph_a_def put_graph_a_def)
        apply (smt (z3) CollectI Collect_cong Ini_def ex_graph_def gra.simps graphI.simps insertCI nodes_def same_nodes split_cong state_transition_infra_def state_transition_refl_def)
        apply (smt (z3) Alice_Bob_in_Credit_Kripke CollectI Collect_cong Credit_Kripke_def Credit_states_def graphI.simps insertCI same_actors split_cong state_transition_infra_def state_transition_refl_def states.simps)
           apply (simp add: actors_graph_def put_graph_a_def get_graph_a_def move_graph_a_def)
          apply (subgoal_tac \<open>dgra (graphI Ini) = dgra (graphI x)\<close>)
        apply (subgoal_tac \<open>Actor ''CI'' \<in> readers  (dgra (graphI x) ''Alice'')\<close>)
            apply (simp add: readers_def owner_def put_graph_a_def get_graph_a_def move_graph_a_def)
           apply (erule subst)
           apply (simp add: Ini_def ex_graph_def ex_data_def readers_def)
        apply (simp add: dgra_inv state_transition_infra_def state_transition_refl_def)
          apply (rule enables_eval)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
        apply (smt (z3) Alice_Bob_in_Credit_Kripke CollectI Collect_cong Credit_Kripke_def Credit_states_def insertCI same_actors split_cong state_transition_infra_def state_transition_refl_def states.simps)
        apply (smt (z3) CollectI Collect_cong Ini_def ex_graph_def gra.simps graphI.simps insertCI nodes_def same_nodes split_cong state_transition_infra_def state_transition_refl_def)
        apply (subgoal_tac \<open>(delta
              (Infrastructure
                (put_graph_a ''Alice'' N3 (get_graph_a ''Alice'' N3 40000 (move_graph_a ''Alice'' l N3 (graphI x))))
                (delta x))) = delta x\<close>)
         apply simp
        using delta.simps by blast
next show \<open>{s. s \<in> states Credit_Kripke} \<subseteq> AX {s. s \<in> states Credit_Kripke} \<and> Ini \<in> {s. s \<in> states Credit_Kripke}\<close>
  proof
  show \<open>Ini \<in> {s. s \<in> states Credit_Kripke}\<close>
    by (simp add: Credit_Kripke_def Credit_states_def state_transition_refl_def actors_graph_def)
next show \<open>{s. s \<in> states Credit_Kripke} \<subseteq> AX {s. s \<in> states Credit_Kripke} \<close>
    by (simp add: AX_def Collect_mono Credit_Kripke_def Credit_states_def rtrancl.intros(2) state_transition_refl_def)
qed
qed
next show \<open>Ini \<in> Credit_states \<and>
    Ini \<in> AG (EF {s. 40000 \<le> salary ''Bob'' s \<and> ''Bob'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''Bob'' s}) \<and>
    Ini \<in> Credit_states \<and> Ini \<in> AG (EF {s. 40000 \<le> salary ''CI'' s \<and> ''CI'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''CI'' s}) \<close>
  proof
    show \<open>Ini \<in> Credit_states \<close>
 by (simp add: Credit_states_def state_transition_refl_def)
next show \<open>Ini \<in> AG (EF {s. 40000 \<le> salary ''Bob'' s \<and> ''Bob'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''Bob'' s}) \<and>
    Ini \<in> Credit_states \<and> Ini \<in> AG (EF {s. 40000 \<le> salary ''CI'' s \<and> ''CI'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''CI'' s})\<close>
  proof 
    show \<open>Ini \<in> AG (EF {s. 40000 \<le> salary ''Bob'' s \<and> ''Bob'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''Bob'' s})\<close>
    proof (unfold AG_def, simp add: gfp_def,
        rule_tac x = \<open>{s. s \<in> states(Credit_Kripke)}\<close> in exI,
        rule conjI)
      show \<open>{s. s \<in> states Credit_Kripke} \<subseteq> 
            EF {s. 40000 \<le> salary ''Bob'' s \<and> ''Bob'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''Bob'' s}\<close> 
        sorry
    next show \<open>{s. s \<in> states Credit_Kripke} \<subseteq> AX {s. s \<in> states Credit_Kripke} \<and> Ini \<in> {s. s \<in> states Credit_Kripke}\<close>
      proof
        show \<open>{s. s \<in> states Credit_Kripke} \<subseteq> AX {s. s \<in> states Credit_Kripke}\<close>
    by (simp add: AX_def Collect_mono Credit_Kripke_def Credit_states_def rtrancl.intros(2) state_transition_refl_def)
next show \<open>Ini \<in> {s. s \<in> states Credit_Kripke}\<close>
    by (simp add: Credit_Kripke_def Credit_states_def state_transition_refl_def actors_graph_def)
qed
qed
next show \<open> Ini \<in> Credit_states \<and> Ini \<in> AG (EF {s. 40000 \<le> salary ''CI'' s \<and> ''CI'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''CI'' s})\<close>
  proof 
    show \<open> Ini \<in> Credit_states\<close>
    by (simp add: Credit_Kripke_def Credit_states_def state_transition_refl_def actors_graph_def)
next show \<open>Ini \<in> AG (EF {s. 40000 \<le> salary ''CI'' s \<and> ''CI'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''CI'' s}) \<close>
    proof (unfold AG_def, simp add: gfp_def,
        rule_tac x = \<open>{s. s \<in> states(Credit_Kripke)}\<close> in exI,
        rule conjI)
      show \<open> {s. s \<in> states Credit_Kripke} \<subseteq> EF {s. 40000 \<le> salary ''CI'' s \<and> ''CI'' @\<^bsub>graphI s\<^esub> N3 \<longrightarrow> DO ''CI'' s}\<close>
        sorry
    next show \<open>{s. s \<in> states Credit_Kripke} \<subseteq> AX {s. s \<in> states Credit_Kripke} \<and> Ini \<in> {s. s \<in> states Credit_Kripke}\<close>
      proof
        show \<open>{s. s \<in> states Credit_Kripke} \<subseteq> AX {s. s \<in> states Credit_Kripke}\<close>
    by (simp add: AX_def Collect_mono Credit_Kripke_def Credit_states_def rtrancl.intros(2) state_transition_refl_def)
next show \<open>Ini \<in> {s. s \<in> states Credit_Kripke} \<close>
    by (simp add: Credit_Kripke_def Credit_states_def state_transition_refl_def actors_graph_def)
qed
qed
qed
qed
qed
qed
qed

end
