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

fixes ex_requests''':: \<open>(identity \<times> bool option)set\<close>
defines ex_requests'''_def: \<open>ex_requests''' \<equiv> {(''Bob'', Some(True))}\<close>

fixes ex_requests'''':: \<open>(identity \<times> bool option)set\<close>
defines ex_requests''''_def: \<open>ex_requests'''' \<equiv> {(''Alice'', None),(''Bob'', Some(True))}\<close>

fixes ex_requestsV:: \<open>(identity \<times> bool option)set\<close>
defines ex_requestsV_def: \<open>ex_requestsV \<equiv> {(''Alice'', Some(False)),(''Bob'', Some(True))}\<close>

fixes ex_requestsV':: \<open>(identity \<times> bool option)set\<close>
defines ex_requestsV'_def: \<open>ex_requestsV' \<equiv> {(''Alice'', Some(True)),(''Bob'', Some(True))}\<close>

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


(* Another possibility from initial state I 
   Bob first actions a get to get a salary increase *)
fixes ex_graph''' :: "igraph"
defines ex_graph'''_def: "ex_graph''' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data' black_box ex_requests"


(* Bob puts in a credit application *)
fixes ex_graph'''' :: "igraph"
defines ex_graph''''_def: "ex_graph'''' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data' black_box ex_requests'"


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

(* In an alternative run, Alice moves to N3 first *)
fixes ex_graphV''' :: "igraph"
defines ex_graphV'''_def: "ex_graphV''' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data'' black_box ex_requests'''"

(* Alice now puts in an application from N3 *)
fixes ex_graphV'''' :: "igraph"
defines ex_graphV''''_def: "ex_graphV'''' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data'' black_box ex_requests''''"

(* This time, CI evaluates to positive *)
fixes ex_graphX :: "igraph"
defines ex_graphX_def: "ex_graphX \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass ex_data'' black_box ex_requestsV'"


fixes local_policies :: "[igraph, location] \<Rightarrow> policy set"
defines local_policies_def: "local_policies G \<equiv> 
    (\<lambda> x. if x = N3 then  {(\<lambda> y. True, {get,move,put,eval})}
          else (if x = SE1 then {(\<lambda> y. True, {get,move,put,eval})} 
                else (if x = E1 then {(\<lambda> y. True, {get,move,put,eval})} 
                      else {})))"

(* scenario states *)
fixes Ini :: \<open>infrastructure\<close>
defines Ini: \<open>Ini \<equiv> Infrastructure ex_graph local_policies\<close>

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

begin 

lemma stepI_C: "Ini  \<rightarrow>\<^sub>n C"
proof (rule_tac l = N3 and a = "''Bob''" in put)
  show "graphI Ini = graphI Ini" by (rule refl)
next show "''Bob'' @\<^bsub>graphI Ini\<^esub> N3"
    by (simp add: Ini atI_def ex_graph_def ex_loc_ass_def)
next show "N3 \<in> nodes (graphI Ini)"
    using Ini ex_graph_def nodes_def by auto
next show \<open>enables Ini N3 (Actor ''Bob'') put\<close>
    by (simp add: Ini enables_def local_policies_def)
next show \<open>C =
    Infrastructure
     (Lgraph (gra (graphI Ini)) (agra (graphI Ini)) (dgra (graphI Ini)) (bb (graphI Ini))
       (insert (''Bob'', None) (requests (graphI Ini))))
     (delta Ini)\<close>
    using C_def Ini agra.simps bb.simps delta.simps dgra.simps ex_graph'_def ex_graph_def ex_requests'_def ex_requests_def gra.simps graphI.simps requests.simps by presburger
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
next show " ((Actor ''Bob'',{Actor ''CI''}),(N3, 35000, 1968, white)) = dgra (graphI C) ''Bob''"
    by (simp add: C_def ex_graph'_def ex_data_def)
next show \<open> Actor ''CI'' \<in> snd (Actor ''Bob'', {Actor ''CI''})\<close>
    by fastforce
next show \<open>enables C N3 (Actor ''CI'') eval\<close>
    by (simp add: C_def enables_def local_policies_def)
next show "CC =
    Infrastructure
     (Lgraph (gra (graphI C)) (agra (graphI C)) (dgra (graphI C)) (bb (graphI C))
       (insert (''Bob'', Some (bb (graphI C) (N3, 35000, 1968, white))) (requests (graphI C) - {(''Bob'', None)})))
     (delta C)"
    by (simp add: C_def CC_def ex_graph'_def ex_graph''_def black_box_def ex_requests''_def ex_requests'_def)
qed

end
