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
                                         ex_loc_ass' ex_data'' black_box ex_requests'''"

(* Alice now puts in an application from N3 *)
fixes ex_graphV'''' :: "igraph"
defines ex_graphV''''_def: "ex_graphV'''' \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass' ex_data'' black_box ex_requests''''"

(* This time, CI evaluates to positive *)
fixes ex_graphX :: "igraph"
defines ex_graphX_def: "ex_graphX \<equiv> Lgraph {(N3,SE1),(N3,E1),(SE1,E1)} 
                                         ex_loc_ass' ex_data'' black_box ex_requestsV'"


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
next show \<open>C =
    Infrastructure
     (Lgraph (gra (graphI Ini)) (agra (graphI Ini)) (dgra (graphI Ini)) (bb (graphI Ini))
       (insert (''Bob'', None) (requests (graphI Ini))))
     (delta Ini)\<close>
    using C_def Ini_def agra.simps bb.simps delta.simps dgra.simps ex_graph'_def ex_graph_def ex_requests'_def ex_requests_def gra.simps graphI.simps requests.simps by presburger
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

lemma stepI_Ca: "Ini  \<rightarrow>\<^sub>n Ca"
proof (rule_tac l = N3 and a = "''Bob''" and m = "40000" in get)
  show "graphI Ini = graphI Ini" by (rule refl)
next show "''Bob'' @\<^bsub>graphI Ini\<^esub> N3"
    by (simp add: Ini_def atI_def ex_graph_def ex_loc_ass_def) 
next show \<open>N3 \<in> nodes (graphI Ini)\<close>
    using Ini_def ex_graph_def nodes_def by auto
next show \<open>enables Ini N3 (Actor ''Bob'') get\<close>
    by (simp add: Ini_def enables_def local_policies_def)
next show \<open>Ca =
    Infrastructure
     (Lgraph (gra (graphI Ini)) (agra (graphI Ini))
       ((dgra (graphI Ini))
        (''Bob'' :=
           (fst (dgra (graphI Ini) ''Bob''), fst (snd (dgra (graphI Ini) ''Bob'')), 40000,
            snd (snd (snd (dgra (graphI Ini) ''Bob''))))))
       (bb (graphI Ini)) (requests (graphI Ini)))
     (delta Ini) \<close>
    apply (simp add: Ini_def Ca_def ex_graph_def ex_graph'''_def ex_data_def ex_data'_def)
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
next show \<open>CCa =
    Infrastructure
     (Lgraph (gra (graphI Ca)) (agra (graphI Ca)) (dgra (graphI Ca)) (bb (graphI Ca))
       (insert (''Bob'', None) (requests (graphI Ca))))
     (delta Ca)\<close>
    by (simp add: CCa_def Ca_def ex_graph''''_def ex_graph'''_def ex_requests'_def ex_requests_def)
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
    by (simp add: CCa_def ex_graph''''_def ex_requests'_def)
next show \<open> ((Actor ''Bob'',{Actor ''CI''}),(N3, 40000, 1968, white)) = dgra (graphI CCa) ''Bob''\<close>
    by (simp add: CCa_def ex_graph''''_def ex_data'_def)
next show \<open>Actor ''CI'' \<in> snd (Actor ''Bob'', {Actor ''CI''})\<close>
    by force
next show \<open>enables CCa N3 (Actor ''CI'') eval\<close>
    by (simp add: CCa_def enables_def local_policies_def)
next show \<open>CCCa =
    Infrastructure
     (Lgraph (gra (graphI CCa)) (agra (graphI CCa)) (dgra (graphI CCa)) (bb (graphI CCa))
       (insert (''Bob'', Some (bb (graphI CCa) (N3, 40000, 1968, white))) (requests (graphI CCa) - {(''Bob'', None)})))
     (delta CCa) \<close>
    by (simp add: CCCa_def ex_graphV_def CCa_def ex_graph''''_def ex_requests'''_def black_box_def ex_requests'_def)
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
next show \<open>Cb =
    Infrastructure
     (Lgraph (gra (graphI CCCa)) (agra (graphI CCCa)) (dgra (graphI CCCa)) (bb (graphI CCCa))
       (insert (''Alice'', None) (requests (graphI CCCa))))
     (delta CCCa) \<close>
    by (simp add: CCCa_def Cb_def ex_graphV'_def ex_graphV_def ex_requests''''_def ex_requests'''_def)
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
next show \<open>((Actor ''Alice'',{Actor ''CI''}),(SE1, 40000,1982, black)) = dgra (graphI Cb) ''Alice''\<close>
    by (simp add: Cb_def ex_graphV'_def ex_data'_def)
next show \<open>Actor ''CI'' \<in> snd (Actor ''Alice'', {Actor ''CI''})\<close>
    by force
next show \<open>enables Cb SE1 (Actor ''CI'') eval\<close>
    by (simp add: Cb_def enables_def local_policies_def) 
next show \<open>CCb =
    Infrastructure
     (Lgraph (gra (graphI Cb)) (agra (graphI Cb)) (dgra (graphI Cb)) (bb (graphI Cb))
       (insert (''Alice'', Some (bb (graphI Cb) (SE1, 40000, 1982, black)))
         (requests (graphI Cb) - {(''Alice'', None)})))
     (delta Cb) \<close>
    by (simp add: CCb_def ex_graphV''_def Cb_def ex_graphV'_def ex_requestsV_def ex_requests''''_def
                     black_box_def SE1_def N3_def)
qed

lemma stepCCCa_Cc: "CCCa  \<rightarrow>\<^sub>n Cc"
proof (rule_tac l = SE1 and l' = N3 and a = "''Alice''"  in move)
  show \<open>graphI CCCa = graphI CCCa\<close> by (rule refl)
next show \<open>''Alice'' @\<^bsub>graphI CCCa\<^esub> SE1\<close>
    by (simp add: CCCa_def N3_def SE1_def atI_def ex_graphV_def ex_loc_ass_def)
next show \<open>SE1 \<in> nodes (graphI CCCa)\<close>
    using CCCa_def ex_graphV_def nodes_def by auto
next show \<open>N3 \<in> nodes (graphI CCCa)\<close>
    using CCCa_def ex_graphV_def nodes_def by auto
next show \<open>''Alice'' \<in> actors_graph (graphI CCCa)\<close>
    apply (simp add: actors_graph_def)
    by (smt (verit, ccfv_SIG) CCCa_def N3_def One_nat_def SE1_def Zero_not_Suc agra.simps ex_graphV_def ex_loc_ass_def gra.simps graphI.simps insertI1 location.inject mem_Collect_eq nodes_def)
next show \<open>enables CCCa N3 (Actor ''Alice'') move\<close>
    by (simp add: CCCa_def enables_def local_policies_def)
next show \<open>Cc = Infrastructure (move_graph_a ''Alice'' SE1 N3 (graphI CCCa)) (delta CCCa)\<close>
    apply (simp add: move_graph_a_def Cc_def ex_graphV'''_def CCCa_def ex_graphV_def ex_loc_ass_def
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
next show \<open> CCc =
    Infrastructure
     (Lgraph (gra (graphI Cc)) (agra (graphI Cc)) (dgra (graphI Cc)) (bb (graphI Cc))
       (insert (''Alice'', None) (requests (graphI Cc))))
     (delta Cc) \<close>
    by (simp add: CCc_def ex_graphV''''_def ex_loc_ass'_def Cc_def ex_graphV'''_def ex_requests'''_def
                     ex_requests''''_def)
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
    by (simp add: CCc_def ex_graphV''''_def ex_requests''''_def)
next show \<open>((Actor ''Alice'',{Actor ''CI''}),(N3, 40000,1982, black)) = dgra (graphI CCc) ''Alice''\<close>
    by (simp add: CCc_def ex_graphV''''_def ex_data''_def)
next show \<open> Actor ''CI'' \<in> snd (Actor ''Alice'', {Actor ''CI''})\<close> by simp
next show \<open>enables CCc N3 (Actor ''CI'') eval\<close>
    by (simp add: CCc_def enables_def local_policies_def)
next show \<open>CCCc =
    Infrastructure
     (Lgraph (gra (graphI CCc)) (agra (graphI CCc)) (dgra (graphI CCc)) (bb (graphI CCc))
       (insert (''Alice'', Some (bb (graphI CCc) (N3, 40000, 1982, black)))
         (requests (graphI CCc) - {(''Alice'', None)})))
     (delta CCc)\<close>
    by (simp add: CCCc_def ex_graphX_def CCc_def ex_graphV''''_def ex_requestsV'_def ex_requests''''_def
                     black_box_def)
qed
end
