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

end
