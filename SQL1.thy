theory SQL1
  imports Main
begin



datatype s_type = ST_String | ST_Int | ST_Date

datatype s_rowname = SRN_String string

datatype s_value = SV_String string | SV_Int int | SV_Null

datatype s_schema = SS_Schema "(s_rowname * s_type) list"

datatype s_select_argument = SSA_Rowname s_rowname | SSA_Star

datatype s_table_name = STN_String string

datatype s_from_argument = SFA_Table_Name s_table_name

datatype s_where_argument = SWA_AND s_where_argument s_where_argument | SWA_ISNULL s_rowname | SWA_Empty

datatype s_group_by = SGB_Empty

datatype s_row = SS_Row "(s_select_argument * s_value) list"

datatype s_query_result = SQR "s_row list"

datatype s_query = SQ "s_select_argument list" 


datatype s_table = ST "s_table_name * s_schema * ((s_rowname * s_value) list)"

datatype s_insert_query = SIQ "(s_rowname * s_value) list"

datatype s_database = SD "s_table list"

fun test_schema :: "unit \<Rightarrow> s_schema" where
"test_schema _ = SS_Schema []"

value "test_schema ()"

inductive s_value_correct :: "s_value \<Rightarrow> s_type \<Rightarrow> bool" where
svc_string : "s_value_correct (SV_String x) ST_String"

inductive s_schema_correct :: "s_schema \<Rightarrow> s_insert_query \<Rightarrow> bool" where
ssc_empty : "s_schema_correct (SS_Schema []) (SIQ [])" |
ssc_cons : "s_schema_correct (SS_Schema x) (SIQ y) \<Longrightarrow> s_value_correct v t \<Longrightarrow> s_schema_correct (SS_Schema ((rn, t) # x)) (SIQ ((rn, v) # y))"

value "svc_string"
(*inductive s_schema_correct :: *)

fun is_value_correct :: "s_value \<Rightarrow> s_type \<Rightarrow> bool" where
"is_value_correct (SV_String _) (ST_String) = True" |
"is_value_correct _ _ = False"

fun pop_from_map :: "s_rowname \<Rightarrow> (s_rowname * 'a) list \<Rightarrow> (( (s_rowname * 'a) list) * (s_rowname * 'a)) option" where
"pop_from_map _ [] = None" |
"pop_from_map (SRN_String s1) (((SRN_String s2), a) # xs) = (case s1 = s2 of
  True \<Rightarrow> Some (xs, (SRN_String s1, a)) |
  False \<Rightarrow> (case pop_from_map (SRN_String s1) xs of
    Some (xs', v) \<Rightarrow> Some (((SRN_String s2), a) # xs', v) |
    None \<Rightarrow> None))"

(*lemma pop_smaller : "pop_from_map x y = Some (y', t) \<Longrightarrow> length y' < length y"
  apply(induction y)
  apply(auto)
  done
*)

fun is_insert_query_correct :: "s_schema \<Rightarrow> s_insert_query \<Rightarrow> bool" where
"is_insert_query_correct (SS_Schema []) (SIQ []) = True" |
"is_insert_query_correct (SS_Schema (x # xs)) (SIQ []) = False"|
"is_insert_query_correct (SS_Schema y) (SIQ ((rn, v) # rest)) = (case pop_from_map rn y of
  Some ((y', (rn', t))) \<Rightarrow> (is_value_correct v t \<and> is_insert_query_correct (SS_Schema y') (SIQ rest)) |
  None \<Rightarrow> False)"
by  auto
termination by (relation "measures [\<lambda>(i, N). N, \<lambda>(i,N). N + 1 - i]") auto

fun insert :: "s_insert_query \<Rightarrow> s_table \<Rightarrow> s_table option" where 
"insert (SIQ "

fun test :: "unit \<Rightarrow> (string \<rightharpoonup>  int)" where
"test _ = empty(''a'' \<mapsto>1)"

value "test () ''a''"
end 