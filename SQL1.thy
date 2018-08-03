theory SQL1
  imports Main "~~/src/HOL/Library/Finite_Map"
begin



datatype s_type = ST_String | ST_Int | ST_Date

type_synonym s_rowname = string

datatype s_value = SV_String string | SV_Int int | SV_Null

datatype s_schema = SS_Schema "(s_rowname, s_type) fmap"

datatype s_select_argument = SSA_Rowname s_rowname | SSA_Star

datatype s_table_name = STN_String string

datatype s_from_argument = SFA_Table_Name s_table_name

datatype s_where_argument = SWA_AND s_where_argument s_where_argument | SWA_ISNULL s_rowname | SWA_Empty

datatype s_group_by = SGB_Empty

datatype s_row = SS_Row "(s_select_argument, s_value) fmap"

datatype s_query_result = SQR_Success "s_row list" | SQR_Error string

datatype s_query = SQ "s_select_argument list" s_from_argument s_where_argument s_group_by


record s_table = 
  table_name :: s_table_name
  schema :: s_schema 
  vals :: "(((s_rowname, s_value) fmap) list)"

datatype s_insert_query = SIQ "(s_rowname, s_value) fmap"

datatype s_database = SD "(s_table_name, s_table) fmap"

fun test_schema :: "unit \<Rightarrow> s_schema" where
"test_schema _ = SS_Schema (
  fmap_of_list 
    [ (''id'', ST_Int)
    , (''name'', ST_String)
    ]
)"

fun test_table :: "unit \<Rightarrow> s_table" where
"test_table _ = 
  \<lparr> table_name = STN_String ''test_table''
  , schema = test_schema ()
  , vals = []
  \<rparr>
" 

fun test_db :: "unit \<Rightarrow> s_database" where 
"test_db _ = SD (fmap_of_list [(STN_String ''test_table'', test_table ())])"

value "SR_String ''a'' = SR_String ''b''"
value "(case (test_schema ()) of 
  SS_Schema x \<Rightarrow> fmdom x)"


fun is_value_correct :: "s_value \<Rightarrow> s_type \<Rightarrow> bool" where
"is_value_correct (SV_String _) (ST_String) = True" |
"is_value_correct (SV_Int _) (ST_Int) = True" |
"is_value_correct (SV_Null) _ = True" |
"is_value_correct _ _ = False"


fun is_insert_query_correct_helper :: "s_schema \<Rightarrow> (s_rowname \<times> s_value) \<Rightarrow> bool" where
"is_insert_query_correct_helper (SS_Schema sch) (rowname, value) = (
  case fmlookup sch rowname of 
    Some type_ \<Rightarrow> is_value_correct value type_ |
    Empty \<Rightarrow> False
)"

fun is_insert_query_correct :: "s_schema \<Rightarrow> s_insert_query \<Rightarrow> bool" where
"is_insert_query_correct (SS_Schema sch) (SIQ iq) = (
  let iq_set = fset_of_fmap iq; 
      iq_dom = fmdom iq;
      sch_dom = fmdom sch
  in
  fBall iq_set (is_insert_query_correct_helper (SS_Schema sch))
  \<and> (HOL.equal iq_dom sch_dom)
)"

(*lemma is_insert_query_correct_same_no_of_args : "
  is_insert_query_correct 
    (SS_Schema (fmap_of_list [ (SR_String rn, t) ] )) 
    (SIQ (fmap_of_list [ (SR_String rn, SV_Null) ])) 
  = True" 
  apply(induction t)
  apply(auto)
  done *)
fun test_insert_query :: "unit \<Rightarrow> s_insert_query" where 
"test_insert_query _ = SIQ (
  fmap_of_list []
)"

value "is_insert_query_correct_helper (SS_Schema (fmap_of_list []))"

value "fBall (fset_of_list [True, False, True]) (\<lambda>x. x)"

fun insert_to_table :: "s_insert_query \<Rightarrow> s_table \<Rightarrow> s_table option" where 
"insert_to_table (SIQ iq) table = (
  case is_insert_query_correct (schema table) (SIQ iq) of
    False \<Rightarrow> None |
    True \<Rightarrow> Some (table \<lparr> vals := (iq # (vals table)) \<rparr>)
)"

value "insert_to_table (test_insert_query ()) (test_table ())"

fun select :: "s_query \<Rightarrow> s_database \<Rightarrow> s_query_result" where
"select (SQ args from where groupby) (SD tables) = SQR_Error ''test2'' "

end 