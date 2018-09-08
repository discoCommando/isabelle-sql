theory SQL1
  imports Main "~~/src/HOL/Library/Finite_Map"
begin



datatype s_type 
  = ST_String 
  | ST_Int 
  | ST_Date

type_synonym s_rowname = string

datatype s_value 
  = SV_String string 
  | SV_Int int 
  | SV_Null

fun s_value_eq :: "s_value \<Rightarrow> s_value \<Rightarrow> bool" where
"s_value_eq (SV_String s1) (SV_String s2) = (s1 = s2)" |
"s_value_eq (SV_Int i1) (SV_Int i2) = (i1 = i2)" |
"s_value_eq (SV_Null) (SV_Null) = True" |
"s_value_eq _ _ = False"

datatype s_schema 
  = SS_Schema "(s_rowname, s_type) fmap"

datatype s_tbl_name 
  = STN_String string

datatype s_select_argument 
  = SSA_Rowname s_rowname 
  | SSA_Tablerowname s_tbl_name s_rowname 
  | SSA_Star


fun show_table_name :: "s_tbl_name \<Rightarrow> string" where 
  "show_table_name (STN_String s) = s"

datatype s_lr_join_type 
  = SLJT_Left
  | SLJT_Right
datatype 
  s_join_condition 
    = SJC_Using "s_rowname list"
datatype 
  s_table_factor 
    = STF_Single s_tbl_name 
    | STF_Multiple "s_table_reference list"
and
  s_join_table 
    = SJT_Join s_table_reference s_table_factor "s_join_condition list" (* for now it is inner join *) 
    | SJT_LR_Join s_table_reference s_lr_join_type s_table_reference s_join_condition
    | SJT_Nat_Join s_table_reference s_table_factor
and 
  s_table_reference 
    = SFA_Table_Factor s_table_factor 
    | SFA_Join_Table s_join_table 


fun get_tbl_names_from_tf :: "s_table_factor \<Rightarrow> s_tbl_name list"
and get_tbl_names_from_tr :: "s_table_reference \<Rightarrow> s_tbl_name list" where 
"get_tbl_names_from_tf (STF_Single x) = [x]" |
"get_tbl_names_from_tf (STF_Multiple []) = []" |
"get_tbl_names_from_tf (STF_Multiple (x#xs)) = 
  (get_tbl_names_from_tr x) @ get_tbl_names_from_tr (SFA_Table_Factor (STF_Multiple xs))" |

"get_tbl_names_from_tr (SFA_Table_Factor tf) = get_tbl_names_from_tf tf" | 
"get_tbl_names_from_tr (SFA_Join_Table (SJT_Join tr tf _)) = 
  get_tbl_names_from_tr tr @ get_tbl_names_from_tf tf" | 
"get_tbl_names_from_tr (SFA_Join_Table (SJT_LR_Join tr1 _ tr2 _)) = 
  get_tbl_names_from_tr tr1 @ get_tbl_names_from_tr tr2" |
"get_tbl_names_from_tr (SFA_Join_Table (SJT_Nat_Join tr tf)) = 
  get_tbl_names_from_tr tr @ get_tbl_names_from_tf tf"



datatype s_where_argument = SWA_AND s_where_argument s_where_argument | SWA_ISNULL s_rowname | SWA_Empty

datatype s_group_by = SGB_Empty

datatype s_row = SS_Row "(s_select_argument, s_value) fmap"

datatype s_query_result = SQR_Success "s_row list" | SQR_Error string

datatype s_query = SQ "s_select_argument list" s_table_reference s_where_argument s_group_by

datatype 'a option_err = Error string | Ok 'a 

type_synonym vals =  "(((s_rowname, s_value) fmap) list)"

type_synonym s_join_result = "((s_tbl_name \<times> s_rowname \<times> s_value) list) list"

record s_table = 
  tbl_name :: s_tbl_name
  schema :: s_schema 
  vals :: vals

datatype s_insert_query = SIQ "(s_rowname, s_value) fmap"

datatype s_database = SD "(s_tbl_name, s_table) fmap"

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


fun is_insert_query_correct_helper :: "s_schema \<Rightarrow> s_rowname \<Rightarrow> s_value \<Rightarrow> bool" where
"is_insert_query_correct_helper (SS_Schema sch) rowname value = (
  case fmlookup sch rowname of 
    Some type_ \<Rightarrow> is_value_correct value type_ |
    Empty \<Rightarrow> False
)"

fun is_insert_query_correct :: "s_schema \<Rightarrow> s_insert_query \<Rightarrow> bool" where
"is_insert_query_correct (SS_Schema sch) (SIQ iq) = (
  let 
      iq_dom = fmdom iq;
      sch_dom = fmdom sch
  in
  fmpred (is_insert_query_correct_helper (SS_Schema sch)) iq
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
  fmap_of_list [(''id'', SV_Int 10), (''name'', SV_String ''Test'')]
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

fun check_schema_for_select_arguments :: "s_schema \<Rightarrow> s_select_argument list \<Rightarrow> string option" where 
"check_schema_for_select_arguments (SS_Schema sch) (arg # args) = (
  case check_schema_for_select_arguments (SS_Schema sch) args of 
    Some err \<Rightarrow> Some err |
    None \<Rightarrow> (
      case arg of 
        SSA_Star \<Rightarrow> None |
        SSA_Rowname rowname \<Rightarrow> (
          case fmlookup sch rowname of 
            None \<Rightarrow> Some (''Unknown column \"''  @ rowname @ ''\" in \"field list\"'') |
            Some x \<Rightarrow> None
        )
    )
)" | 
"check_schema_for_select_arguments (SS_Schema sch) [] = None" 

fun table_names_unique :: "s_tbl_name list \<Rightarrow> bool" where 
"table_names_unique list = distinct (map show_table_name list)"

fun find_in_row :: "s_rowname \<Rightarrow> (s_tbl_name \<times> s_rowname \<times> s_value) list  \<Rightarrow> (s_tbl_name \<times> s_rowname \<times> s_value) option" where 
"find_in_row rn [] = None" |
"find_in_row rn1 ((tbl_nm, rn2, v)#xs) = (
  case (rn1 = rn2) of 
    True \<Rightarrow> Some (tbl_nm, rn2, v) |
    False \<Rightarrow> find_in_row rn2 xs
)"

fun inner_join_using :: "s_rowname list \<Rightarrow> (s_tbl_name \<times> s_rowname \<times> s_value) list \<Rightarrow> (s_tbl_name \<times> s_rowname \<times> s_value) list \<Rightarrow> bool option_err" where
"inner_join_using [] _ _ = Error ''Empty 'using' list ''" |
"inner_join_using (x#xs) l r = (
  case (find_in_row x l, find_in_row x r) of 
    (Some (tbl_nm1, rn1, v1), Some (tbl_nm2, rn2, v2)) \<Rightarrow> (
      case s_value_eq v1 v2 of 
        False \<Rightarrow> Ok False |
        True \<Rightarrow> (
          case xs of 
            [] \<Rightarrow> Ok True |
            _ \<Rightarrow> inner_join_using xs l r
        )
    )
)"

fun inner_join_try :: "s_join_condition list \<Rightarrow> (s_tbl_name \<times> s_rowname \<times> s_value) list \<Rightarrow> (s_tbl_name \<times> s_rowname \<times> s_value) list \<Rightarrow> bool option_err" where 
"inner_join_try [] _ _ = Error ''Empty join condition list''" |
"inner_join_try ((SJC_Using rnl)#xs) l r = (
  case inner_join_using rnl l r of 
    Error x \<Rightarrow> Error x |
    Ok False \<Rightarrow> Ok False |
    Ok True \<Rightarrow> (
      case xs of 
        [] \<Rightarrow> Ok True |
        _ \<Rightarrow> inner_join_try xs l r
    )
)"

fun inner_join_single_row :: "s_join_condition list \<Rightarrow> (s_tbl_name \<times> s_rowname \<times> s_value) list \<Rightarrow> s_join_result \<Rightarrow> s_join_result option_err" where 
"inner_join_single_row conds left_row [] = Ok []" |
"inner_join_single_row conds left_row (r#rs) = (
  case inner_join_try conds left_row r of 
    Error x \<Rightarrow> Error x |
    Ok can_join \<Rightarrow> (
      case inner_join_single_row conds left_row rs of 
        Error x \<Rightarrow> Error x |
        Ok join_res \<Rightarrow> (
          case can_join of 
            True \<Rightarrow> Ok ((left_row @ r) # join_res) |
            False \<Rightarrow> Ok join_res
        )
    )
)"

fun inner_join :: "s_join_condition list \<Rightarrow> s_join_result \<Rightarrow> s_join_result \<Rightarrow> s_join_result option_err" where
"inner_join conds [] _ = Ok []" | 
"inner_join conds (l#ls) rs = (
  case inner_join_single_row conds l rs of 
    Error x \<Rightarrow> Error x |
    Ok join_res \<Rightarrow> (
      case inner_join conds ls rs of 
        Error x \<Rightarrow> Error x |
        Ok join_res2 \<Rightarrow> Ok (join_res @ join_res2)
    )
)"


definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. set l = s)"

lemma  set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)


fun list_of_fmap :: "('a, 'b) fmap \<Rightarrow> ('a \<times> 'b) list" where
"list_of_fmap x = set_to_list (fset_of_fmap x)"


value "fset_of_fmap (fmap_of_list 
    [ (''id'', ST_Int)
    , (''name'', ST_String)
    ])"

fun resolve_single_table :: "s_tbl_name \<Rightarrow> s_database \<Rightarrow> s_join_result option_err" where
"resolve_single_table tbl_nm (SD tables) = (
  case fmlookup tables tbl_nm of
    None \<Rightarrow> Error (''Unknown table '' @ (show_table_name tbl_nm) @ '' in database '') |
    Some table \<Rightarrow> ( 
      let 
        result = map (\<lambda>vs. (
          let
            ls = fset_of_fmap vs 
          in
          map (\<lambda>(a,b). (tbl_name table, a, b)) (sorted_list_of_set ls)
          )) (vals table)
      in
      Ok result
    )
)"

fun resolve_table_factor :: "s_table_factor \<Rightarrow> s_database \<Rightarrow> s_join_result option_err" 
and resolve_join_table :: "s_join_table \<Rightarrow> s_database \<Rightarrow> s_join_result option_err"
and resolve_table_reference :: "s_table_reference \<Rightarrow> s_database \<Rightarrow> s_join_result option_err" where
"resolve_table_factor (STF_Single tbl_nm) db = resolve_single_table tbl_nm db" |
"resolve_table_factor (STF_Multiple []) _ = Error (''No tables specified for JOIN'')" |
"resolve_table_factor (STF_Multiple (x#xs)) db = (
  case resolve_table_reference x db of 
    Error x \<Rightarrow> Error x |
    Ok res \<Rightarrow> (
      case xs of 
        [] \<Rightarrow> Ok res |
        _ \<Rightarrow> (
          case resolve_table_factor (STF_Multiple xs) db of 
            Error x \<Rightarrow> Error x |
            Ok res2 \<Rightarrow> Ok (res @ res2)
        )
    )
)" |

"resolve_join_table (SJT tr tf )" |
"resolve_table_reference (SFA_Table_Factor table_factor) db = resolve_table_factor table_factor db" |
"resolve_table_reference (SFA_Join_Table join) db = resolve_join_table join db"

(*fun get_values_for_select_arguments :: "s_select_argument list \<Rightarrow> ((s_rowname, s_value) fmap) list \<Rightarrow> " *)

(*fun select_from_single_table :: "s_query \<Rightarrow> s_table \<Rightarrow> s_query_result" where
"select_from_single_table (SQ args from where groupby) table = (
  case check_schema_for_select_arguments (schema table) args of 
    Some err \<Rightarrow> SQR_Error err |
    None \<Rightarrow> 
)"*)

fun select :: "s_query \<Rightarrow> s_database \<Rightarrow> s_query_result" where
"select (SQ args from where groupby) (SD tables) = (
  case from of 
     SFA_Tbl_Name from_table \<Rightarrow> ( 
      case fmlookup tables from_table of
        None \<Rightarrow> SQR_Error (''Table '' @ (show_table_name from_table) @ '' doesn't exist'') |
        Some t \<Rightarrow> SQR_Error ''table found''
     ) 
) "

fun test_query :: "unit => s_query" where 
"test_query _ = SQ [] (SFA_Table_Name (STN_String ''test_table'')) SWA_Empty SGB_Empty"

value "select (test_query ()) (test_db ())"

end 