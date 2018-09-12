theory SQL1
  imports Main "~~/src/HOL/Library/Finite_Map"
begin

fun pipe :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" where 
"pipe a f = (f a)"

notation pipe (infixl "|>" 80)

datatype s_type 
  = ST_String 
  | ST_Int 
  | ST_Date

type_synonym s_column_name = string

datatype s_value 
  = SV_String string 
  | SV_Int int 
  | SV_Null

fun string_of_nat :: "nat \<Rightarrow> string"
where
  "string_of_nat n = (if n < 10 then [char_of_nat (48 + n)] else 
     string_of_nat (n div 10) @ [char_of_nat (48 + (n mod 10))])"

definition string_of_int :: "int \<Rightarrow> string"
where
  "string_of_int i = (if i < 0 then ''-'' @ string_of_nat (nat (- i)) else 
     string_of_nat (nat i))"


fun show_s_value :: "s_value \<Rightarrow> string" where 
"show_s_value (SV_String s) = ''\"'' @ s @ ''\"'' " |
"show_s_value (SV_Int i) = string_of_int i" |
"show_s_value SV_Null = ''NULL''"

fun s_value_eq :: "s_value \<Rightarrow> s_value \<Rightarrow> bool" where
"s_value_eq (SV_String s1) (SV_String s2) = (s1 = s2)" |
"s_value_eq (SV_Int i1) (SV_Int i2) = (i1 = i2)" |
"s_value_eq (SV_Null) (SV_Null) = True" |
"s_value_eq _ _ = False"

record s_schema_cell = 
  s_schema_column_name :: s_column_name
  s_schema_column_type :: s_type

type_synonym s_schema = "s_schema_cell list"

type_synonym s_tbl_name = string

datatype s_select_argument 
  = SSA_Rowname s_column_name 
  | SSA_Tablecolumn_name s_tbl_name s_column_name 
  | SSA_Star

datatype s_identifier
  = SI_Simple s_column_name
  | SI_With_Tbl_Name s_tbl_name s_column_name

datatype s_simple_expr 
  = SSE_Literal s_value (* this is a simplification *)
  | SSE_Identifier s_identifier
datatype s_bit_expr
  = SBE_Add s_bit_expr s_bit_expr
  | SBE_Mult s_bit_expr s_bit_expr
  | SBE_Simple_Expr s_simple_expr
datatype s_predicate 
  = SP_Bit_Expr s_bit_expr
datatype s_comparison_operator
  = SCO_Equal
  | SCO_Less
datatype s_boolean_primary 
  = SBP_Is_Null s_boolean_primary
  | SBP_Comparison s_boolean_primary s_comparison_operator s_predicate
  | SBP_Predicate s_predicate
datatype s_expr
  = SE_Or s_expr s_expr
  | SE_And s_expr s_expr
  | SE_Not s_expr 
  | SE_Boolean_Primary s_boolean_primary


datatype 
  s_join_condition 
    = SJC_Using "s_column_name list"
datatype 
  s_table_factor 
    = STF_Single s_tbl_name 
    | STF_Multiple "s_table_reference list"
and
  s_join_table 
    = SJT_Join s_table_reference s_table_factor "s_join_condition option" (* for now it is inner join *) 
    | SJT_Left_Join s_table_reference s_table_reference s_join_condition
    | SJT_Nat_Join s_table_reference s_table_factor
and 
  s_table_reference 
    = SFA_Table_Factor s_table_factor 
    | SFA_Join_Table s_join_table 

datatype s_aggregating_expr
  = SAE_Max s_expr
  | SAE_Sum s_expr
  | SAE_Count s_expr

datatype s_select_expr_unnamed
  = SSEU_Expr s_expr
  | SSEU_Aggregating s_aggregating_expr
datatype s_select_expr 
  = SSE_Unnamed s_select_expr_unnamed
  | SSE_Alias s_column_name s_select_expr_unnamed
  | SSE_Star "s_tbl_name option"

fun get_tbl_names_from_tf :: "s_table_factor \<Rightarrow> s_tbl_name list"
and get_tbl_names_from_tr :: "s_table_reference \<Rightarrow> s_tbl_name list" where 
"get_tbl_names_from_tf (STF_Single x) = [x]" |
"get_tbl_names_from_tf (STF_Multiple []) = []" |
"get_tbl_names_from_tf (STF_Multiple (x#xs)) = 
  (get_tbl_names_from_tr x) @ get_tbl_names_from_tr (SFA_Table_Factor (STF_Multiple xs))" |

"get_tbl_names_from_tr (SFA_Table_Factor tf) = get_tbl_names_from_tf tf" | 
"get_tbl_names_from_tr (SFA_Join_Table (SJT_Join tr tf _)) = 
  get_tbl_names_from_tr tr @ get_tbl_names_from_tf tf" | 
"get_tbl_names_from_tr (SFA_Join_Table (SJT_Left_Join tr1 tr2 _)) = 
  get_tbl_names_from_tr tr1 @ get_tbl_names_from_tr tr2" |
"get_tbl_names_from_tr (SFA_Join_Table (SJT_Nat_Join tr tf)) = 
  get_tbl_names_from_tr tr @ get_tbl_names_from_tf tf"

datatype s_where_argument = SWA_AND s_where_argument s_where_argument | SWA_ISNULL s_column_name | SWA_Empty

datatype s_group_by = SGB_Empty

record s_row_cell =
  s_row_select_argument :: s_select_argument
  s_row_value :: s_value

datatype s_row = SS_Row "s_row_cell list"

datatype s_query_result = SQR_Success "s_row list" | SQR_Error string

datatype s_query = SQ "s_select_argument list" s_table_reference s_where_argument s_group_by

datatype 'a option_err = Error string | Ok 'a 

fun map_oe :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option_err \<Rightarrow> 'b option_err" where 
"map_oe _ (Error x) = Error x" |
"map_oe f (Ok x) = Ok (f x)"

(* notation map_oe (infixl "<$>" 80) *)

fun and_map_oe :: "('a  \<Rightarrow> 'b) option_err \<Rightarrow> 'a option_err \<Rightarrow> 'b option_err" where 
"and_map_oe (Error x) _ = Error x" |
"and_map_oe _ (Error x) = Error x" |
"and_map_oe (Ok f) (Ok a) = Ok (f a)"

(* notation and_map_oe (infixl "<*>" 80) *)

fun and_then_oe :: "('a \<Rightarrow> 'b option_err) \<Rightarrow> 'a option_err  \<Rightarrow> 'b option_err" where 
"and_then_oe _ (Error x) = Error x" |
"and_then_oe f (Ok a) = f a"

(*notation and_then_oe (infixl "\<bind>" 80)*)

record s_table_cell =
  s_table_cell_column_name :: s_column_name
  s_table_cell_value :: s_value

record s_join_result_cell = s_table_cell + 
  s_join_result_cell_tbl_name :: "s_tbl_name list"

record s_join_result_schema_cell = s_schema_cell + 
  s_join_result_schema_tbl_name :: "s_tbl_name list"

type_synonym s_join_row = "s_join_result_cell list"

type_synonym s_join_result_vals =  "s_join_row list"

record s_join_result = 
  s_join_result_schema :: "s_join_result_schema_cell list"
  s_join_result_vals :: s_join_result_vals

record s_select_args_result_cell =
  s_select_expr :: s_select_expr
  s_select_value :: s_value

type_synonym s_select_args_result_row = "s_select_args_result_cell list"

record s_select_args_result =
  s_select_args_result :: "s_select_args_result_row list"

record s_table = 
  s_table_tbl_name :: s_tbl_name
  s_table_schema :: s_schema 
  s_table_vals :: "(s_table_cell list) list"

datatype s_insert_query = SIQ "(s_column_name, s_value) fmap"

datatype s_database = SD "s_table list"

fun test_schema :: "unit \<Rightarrow> s_schema" where
"test_schema _ = SS_Schema 
    [ \<lparr> s_schema_column_name = ''id'', s_schema_column_type = ST_Int \<rparr>
    , \<lparr> s_schema_column_name = ''name'', s_schema_column_type = ST_String \<rparr>
    ]"

fun test_table :: "unit \<Rightarrow> s_table" where
"test_table _ = 
  \<lparr> s_table_tbl_name = STN_String ''test_table''
  , s_table_schema = test_schema ()
  , s_table_vals = [
    [ \<lparr>s_table_cell_column_name = ''id'', s_table_cell_value = SV_Int 10\<rparr>
    , \<lparr>s_table_cell_column_name = ''name'', s_table_cell_value = SV_String ''test''\<rparr>]
  ]
  \<rparr>
" 

value "test_table () |> s_table_vals |> map ( map (\<lambda>x. s_table_cell.extend x (s_join_result_cell.fields (STN_String ''a'')) ))"

fun test_db :: "unit \<Rightarrow> s_database" where 
"test_db _ = SD (fmap_of_list [(STN_String ''test_table'', test_table ())])"

value "SR_String ''a'' = SR_String ''b''"
value "test_db ()"

fun lookup_column_name :: "s_column_name \<Rightarrow> ('a \<Rightarrow> s_column_name) \<Rightarrow> 'a list \<Rightarrow> 'a option" where 
"lookup_column_name rn getter [] = None" |
"lookup_column_name rn getter (x#xs) = (
  case (getter x = rn) of 
    True \<Rightarrow> Some x |
    False \<Rightarrow> lookup_column_name rn getter xs
)"

fun lookup_tbl_name :: "s_tbl_name \<Rightarrow> ('a \<Rightarrow> s_tbl_name) \<Rightarrow> 'a list \<Rightarrow> 'a option" where 
"lookup_tbl_name rn getter [] = None" |
"lookup_tbl_name rn getter (x#xs) = (
  case (getter x = rn) of 
    True \<Rightarrow> Some x |
    False \<Rightarrow> lookup_tbl_name rn getter xs
)"

fun is_value_correct :: "s_value \<Rightarrow> s_type \<Rightarrow> bool" where
"is_value_correct (SV_String _) (ST_String) = True" |
"is_value_correct (SV_Int _) (ST_Int) = True" |
"is_value_correct (SV_Null) _ = True" |
"is_value_correct _ _ = False"


fun is_insert_query_correct_helper :: "s_schema \<Rightarrow> s_column_name \<Rightarrow> s_value \<Rightarrow> bool" where
"is_insert_query_correct_helper (SS_Schema sch) column_name value = (
  case fmlookup sch column_name of 
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
        SSA_Rowname column_name \<Rightarrow> (
          case fmlookup sch column_name of 
            None \<Rightarrow> Some (''Unknown column \"''  @ column_name @ ''\" in \"field list\"'') |
            Some x \<Rightarrow> None
        )
    )
)" | 
"check_schema_for_select_arguments (SS_Schema sch) [] = None" 

fun table_names_unique :: "s_tbl_name list \<Rightarrow> bool" where 
"table_names_unique list = distinct (map show_table_name list)"

fun find_in_row :: "s_column_name \<Rightarrow> s_join_row  \<Rightarrow> s_join_result_cell list" where 
"find_in_row rn [] = []" |
"find_in_row rn (cell # rest) = (
  case rn = s_table_cell_column_name cell of 
    True \<Rightarrow> cell # find_in_row rn rest |
    False \<Rightarrow> find_in_row rn rest
)"

fun remove_from_row :: "s_column_name list \<Rightarrow> s_join_row \<Rightarrow> s_join_row" where 
"remove_from_row [] x = x" |
"remove_from_row (r # rs) x = filter (op \<noteq> r \<circ> s_table_cell_column_name) (remove_from_row rs x)"

fun inner_join_using :: "s_column_name list \<Rightarrow> s_join_row \<Rightarrow> s_join_row \<Rightarrow> ((s_join_result_cell list) option) option_err" where
"inner_join_using [] _ _ = Error ''Empty 'using' list''" |
"inner_join_using (x#xs) l r = (
  case (find_in_row x l, find_in_row x r) of 
    ([jrc1], [jrc2]) \<Rightarrow> (
      case s_value_eq (s_table_cell_value jrc1) (s_table_cell_value jrc2) of 
        False \<Rightarrow> Ok None |
        True \<Rightarrow> (
          let merged_cell = 
            \<lparr> s_table_cell_column_name = x
            , s_table_cell_value = s_table_cell_value jrc1
            , s_join_result_cell_tbl_name = s_join_result_cell_tbl_name jrc1 @ s_join_result_cell_tbl_name jrc2
            \<rparr>
          in (
          case xs of 
            [] \<Rightarrow> Ok (Some [merged_cell]) |
            _ \<Rightarrow> inner_join_using xs l r 
              |> map_oe (\<lambda>rest. (case rest of 
                Some merged_cells \<Rightarrow> Some (merged_cell # merged_cells) |
                None \<Rightarrow> None
              ))
        ))
    ) |
    ([], _) \<Rightarrow> Error (''Cannot find column '' @ x @ '' in the left table of join'') |
    (_, []) \<Rightarrow> Error (''Cannot find column '' @ x @ '' in the right table of join'') |
    (a#b#rs, _) \<Rightarrow> Error (''More than one column '' @ x @ '' found in the left table of join'')|
    (_, a#b#rs) \<Rightarrow> Error (''More than one column '' @ x @ '' found in the right table of join'')
)"

fun inner_join_try :: "s_join_condition \<Rightarrow> s_join_row \<Rightarrow> s_join_row \<Rightarrow> ((s_join_row) option) option_err" where 
"inner_join_try (SJC_Using rnl) l r = (
  case inner_join_using rnl l r of 
    Error x \<Rightarrow> Error x |
    Ok None \<Rightarrow> Ok None |
    Ok (Some merged_cells) \<Rightarrow> Ok (Some (merged_cells @ remove_from_row rnl (l @ r)))
)"


fun inner_join_single_row :: "s_join_condition  \<Rightarrow> s_join_row \<Rightarrow> s_join_result_vals \<Rightarrow> s_join_result_vals option_err" where 
"inner_join_single_row cond left_row [] = Ok []" |
"inner_join_single_row cond left_row (r#rs) = (
  case inner_join_try cond left_row r of 
    Error x \<Rightarrow> Error x |
    Ok can_join \<Rightarrow> (
      case inner_join_single_row cond left_row rs of 
        Error x \<Rightarrow> Error x |
        Ok join_res \<Rightarrow> (
          case can_join of 
            Some new_row \<Rightarrow> Ok (new_row # join_res) |
            None \<Rightarrow> Ok join_res
        )
    )
)"

fun inner_join_helper :: "s_join_condition \<Rightarrow> s_join_result_vals \<Rightarrow> s_join_result_vals \<Rightarrow> s_join_result_vals option_err" where 
"inner_join_helper _ [] _ = Ok []" |
"inner_join_helper conds (l#ls) rs = (
  case inner_join_single_row conds l rs of 
    Error x \<Rightarrow> Error x |
    Ok join_res \<Rightarrow> (
      case inner_join_helper conds ls rs of 
        Error x \<Rightarrow> Error x |
        Ok join_res2 \<Rightarrow> Ok (join_res @ join_res2)
    )
)"

fun add_tbl_name_to_schema :: "s_tbl_name \<Rightarrow> s_schema_cell \<Rightarrow> s_join_result_schema_cell" where 
"add_tbl_name_to_schema tbl_name schema_cell = 
  \<lparr> s_schema_column_name = s_schema_column_name schema_cell
  , s_schema_column_type = s_schema_column_type schema_cell
  , s_join_result_schema_tbl_name = [tbl_name]
  \<rparr>
"

fun cross_join_tables_helper :: "s_join_result_vals \<Rightarrow> s_join_result_vals \<Rightarrow> s_join_result_vals" where
"cross_join_tables_helper [] _ = []" |
"cross_join_tables_helper (l#ls) rs = 
  map (\<lambda>r. l @ r) rs @ cross_join_tables_helper ls rs
"

fun cross_join_tables :: "s_join_result \<Rightarrow> s_join_result \<Rightarrow> s_join_result" where
"cross_join_tables l r = 
  \<lparr> s_join_result_schema = s_join_result_schema l @ s_join_result_schema r
  , s_join_result_vals = cross_join_tables_helper (s_join_result_vals l) (s_join_result_vals r)
  \<rparr>
"

fun inner_join :: "s_join_condition option \<Rightarrow> s_join_result \<Rightarrow> s_join_result \<Rightarrow> s_join_result option_err" where
"inner_join o_cond l r = (
  case o_cond of 
    None \<Rightarrow> Ok (cross_join_tables l r) |
    Some cond \<Rightarrow> (
      let inner_join_vals = inner_join_helper cond (s_join_result_vals l) (s_join_result_vals r) in
      inner_join_vals 
        |> map_oe (
          \<lambda>vals. 
            \<lparr> s_join_result_schema = append
                (s_join_result_schema l) 
                (s_join_result_schema r)
            , s_join_result_vals = vals
            \<rparr>
          )
    )
)"

fun make_empty_row :: "s_join_result_schema_cell list \<Rightarrow> s_join_row" where 
"make_empty_row [] = []" |
"make_empty_row (schema_cell#rest) = (
  let cell = 
    \<lparr> s_table_cell_column_name = s_schema_column_name schema_cell
    , s_table_cell_value = SV_Null
    , s_join_result_cell_tbl_name = s_join_result_schema_tbl_name schema_cell
    \<rparr>
  in
  cell # make_empty_row rest
)"

fun left_join_helper :: "s_join_condition \<Rightarrow> s_join_result_vals \<Rightarrow> s_join_result \<Rightarrow> s_join_result_vals option_err" where 
"left_join_helper _ [] _ = Ok [] " |
"left_join_helper cond (l#ls) rs = (
  inner_join_single_row cond l (s_join_result_vals rs) 
  |> map_oe (\<lambda>single_row_result. (
    case single_row_result of 
      (x#xs) \<Rightarrow> single_row_result |
      [] \<Rightarrow> [l @ make_empty_row (s_join_result_schema rs)]
  ))
)"

fun left_join :: "s_join_condition \<Rightarrow> s_join_result \<Rightarrow> s_join_result \<Rightarrow> s_join_result option_err" where
"left_join cond l r = (
  let left_join_vals = left_join_helper cond (s_join_result_vals l) r in
  left_join_vals 
    |> map_oe (
      \<lambda>vals. 
        \<lparr> s_join_result_schema = append
            (s_join_result_schema l) 
            (s_join_result_schema r)
        , s_join_result_vals = vals
        \<rparr>
      )
)"

fun find_same_column_names :: "s_join_result_schema_cell list \<Rightarrow> s_join_result_schema_cell list \<Rightarrow> (s_column_name list) option_err" where 
"find_same_column_names [] _ = Ok []" |
"find_same_column_names (l#ls) rs = (
  case find ((op = (s_schema_column_name l)) \<circ> s_schema_column_name) ls of 
    Some _ \<Rightarrow> Error (''Column '' @ s_schema_column_name l @ '' occurs more than once in the left table of join'') |
    None \<Rightarrow> (
      case filter ((op = (s_schema_column_name l)) \<circ> s_schema_column_name) rs of 
        [] \<Rightarrow> find_same_column_names ls rs |
        [r] \<Rightarrow> find_same_column_names ls rs |> map_oe (op # (s_schema_column_name l)) |
        (a # b # rest) \<Rightarrow> Error (''Column '' @ s_schema_column_name l @ '' occurs more than once in the right table of join'')
    )
)"

fun natural_join :: "s_join_result \<Rightarrow> s_join_result \<Rightarrow> s_join_result option_err" where 
"natural_join l r = 
  find_same_column_names (s_join_result_schema l) (s_join_result_schema r)
  |> and_then_oe (\<lambda>same_column_names. inner_join (Some (SJC_Using same_column_names)) l r)
" (* definition of natural join in https://dev.mysql.com/doc/refman/8.0/en/join.html *)

fun resolve_single_table :: "s_tbl_name \<Rightarrow> s_database \<Rightarrow> s_join_result option_err" where
"resolve_single_table tbl_nm (SD tables) = (
  case lookup_tbl_name tbl_nm s_table_tbl_name tables of
    None \<Rightarrow> Error (''Unknown table '' @ tbl_nm @ '' in database '') |
    Some table \<Rightarrow> ( 
      let 
        result = s_table_vals table 
          |> map (map (\<lambda>tc. \<lparr> 
              s_table_cell_column_name = s_table_cell_column_name tc,
              s_table_cell_value = s_table_cell_value tc,
              s_join_result_cell_tbl_name = [tbl_nm]
            \<rparr>))
      in
      Ok 
        \<lparr> s_join_result_schema = s_table_schema table |> map (add_tbl_name_to_schema (s_table_tbl_name table))
        , s_join_result_vals = result 
        \<rparr>
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
            Ok res2 \<Rightarrow> Ok (cross_join_tables res res2)
        )
    )
)" |

"resolve_join_table (SJT_Join tr tf conds) db = 
  resolve_table_reference tr db
  |> and_then_oe (\<lambda>jr1. resolve_table_factor tf db
  |> and_then_oe (\<lambda>jr2. inner_join conds jr1 jr2
  ))" |
"resolve_join_table (SJT_Left_Join tr1 tr2 cond) db = 
  resolve_table_reference tr1 db
  |> and_then_oe (\<lambda>jr1. resolve_table_reference tr2 db
  |> and_then_oe (\<lambda>jr2. left_join cond jr1 jr2
  ))" |
"resolve_join_table (SJT_Nat_Join tr tf) db = 
  resolve_table_reference tr db
  |> and_then_oe (\<lambda>jr1. resolve_table_factor tf db
  |> and_then_oe (\<lambda>jr2. natural_join jr1 jr2
  ))" |

"resolve_table_reference (SFA_Table_Factor table_factor) db = resolve_table_factor table_factor db" |
"resolve_table_reference (SFA_Join_Table join) db = resolve_join_table join db"


fun interpret_identifier :: "s_identifier \<Rightarrow> s_join_row \<Rightarrow> s_value option_err" where 
"interpret_identifier (SI_Simple rn) jr = (
  case find_in_row rn jr of 
    [] \<Rightarrow> Error (''Unknown column '' @ rn @ '' in where clause'') |
    (x # y # zs) \<Rightarrow> Error (''Column '' @ rn @ '' in where clause is ambiguous'') | 
    [cell] \<Rightarrow> Ok (s_table_cell_value cell) 
)" |
"interpret_identifier (SI_With_Tbl_Name tbl_nm rn) [] = Error (''Unknown column '' @ tbl_nm @ ''.'' @ rn @ '' in where clause'') " |
"interpret_identifier (SI_With_Tbl_Name tbl_nm rn) (cell # rest) = (
  case (s_table_cell_column_name cell = rn, lookup_tbl_name tbl_nm id (s_join_result_cell_tbl_name cell)) of 
    (True, Some _) \<Rightarrow> Ok (s_table_cell_value cell) |
    _ \<Rightarrow> interpret_identifier (SI_With_Tbl_Name tbl_nm rn) rest
)"

fun interpret_simple_expr :: "s_simple_expr \<Rightarrow> s_join_row \<Rightarrow> s_value option_err" where 
"interpret_simple_expr (SSE_Literal s_value) _ = Ok s_value" |
"interpret_simple_expr (SSE_Identifier i) jr = interpret_identifier i jr"

fun interpret_bit_expr :: "s_bit_expr \<Rightarrow> s_join_row \<Rightarrow> s_value option_err" where
"interpret_bit_expr (SBE_Add e1 e2) jr = (
  case (interpret_bit_expr e1 jr, interpret_bit_expr e2 jr) of
    (Ok (SV_Int i1), Ok (SV_Int i2)) \<Rightarrow> Ok (SV_Int (i1 + i2)) |
    (Ok SV_Null, _) \<Rightarrow> Ok SV_Null |
    (_, Ok SV_Null) \<Rightarrow> Ok SV_Null |
    (Error x, _) \<Rightarrow> Error x |
    (_, Error x) \<Rightarrow> Error x |
    (Ok x1, Ok x2) \<Rightarrow> Error (''Wrong arguments for addition: '' @ show_s_value x1 @ '' and '' @ show_s_value x2)
)" |
"interpret_bit_expr (SBE_Mult e1 e2) jr = (
  case (interpret_bit_expr e1 jr, interpret_bit_expr e2 jr) of
    (Ok (SV_Int i1), Ok (SV_Int i2)) \<Rightarrow> Ok (SV_Int (i1 * i2)) |
    (Ok SV_Null, _) \<Rightarrow> Ok SV_Null |
    (_, Ok SV_Null) \<Rightarrow> Ok SV_Null |
    (Error x, _) \<Rightarrow> Error x |
    (_, Error x) \<Rightarrow> Error x |
    (Ok x1, Ok x2) \<Rightarrow> Error (''Wrong arguments for multiplication: '' @ show_s_value x1 @ '' and '' @ show_s_value x2)
)" | 
"interpret_bit_expr (SBE_Simple_Expr e) jr = interpret_simple_expr e jr"

fun interpret_predicate :: "s_predicate \<Rightarrow> s_join_row \<Rightarrow> s_value option_err" where 
"interpret_predicate (SP_Bit_Expr e) jr = interpret_bit_expr e jr"

fun bool_to_s_value :: "bool \<Rightarrow> s_value" where 
"bool_to_s_value True = SV_Int 1" | 
"bool_to_s_value False = SV_Int 0" 

fun interpret_boolean_primary :: "s_boolean_primary \<Rightarrow> s_join_row \<Rightarrow> s_value option_err" where
"interpret_boolean_primary (SBP_Is_Null bp) jr = (
  interpret_boolean_primary bp jr 
  |> and_then_oe (\<lambda>res. case res of 
    SV_Null \<Rightarrow> Ok (bool_to_s_value True) |
    _ \<Rightarrow> Ok (bool_to_s_value False)
  )
)" |
"interpret_boolean_primary (SBP_Comparison bp SCO_Equal pred) jr = 
  interpret_boolean_primary bp jr 
  |> and_then_oe (\<lambda>l. interpret_predicate pred jr
  |> and_then_oe (\<lambda>r. (
    case l of 
      SV_Null \<Rightarrow> Ok SV_Null | 
      _ \<Rightarrow> (
        case r of 
          SV_Null \<Rightarrow> Ok SV_Null |
          _ \<Rightarrow> (s_value_eq l r) |> bool_to_s_value |> Ok)
      )
  ))
" |
"interpret_boolean_primary (SBP_Comparison bp SCO_Less pred) jr = 
  interpret_boolean_primary bp jr 
  |> and_then_oe (\<lambda>l. interpret_predicate pred jr
  |> and_then_oe (\<lambda>r. ( 
        case (l, r) of 
          (SV_Int il, SV_Int ir) \<Rightarrow> Ok (bool_to_s_value (il < ir)) |
          (SV_Null, _) \<Rightarrow> Ok SV_Null |
          (_, SV_Null) \<Rightarrow> Ok SV_Null |
          (_,_) \<Rightarrow> Error (''Not comparable values in the where clause'')
      )
  ))
" |
"interpret_boolean_primary (SBP_Predicate pred) jr = interpret_predicate pred jr"

fun is_true :: "s_value \<Rightarrow> bool" where 
"is_true v = s_value_eq v (SV_Int 1)"

fun boolean_operator :: "s_value \<Rightarrow> s_value \<Rightarrow> (bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> s_value" where 
"boolean_operator SV_Null _ _ = SV_Null" | 
"boolean_operator _ SV_Null _ = SV_Null" | 
"boolean_operator a b f = f (is_true a) (is_true b) |> bool_to_s_value" 

fun interpret_expr :: "s_expr \<Rightarrow> s_join_row \<Rightarrow> s_value option_err" where 
"interpret_expr (SE_Or e1 e2) jr = 
  interpret_expr e1 jr 
  |> and_then_oe (\<lambda>r1. interpret_expr e2 jr
  |> and_then_oe (\<lambda>r2. boolean_operator r1 r2 (op \<or>) |> Ok))" |
"interpret_expr (SE_And e1 e2) jr = 
  interpret_expr e1 jr 
  |> and_then_oe (\<lambda>r1. interpret_expr e2 jr
  |> and_then_oe (\<lambda>r2. boolean_operator r1 r2 (op \<and>) |> Ok))" |
"interpret_expr (SE_Not e) jr = 
  interpret_expr e jr 
  |> map_oe (\<lambda>r. (
    case r of 
      SV_Null \<Rightarrow> SV_Null |
      _ \<Rightarrow> (\<not> (is_true r)) |> bool_to_s_value
  ))" |
"interpret_expr (SE_Boolean_Primary bp) jr = 
  interpret_boolean_primary bp jr
"

fun interpret_where_helper :: "s_expr \<Rightarrow> s_join_row list \<Rightarrow> (s_join_row list) option_err" where 
"interpret_where_helper e [] = Ok []" |
"interpret_where_helper e (jr # jrs) = 
  interpret_expr e jr 
  |> and_then_oe (\<lambda>jr_res. interpret_where_helper e jrs
  |> and_then_oe (\<lambda>jrs_res.
    case is_true jr_res of
      True \<Rightarrow> Ok (jr # jrs_res) |
      False \<Rightarrow> Ok jrs_res
  ))
"


fun interpret_where :: "s_expr \<Rightarrow> s_join_result \<Rightarrow> s_join_result option_err" where
"interpret_where e jres = 
  jres
    |> s_join_result_vals
    |> interpret_where_helper e
    |> map_oe (\<lambda>vals. jres\<lparr> s_join_result_vals := vals \<rparr>)
"




(*fun get_values_for_select_arguments :: "s_select_argument list \<Rightarrow> ((s_column_name, s_value) fmap) list \<Rightarrow> " *)

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