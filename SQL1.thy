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

datatype s_comparison_operator
  = SCO_Equal
  | SCO_Less
datatype s_function 
  = SF_Max s_expr
  | SF_Count s_expr
  | SF_Sum s_expr
and s_simple_expr 
  = SSE_Literal s_value (* this is a simplification *)
  | SSE_Identifier s_identifier
  | SSE_Function s_function
and s_bit_expr
  = SBE_Add s_bit_expr s_bit_expr
  | SBE_Mult s_bit_expr s_bit_expr
  | SBE_Simple_Expr s_simple_expr
and s_predicate 
  = SP_Bit_Expr s_bit_expr
and s_boolean_primary 
  = SBP_Is_Null s_boolean_primary
  | SBP_Comparison s_boolean_primary s_comparison_operator s_predicate
  | SBP_Predicate s_predicate
and s_expr
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

datatype s_select_expr_all
  = SSEA_Expr s_expr
  | SSEA_Alias s_column_name s_expr 
  | SSEA_Star

datatype s_select_expr 
  = SSE_Expr s_expr
  | SSE_Alias s_column_name s_expr 

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

fun and_map_oe :: "'a option_err \<Rightarrow> ('a  \<Rightarrow> 'b) option_err \<Rightarrow> 'b option_err" where 
"and_map_oe (Error x) _ = Error x" |
"and_map_oe _ (Error x) = Error x" |
"and_map_oe (Ok a) (Ok f) = Ok (f a)"

(* notation and_map_oe (infixl "<*>" 80) *)

fun and_then_oe :: "('a \<Rightarrow> 'b option_err) \<Rightarrow> 'a option_err \<Rightarrow> 'b option_err" where 
"and_then_oe _ (Error x) = Error x" |
"and_then_oe f (Ok a) = f a"

(*notation and_then_oe (infixl "\<bind>" 80)*)

fun sequence_oe :: "'a option_err list \<Rightarrow> 'a list option_err" where 
"sequence_oe [] = Ok []" |
"sequence_oe (x # xs) = 
  x
  |> map_oe (op #) 
  |> and_map_oe (sequence_oe xs)"

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

record s_select_args_result_row = 
  s_select_args_result_row_vals :: "s_select_args_result_cell list"
  s_join_result_row :: "s_join"

record s_select_args_result =
  s_select_args_result :: "s_select_args_result_row list"

(*record s_group_cell =
  s_group_cell_column_name :: "s_column_name"
  s_group_cell_tbl_name :: "s_tbl_name list"
  s_group_cell_values :: "s_value list"*)

record s_group_row = 
  s_grouped_rows :: "s_join_row list" 
  s_grouping_values :: "(s_expr \<times> s_value) list"

record s_group_result = 
  s_group_result :: "s_group_row list"
  s_group_result_schema :: "s_join_result_schema_cell list"
  s_group_result_grouped :: bool

record s_select_cell = 
  s_select_cell_argument :: s_select_expr
  s_select_cell_value :: s_value

record s_select_row = s_group_row + 
  s_select_row_values :: "s_select_cell list"

record s_select_result = 
  s_select_result :: "s_select_row list"
  s_select_result_grouped :: bool

record s_table = 
  s_table_tbl_name :: s_tbl_name
  s_table_schema :: s_schema 
  s_table_vals :: "(s_table_cell list) list"

datatype s_compare 
  = GT
  | LT
  | EQ 

datatype s_compare_type 
  = SCT_Asc
  | SCT_Desc

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

fun find_in_row :: "s_column_name \<Rightarrow> 'cell list \<Rightarrow> ('cell \<Rightarrow> s_column_name) \<Rightarrow> 'cell list" where 
"find_in_row rn [] get = []" |
"find_in_row rn (cell # rest) get = (
  case rn = get cell of 
    True \<Rightarrow> cell # find_in_row rn rest get |
    False \<Rightarrow> find_in_row rn rest get
)"

fun remove_from_row :: "s_column_name list \<Rightarrow> s_join_row \<Rightarrow> s_join_row" where 
"remove_from_row [] x = x" |
"remove_from_row (r # rs) x = filter (op \<noteq> r \<circ> s_table_cell_column_name) (remove_from_row rs x)"

fun inner_join_using :: "s_column_name list \<Rightarrow> s_join_row \<Rightarrow> s_join_row \<Rightarrow> ((s_join_result_cell list) option) option_err" where
"inner_join_using [] _ _ = Error ''Empty 'using' list''" |
"inner_join_using (x#xs) l r = (
  case (find_in_row x l s_table_cell_column_name, find_in_row x r s_table_cell_column_name) of 
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

type_synonym 'row identifier_evaluator = "s_column_name \<Rightarrow> s_tbl_name option \<Rightarrow> 'row \<Rightarrow> s_value option_err" 
(* row is polymorphic instead of cell because we need to have the whole row context to correctly 
handle errors.  
*)
type_synonym 'row function_evaluator = "s_function \<Rightarrow> 'row \<Rightarrow> s_value option_err"

fun interpret_identifier :: "s_identifier \<Rightarrow> 'row => 'row identifier_evaluator \<Rightarrow> s_value option_err" where
"interpret_identifier (SI_Simple col) row ev = ev col None row" |
"interpret_identifier (SI_With_Tbl_Name tbl_nm col) row ev = ev col (Some tbl_nm) row" 

fun interpret_simple_expr :: "s_simple_expr \<Rightarrow> 'row => 'row identifier_evaluator \<Rightarrow> 'row function_evaluator  \<Rightarrow> s_value option_err" where 
"interpret_simple_expr (SSE_Literal s_value) _ _ _ = Ok s_value" |
"interpret_simple_expr (SSE_Identifier i) row iev fev = interpret_identifier i row iev" |
"interpret_simple_expr (SSE_Function f) row iev fev = fev f row"

fun interpret_bit_expr :: "s_bit_expr \<Rightarrow> 'row => 'row identifier_evaluator => 'row function_evaluator \<Rightarrow> s_value option_err" where
"interpret_bit_expr (SBE_Add e1 e2) row iev fev  = (
  case (interpret_bit_expr e1 row iev fev, interpret_bit_expr e2 row iev fev) of
    (Ok (SV_Int i1), Ok (SV_Int i2)) \<Rightarrow> Ok (SV_Int (i1 + i2)) |
    (Ok SV_Null, _) \<Rightarrow> Ok SV_Null |
    (_, Ok SV_Null) \<Rightarrow> Ok SV_Null |
    (Error x, _) \<Rightarrow> Error x |
    (_, Error x) \<Rightarrow> Error x |
    (Ok x1, Ok x2) \<Rightarrow> Error (''Wrong arguments for addition: '' @ show_s_value x1 @ '' and '' @ show_s_value x2)
)" |
"interpret_bit_expr (SBE_Mult e1 e2) row iev fev = (
  case (interpret_bit_expr e1 row iev fev, interpret_bit_expr e2 row iev fev) of
    (Ok (SV_Int i1), Ok (SV_Int i2)) \<Rightarrow> Ok (SV_Int (i1 * i2)) |
    (Ok SV_Null, _) \<Rightarrow> Ok SV_Null |
    (_, Ok SV_Null) \<Rightarrow> Ok SV_Null |
    (Error x, _) \<Rightarrow> Error x |
    (_, Error x) \<Rightarrow> Error x |
    (Ok x1, Ok x2) \<Rightarrow> Error (''Wrong arguments for multiplication: '' @ show_s_value x1 @ '' and '' @ show_s_value x2)
)" | 
"interpret_bit_expr (SBE_Simple_Expr e) row iev fev = interpret_simple_expr e row iev fev"

fun interpret_predicate :: "s_predicate \<Rightarrow> 'row => 'row identifier_evaluator => 'row function_evaluator \<Rightarrow> s_value option_err" where 
"interpret_predicate (SP_Bit_Expr e) row iev fev = interpret_bit_expr e row iev fev"

fun bool_to_s_value :: "bool \<Rightarrow> s_value" where 
"bool_to_s_value True = SV_Int 1" | 
"bool_to_s_value False = SV_Int 0" 

fun interpret_boolean_primary :: "s_boolean_primary \<Rightarrow> 'row => 'row identifier_evaluator => 'row function_evaluator \<Rightarrow> s_value option_err" where
"interpret_boolean_primary (SBP_Is_Null bp) row iev fev = (
  interpret_boolean_primary bp row iev fev 
  |> and_then_oe (\<lambda>res. case res of 
    SV_Null \<Rightarrow> Ok (bool_to_s_value True) |
    _ \<Rightarrow> Ok (bool_to_s_value False)
  )
)" |
"interpret_boolean_primary (SBP_Comparison bp SCO_Equal pred) row iev fev = 
  interpret_boolean_primary bp row iev fev 
  |> and_then_oe (\<lambda>l. interpret_predicate pred row iev fev
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
"interpret_boolean_primary (SBP_Comparison bp SCO_Less pred) row iev fev = 
  interpret_boolean_primary bp row iev fev 
  |> and_then_oe (\<lambda>l. interpret_predicate pred row iev fev
  |> and_then_oe (\<lambda>r. ( 
        case (l, r) of 
          (SV_Int il, SV_Int ir) \<Rightarrow> Ok (bool_to_s_value (il < ir)) |
          (SV_Null, _) \<Rightarrow> Ok SV_Null |
          (_, SV_Null) \<Rightarrow> Ok SV_Null |
          (_,_) \<Rightarrow> Error (''Not comparable values in the where clause'')
      )
  ))
" |
"interpret_boolean_primary (SBP_Predicate pred) row iev fev = interpret_predicate pred row iev fev"

fun is_true :: "s_value \<Rightarrow> bool" where 
"is_true v = s_value_eq v (SV_Int 1)"

fun boolean_operator :: "s_value \<Rightarrow> s_value \<Rightarrow> (bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> s_value" where 
"boolean_operator SV_Null _ _ = SV_Null" | 
"boolean_operator _ SV_Null _ = SV_Null" | 
"boolean_operator a b f = f (is_true a) (is_true b) |> bool_to_s_value" 

fun interpret_expr :: "s_expr \<Rightarrow> 'row => 'row identifier_evaluator => 'row function_evaluator \<Rightarrow> s_value option_err" where 
"interpret_expr (SE_Or e1 e2) row iev fev = 
  interpret_expr e1 row iev fev 
  |> and_then_oe (\<lambda>r1. interpret_expr e2 row iev fev
  |> and_then_oe (\<lambda>r2. boolean_operator r1 r2 (op \<or>) |> Ok))" |
"interpret_expr (SE_And e1 e2) row iev fev = 
  interpret_expr e1 row iev fev 
  |> and_then_oe (\<lambda>r1. interpret_expr e2 row iev fev
  |> and_then_oe (\<lambda>r2. boolean_operator r1 r2 (op \<and>) |> Ok))" |
"interpret_expr (SE_Not e) row iev fev = 
  interpret_expr e row iev fev 
  |> map_oe (\<lambda>r. (
    case r of 
      SV_Null \<Rightarrow> SV_Null |
      _ \<Rightarrow> (\<not> (is_true r)) |> bool_to_s_value
  ))" |
"interpret_expr (SE_Boolean_Primary bp) row iev fev = 
  interpret_boolean_primary bp row iev fev
"

fun evaluate_identifier_join_row :: "s_join_row identifier_evaluator" where 
"evaluate_identifier_join_row col None jr = (
  case find_in_row col jr s_table_cell_column_name of 
    [] \<Rightarrow> Error (''Unknown column '' @ col @ '' in where clause'') |
    (x # y # zs) \<Rightarrow> Error (''Column '' @ col @ '' in where clause is ambiguous'') | 
    [cell] \<Rightarrow> Ok (s_table_cell_value cell) 
)" |
"evaluate_identifier_join_row col (Some tbl_nm) [] = Error (''Unknown column '' @ tbl_nm @ ''.'' @ col @ '' in where clause'') " |
"evaluate_identifier_join_row col (Some tbl_nm) (cell # rest) = (
  case (s_table_cell_column_name cell = col, lookup_tbl_name tbl_nm id (s_join_result_cell_tbl_name cell)) of 
    (True, Some _) \<Rightarrow> Ok (s_table_cell_value cell) |
    _ \<Rightarrow> evaluate_identifier_join_row col (Some tbl_nm) rest
)"

fun evaluate_function_join_row :: "s_join_row function_evaluator" where 
"evaluate_function_join_row (SF_Max _) _ = Error ''Invalid use of group function''" |
"evaluate_function_join_row (SF_Count _) _ = Error ''Invalid use of group function''" |
"evaluate_function_join_row (SF_Sum _) _ = Error ''Invalid use of group function''" 

fun interpret_where_helper :: "s_expr \<Rightarrow> s_join_row list \<Rightarrow> (s_join_row list) option_err" where 
"interpret_where_helper e [] = Ok []" |
"interpret_where_helper e (jr # jrs) = 
  interpret_expr e jr evaluate_identifier_join_row evaluate_function_join_row
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

fun has_aggregation_h5 :: "s_function \<Rightarrow> bool" where 
"has_aggregation_h5 (SF_Max _) = True" | 
"has_aggregation_h5 (SF_Count _) = True" |
"has_aggregation_h5 (SF_Sum _) = True" 

fun has_aggregation_h4 :: "s_simple_expr \<Rightarrow> bool" where 
"has_aggregation_h4 (SSE_Literal _) = False" |
"has_aggregation_h4 (SSE_Identifier _) = False" | 
"has_aggregation_h4 (SSE_Function f) = has_aggregation_h5 f" 

fun has_aggregation_h3 :: "s_bit_expr \<Rightarrow> bool" where 
"has_aggregation_h3 (SBE_Add sbe1 sbe2) = (has_aggregation_h3 sbe1 \<and> has_aggregation_h3 sbe2)" |
"has_aggregation_h3 (SBE_Mult sbe1 sbe2) = (has_aggregation_h3 sbe1 \<and> has_aggregation_h3 sbe2)" |
"has_aggregation_h3 (SBE_Simple_Expr se) = has_aggregation_h4 se" 

fun has_aggregation_h1 :: "s_boolean_primary \<Rightarrow> bool" where 
"has_aggregation_h1 (SBP_Is_Null bp) = has_aggregation_h1 bp" |
"has_aggregation_h1 (SBP_Comparison bp _ (SP_Bit_Expr be)) = (has_aggregation_h1 bp \<and> has_aggregation_h3 be)" |
"has_aggregation_h1 (SBP_Predicate (SP_Bit_Expr be)) = (has_aggregation_h3 be)" 

fun has_aggregation :: "s_expr \<Rightarrow> bool" where
"has_aggregation (SE_Or e1 e2) = (has_aggregation e1 \<and> has_aggregation e2)" |
"has_aggregation (SE_And e1 e2) = (has_aggregation e1 \<and> has_aggregation e2)" |
"has_aggregation (SE_Not e1) = has_aggregation e1" |
"has_aggregation (SE_Boolean_Primary bp) = has_aggregation_h1 bp" 

fun has_aggregation_select_arg :: "s_select_expr \<Rightarrow> bool" where 
"has_aggregation_select_arg (SSE_Expr e) = has_aggregation e" |
"has_aggregation_select_arg (SSE_Alias _ e) = has_aggregation e"

fun convert_to_group_result :: "s_join_result \<Rightarrow> s_group_result" where 
"convert_to_group_result jres = (
  \<lparr> s_group_result = jres 
      |> s_join_result_vals 
      |> map (\<lambda>row. 
        \<lparr> s_grouped_rows = [row]
        , s_grouping_values = [] 
        \<rparr>
      )
  , s_group_result_schema = s_join_result_schema jres
  , s_group_result_grouped = False
  \<rparr>
)"

fun is_simple_identifier :: "s_expr \<Rightarrow> s_identifier option" where 
"is_simple_identifier (SE_Boolean_Primary (SBP_Predicate (SP_Bit_Expr (SBE_Simple_Expr (SSE_Identifier x))))) = Some x" |
"is_simple_identifier _ = None"

fun find_in_select_exprs :: "s_column_name \<Rightarrow> ('cell \<Rightarrow> s_select_expr) \<Rightarrow> (s_expr \<Rightarrow> 'cell \<Rightarrow> 'result) \<Rightarrow> 'cell list \<Rightarrow> 'result list" where 
"find_in_select_exprs col f rf [] = []" |
"find_in_select_exprs col1 f rf (c # rest) = (
  case f c of 
    (SSE_Alias col2 expr) \<Rightarrow> (
      case col1 = col2 of 
        True \<Rightarrow> rf expr c # find_in_select_exprs col1 f rf rest |
        False \<Rightarrow> find_in_select_exprs col1 f rf rest
    ) | 
    (SSE_Expr e) \<Rightarrow> (
      case (is_simple_identifier e = Some (SI_Simple col1)) of 
        True \<Rightarrow> rf e c # find_in_select_exprs col1 f rf rest |
        False \<Rightarrow>  find_in_select_exprs col1 f rf rest
    )
)"

fun find_in_select_exprs_with_tbl_nm :: "s_column_name \<Rightarrow> s_tbl_name \<Rightarrow> ('cell \<Rightarrow> s_select_expr) \<Rightarrow> (s_expr \<Rightarrow> 'cell \<Rightarrow> 'result) \<Rightarrow> 'cell list \<Rightarrow> 'result list" where 
"find_in_select_exprs_with_tbl_nm col tbl_nm f rf [] = []" |
"find_in_select_exprs_with_tbl_nm col1 tbl_nm f rf (c # rest) = (
  case f c of 
    (SSE_Alias col2 expr) \<Rightarrow> find_in_select_exprs_with_tbl_nm col1 tbl_nm f rf rest | 
    (SSE_Expr e) \<Rightarrow> (
      case (is_simple_identifier e = Some (SI_With_Tbl_Name tbl_nm col1)) of 
        True \<Rightarrow> rf e c # find_in_select_exprs_with_tbl_nm col1 tbl_nm f rf rest |
        False \<Rightarrow>  find_in_select_exprs_with_tbl_nm col1 tbl_nm f rf rest
    )
)"

(* MySQL resolves unqualified column or alias references in ORDER BY clauses by searching in the select_expr values, then in the columns of the tables in the FROM clause. For GROUP BY or HAVING clauses, it searches the FROM clause before searching in the select_expr values.
From: https://dev.mysql.com/doc/refman/8.0/en/select.html *)
fun evaluate_identifier_in_group_expr :: "s_select_expr list \<Rightarrow> s_join_row identifier_evaluator" 
and evaluate_function_in_group_expr :: "s_join_row function_evaluator" where 
"evaluate_identifier_in_group_expr select_exprs col None jr = (
  case find_in_row col jr s_table_cell_column_name of 
    [] \<Rightarrow> (
      case find_in_select_exprs col id (\<lambda>e _. e) select_exprs of 
        [] \<Rightarrow> Error (''Unknown column '' @ col @ '' in group statement'') |
        (x # y # zs) \<Rightarrow> Error (''Column '' @ col @ '' in group statement is ambiguous'') | 
        [expr] \<Rightarrow> 
            interpret_expr expr jr (evaluate_identifier_in_group_expr []) evaluate_function_in_group_expr        
    ) |
    (x # y # zs) \<Rightarrow> Error (''Column '' @ col @ '' in group statement is ambiguous'') | 
    [cell] \<Rightarrow> Ok (s_table_cell_value cell)
)" |
"evaluate_identifier_in_group_expr se col (Some tbl_nm) [] = Error (''Unknown column '' @ tbl_nm @ ''.'' @ col @ '' in group statement'') " |
"evaluate_identifier_in_group_expr se col (Some tbl_nm) (cell # rest) = (
  case (s_table_cell_column_name cell = col, lookup_tbl_name tbl_nm id (s_join_result_cell_tbl_name cell)) of 
    (True, Some _) \<Rightarrow> Ok (s_table_cell_value cell) |
    _ \<Rightarrow> evaluate_identifier_in_group_expr se col (Some tbl_nm) rest
)" |
"evaluate_function_in_group_expr (SF_Max _) _ = Error ''Invalid use of group function''" |
"evaluate_function_in_group_expr (SF_Count _) _ = Error ''Invalid use of group function''" |
"evaluate_function_in_group_expr (SF_Sum _) _ = Error ''Invalid use of group function''" 

fun remove_from_list :: "'a \<Rightarrow> 'a list \<Rightarrow> ('a list) option" where 
"remove_from_list a [] = None" |
"remove_from_list a (x#xs) = (
  case a = x of 
    True \<Rightarrow> Some xs | 
    False \<Rightarrow> (
      case remove_from_list a xs of 
        Some xs1 \<Rightarrow> Some (x # xs1) | 
        None \<Rightarrow> None
    )
)"

fun list_eq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where 
"list_eq [] [] = True" |  
"list_eq [] _ = False" | 
"list_eq (l#ls) rs = (
  case remove_from_list l rs of 
    Some rs2 \<Rightarrow> list_eq ls rs2 |
    None \<Rightarrow> False
)" 

fun remove_from_join_row :: "s_column_name \<Rightarrow> s_tbl_name list \<Rightarrow> s_join_row \<Rightarrow> (s_join_result_cell \<times> s_join_row) option" where 
"remove_from_join_row _ _ [] = None" | 
"remove_from_join_row col tnl (cell # rest) = (
  case col = s_table_cell_column_name cell \<and> list_eq tnl (s_join_result_cell_tbl_name cell) of 
    True \<Rightarrow> Some (cell, rest) | 
    False \<Rightarrow> (
      case remove_from_join_row col tnl rest of 
        Some (cell2, rest2) \<Rightarrow> Some (cell2, cell # rest2) | 
        None \<Rightarrow> None
    ) 
)"

fun evaluate_expr_in_group_expr :: "s_select_expr list \<Rightarrow> s_join_row \<Rightarrow> s_expr \<Rightarrow> s_value option_err" where 
"evaluate_expr_in_group_expr se jr e = interpret_expr e jr (evaluate_identifier_in_group_expr se) evaluate_function_in_group_expr"

fun can_group :: "s_select_expr list \<Rightarrow> s_expr list \<Rightarrow> s_join_row \<Rightarrow> s_join_row \<Rightarrow> bool option_err" where 
"can_group se group_exprs jr1 jr2 = (
  let 
    eval1 = group_exprs |> map (evaluate_expr_in_group_expr se jr1) |> sequence_oe;
    eval2 = group_exprs |> map (evaluate_expr_in_group_expr se jr2) |> sequence_oe
  in (
    eval1 
    |> and_then_oe (\<lambda>ev1. eval2 
    |> and_then_oe (\<lambda>ev2. Ok (ev1 = ev2))) 
  )
)"

fun partition_oe :: "('a \<Rightarrow> bool option_err) \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list) option_err" where 
"partition_oe _ [] = Ok ([], [])" |
"partition_oe f (x # xs) = 
  f x 
  |> and_then_oe (\<lambda>a. partition_oe f xs 
  |> and_then_oe (\<lambda>(y, n). 
    case a of 
      True \<Rightarrow> Ok (x # y, n) |
      False \<Rightarrow> Ok (y, x # n)
  ))
"

function group_by_helper :: "s_select_expr list \<Rightarrow> s_expr list \<Rightarrow> s_join_row list \<Rightarrow> s_group_row list \<Rightarrow> s_group_row list option_err" where 
"group_by_helper _ _ [] acc = Ok acc" |
"group_by_helper se grexprs (jr # rest) acc = 
  partition_oe (can_group se grexprs jr) rest
  |> and_then_oe (\<lambda>(ys, ns). (
      let 
        grouping_values = grexprs 
          |> map (\<lambda>e. evaluate_expr_in_group_expr se jr e 
            |> map_oe (\<lambda>r. (e, r))
          ) 
          |> sequence_oe
      in 
        grouping_values 
        |> and_then_oe (\<lambda>gv. 
          group_by_helper 
            se 
            grexprs 
            ns 
            (\<lparr>s_grouped_rows = jr # ys, s_grouping_values = gv\<rparr> # acc)
        )
    ) 
  )
"
  by pat_completeness auto
termination sorry 

fun evaluate_group_by :: "s_select_expr list \<Rightarrow> s_expr option \<Rightarrow> s_expr list \<Rightarrow> s_join_result \<Rightarrow> s_group_result option_err" where 
"evaluate_group_by select_args having_arg group_args j_res = (
  case (filter has_aggregation_select_arg select_args, group_args, map_option has_aggregation having_arg) of 
    ([], [], Some False) \<Rightarrow> 
        Ok (convert_to_group_result j_res) |
    _ \<Rightarrow> 
      group_by_helper select_args  group_args (s_join_result_vals j_res) [] 
        |> map_oe (\<lambda>vs. 
          \<lparr> s_group_result = vs
          , s_group_result_schema = s_join_result_schema j_res
          , s_group_result_grouped = True
          \<rparr>
        )
)"

fun evaluate_max :: "s_value list \<Rightarrow> s_value option_err" where 
"evaluate_max [] = Ok SV_Null" |
"evaluate_max (SV_Null # rest) = evaluate_max rest" |
"evaluate_max ((SV_Int i) # rest) = 
  evaluate_max rest
  |> map_oe (\<lambda>result. (
    case result of 
      SV_Int i2 \<Rightarrow> (if i > i2 then SV_Int i else SV_Int i2) | 
      _ \<Rightarrow> SV_Int i
    )
)" | 
"evaluate_max ((SV_String s) # rest) = Error (''Can't evaluate MAX on string expressions'')"

fun evaluate_sum :: "s_value list \<Rightarrow> s_value option_err" where 
"evaluate_sum [] = Ok SV_Null" |
"evaluate_sum (SV_Null # rest) = evaluate_sum rest" |
"evaluate_sum ((SV_Int i) # rest) = 
  evaluate_sum rest
  |> map_oe (\<lambda>result. (
    case result of 
      SV_Int i2 \<Rightarrow> SV_Int (i + i2) | 
      _ \<Rightarrow> SV_Int i
    )
)" | 
"evaluate_sum ((SV_String s) # rest) = Error (''Can't evaluate SUM on string expressions'')"

fun evaluate_count :: "s_value list \<Rightarrow> int option_err" where 
"evaluate_count [] = Ok 0" |
"evaluate_count (SV_Null # rest) = evaluate_count rest" |
"evaluate_count (_ # rest) = 
  evaluate_count rest
  |> map_oe (op + 1)
"

fun same_values :: "'a list \<Rightarrow> 'a option" where 
"same_values [] = None" |
"same_values (x # xs) = (
  case xs of 
    [] \<Rightarrow> Some x | 
    _ \<Rightarrow> (
      case same_values xs of 
        None \<Rightarrow> None | 
        Some x1 \<Rightarrow> (
          case x1 = x of 
            True \<Rightarrow> Some x | 
            False \<Rightarrow> None
        )
    )
)"

fun evaluate_identifier_in_select_expr :: "s_group_row identifier_evaluator" 
and evaluate_identifier_in_select_expr_helper :: "s_join_row identifier_evaluator"
and evaluate_function_in_select_expr :: "s_group_row function_evaluator"
and evaluate_function_in_select_expr_inside_grouping_function :: "s_join_row function_evaluator" where 
"evaluate_identifier_in_select_expr_helper col None jr = (
  case find_in_row col jr s_table_cell_column_name of 
    [] \<Rightarrow> Error (''Unknown column '' @ col @ '' in 'field list' '') |
    (x # y # zs) \<Rightarrow> Error (''Column '' @ col @ '' in field list is ambiguous'') | 
    [cell] \<Rightarrow> Ok (s_table_cell_value cell)
)" |
"evaluate_identifier_in_select_expr_helper col (Some tbl_nm) [] = Error (''Unknown column '' @ tbl_nm @ ''.'' @ col @ '' in field list'')" |
"evaluate_identifier_in_select_expr_helper col (Some tbl_nm) (cell # rest) = (
  case (s_table_cell_column_name cell = col, lookup_tbl_name tbl_nm id (s_join_result_cell_tbl_name cell)) of 
    (True, Some _) \<Rightarrow> Ok (s_table_cell_value cell) |
    _ \<Rightarrow> evaluate_identifier_in_select_expr_helper col (Some tbl_nm) rest
)" |
"evaluate_identifier_in_select_expr col o_tbl_nm gr = 
  gr 
    |> s_grouped_rows 
    |> map (evaluate_identifier_in_select_expr_helper col o_tbl_nm)
    |> sequence_oe
    |> and_then_oe (\<lambda>values. 
      case same_values values of 
        None \<Rightarrow> Error (''Cannot group on '' @ col @ '' as the values from grouped rows are ambiguous'') | 
        Some v \<Rightarrow> Ok v
    )
" |
"evaluate_function_in_select_expr_inside_grouping_function (SF_Max _) _ = Error ''Invalid use of group function''" |
"evaluate_function_in_select_expr_inside_grouping_function (SF_Count _) _ = Error ''Invalid use of group function''" |
"evaluate_function_in_select_expr_inside_grouping_function (SF_Sum _) _ = Error ''Invalid use of group function''" | 
"evaluate_function_in_select_expr (SF_Max e) gr = 
  gr 
    |> s_grouped_rows
    |> map (\<lambda>jr. interpret_expr e jr evaluate_identifier_in_select_expr_helper evaluate_function_in_select_expr_inside_grouping_function)
    |> sequence_oe 
    |> and_then_oe evaluate_max
" |
"evaluate_function_in_select_expr (SF_Count e) gr = 
  gr 
    |> s_grouped_rows
    |> map (\<lambda>jr. interpret_expr e jr evaluate_identifier_in_select_expr_helper evaluate_function_in_select_expr_inside_grouping_function)
    |> sequence_oe 
    |> and_then_oe evaluate_count
    |> map_oe SV_Int
" | 
"evaluate_function_in_select_expr (SF_Sum e) gr = 
  gr 
    |> s_grouped_rows
    |> map (\<lambda>jr. interpret_expr e jr evaluate_identifier_in_select_expr_helper evaluate_function_in_select_expr_inside_grouping_function)
    |> sequence_oe 
    |> and_then_oe evaluate_sum
"

fun identifier_expr :: "s_column_name \<Rightarrow> s_tbl_name option \<Rightarrow> s_expr" where 
"identifier_expr col None = 
  col
    |> SI_Simple
    |> SSE_Identifier
    |> SBE_Simple_Expr
    |> SP_Bit_Expr
    |> SBP_Predicate
    |> SE_Boolean_Primary
" | 
"identifier_expr col (Some tbl_name) = 
  SI_With_Tbl_Name tbl_name col 
    |> SSE_Identifier
    |> SBE_Simple_Expr
    |> SP_Bit_Expr
    |> SBP_Predicate
    |> SE_Boolean_Primary
"

fun evaluate_select_expr :: "s_select_expr \<Rightarrow> s_group_row \<Rightarrow> s_select_cell option_err" 
and evaluate_select_expr_helper :: "s_expr \<Rightarrow> s_group_row \<Rightarrow> s_value option_err" where 
"evaluate_select_expr_helper e gr = 
  interpret_expr e gr evaluate_identifier_in_select_expr evaluate_function_in_select_expr
" |
"evaluate_select_expr (SSE_Expr e) gr = 
  evaluate_select_expr_helper e gr
    |> map_oe (\<lambda>v. \<lparr> s_select_cell_argument = (SSE_Expr e), s_select_cell_value = v \<rparr>)
"| 
"evaluate_select_expr (SSE_Alias col e) gr = 
  evaluate_select_expr_helper e gr
    |> map_oe (\<lambda>v. \<lparr> s_select_cell_argument = (SSE_Alias col e), s_select_cell_value = v \<rparr>)
" 
fun evaluate_select_single_row :: "s_select_expr list \<Rightarrow> s_group_row \<Rightarrow> s_select_row option_err" where 
"evaluate_select_single_row se gr = 
  se
    |> map (\<lambda>se. evaluate_select_expr se gr) 
    |> sequence_oe
    |> map_oe (\<lambda>res. 
        \<lparr> s_grouped_rows = s_grouped_rows gr
        , s_grouping_values = s_grouping_values gr
        , s_select_row_values = res 
        \<rparr>
    ) 
"

fun convert_select_expr :: "s_join_result_schema_cell list \<Rightarrow> s_select_expr_all \<Rightarrow> s_select_expr list" where 
"convert_select_expr _ (SSEA_Expr e) = [SSE_Expr e]" |
"convert_select_expr _ (SSEA_Alias col e) = [SSE_Alias col e]" |
"convert_select_expr schema (SSEA_Star) = 
  schema 
    |> map (\<lambda>sc. (
      case s_join_result_schema_tbl_name sc of 
        [tn] \<Rightarrow> identifier_expr (s_schema_column_name sc) (Some tn) |> SSE_Expr |
        _ \<Rightarrow> identifier_expr (s_schema_column_name sc) (None) |> SSE_Expr
    ))
" 

fun evaluate_select :: "s_select_expr_all list \<Rightarrow> s_group_result \<Rightarrow> s_select_result option_err" where
"evaluate_select se gres = 
  gres 
    |> s_group_result
    |> map (evaluate_select_single_row (se |> map (convert_select_expr (s_group_result_schema gres)) |> concat)) 
    |> sequence_oe
    |> map_oe (\<lambda>res. \<lparr> s_select_result = res, s_select_result_grouped = s_group_result_grouped gres  \<rparr>)
"

(*MySQL resolves unqualified column or alias references in ORDER BY clauses by searching in the select_expr values, then in the columns of the tables in the FROM clause. For GROUP BY or HAVING clauses, it searches the FROM clause before searching in the select_expr values. (For GROUP BY and HAVING, this differs from the pre-MySQL 5.0 behavior that used the same rules as for ORDER BY.) *)
(*The SQL standard requires that HAVING must reference only columns in the GROUP BY clause or columns used in aggregate functions. However, MySQL supports an extension to this behavior, and permits HAVING to refer to columns in the SELECT list and columns in outer subqueries as well.*)
(*There is a difference in resolving nested group functions. SUM(SUM(x)) will fail in MySQL, SUM(a) where we have SUM(x) as a in field list - this will return NULL (even though both are equivalent). Here both will fail *)
fun evaluate_identifier_in_having :: "s_select_row identifier_evaluator" 
and evaluate_function_in_having :: "s_select_row function_evaluator" 
and evaluate_identifier_in_having_inside_aggr_function :: "s_select_expr list \<Rightarrow> s_join_row identifier_evaluator"
and evaluate_function_in_having_inside_aggr_function :: "s_join_row function_evaluator" where 
"evaluate_identifier_in_having col None sr = (
  case filter (\<lambda>(expr, v). is_simple_identifier expr = Some (SI_Simple col)) (s_grouping_values sr) of 
    ((_, v) # rest) \<Rightarrow> Ok v |
    _ \<Rightarrow> (
      case find_in_select_exprs col s_select_cell_argument (\<lambda>e. s_select_cell_value) (s_select_row_values sr) of 
        [] \<Rightarrow> Error (''Unknown column '' @ col @ '' in having clause'') |
        (x # y # zs) \<Rightarrow> Error (''Column '' @ col @ '' in having clause is ambiguous'') |
        [v] \<Rightarrow> Ok v
    )
)" | 
"evaluate_identifier_in_having col (Some tbl_nm) sr = (
  case filter (\<lambda>(expr, v). is_simple_identifier expr = Some (SI_With_Tbl_Name tbl_nm col)) (s_grouping_values sr) of 
    ((_, v) # rest) \<Rightarrow> Ok v |
    _ \<Rightarrow> (
      case 
          find_in_select_exprs_with_tbl_nm col tbl_nm s_select_cell_argument (\<lambda>e. s_select_cell_value) (s_select_row_values sr)
      of 
        [] \<Rightarrow> Error (''Unknown column '' @ tbl_nm @ ''.'' @ col @ '' in having clause'') |
        (x # y # zs) \<Rightarrow> Error (''Column '' @ tbl_nm @ ''.'' @ col @ '' in having clause is ambiguous'') |
        [v] \<Rightarrow> Ok v
    )
)" |
"evaluate_function_in_having (SF_Max e) sr = 
  sr 
    |> s_grouped_rows
    |> map (\<lambda>jr. 
      interpret_expr 
        e 
        jr 
        (evaluate_identifier_in_having_inside_aggr_function (s_select_row_values sr |> map s_select_cell_argument))
        evaluate_function_in_having_inside_aggr_function
    )
    |> sequence_oe 
    |> and_then_oe evaluate_max" |
"evaluate_function_in_having (SF_Sum e) sr = 
  sr 
    |> s_grouped_rows
    |> map (\<lambda>jr. 
      interpret_expr 
        e 
        jr 
        (evaluate_identifier_in_having_inside_aggr_function (s_select_row_values sr |> map s_select_cell_argument))
        evaluate_function_in_having_inside_aggr_function
    )
    |> sequence_oe 
    |> and_then_oe evaluate_sum" |
"evaluate_function_in_having (SF_Count e) sr = 
  sr 
    |> s_grouped_rows
    |> map (\<lambda>jr. 
      interpret_expr 
        e 
        jr 
        (evaluate_identifier_in_having_inside_aggr_function (s_select_row_values sr |> map s_select_cell_argument))
        evaluate_function_in_having_inside_aggr_function
    )
    |> sequence_oe 
    |> and_then_oe evaluate_count
    |> map_oe SV_Int" |
"evaluate_identifier_in_having_inside_aggr_function s_exprs col None jr = (
  case find_in_row col jr s_table_cell_column_name of 
    (x # y # zs) \<Rightarrow> Error (''Column '' @ col @ '' in having clause is ambiguous'') | 
    [cell] \<Rightarrow> Ok (s_table_cell_value cell) | 
    [] \<Rightarrow> (
      case find_in_select_exprs col id (\<lambda>e _. e) s_exprs of 
        [] \<Rightarrow> Error (''Unknown column '' @ col @ '' in having clause'') |
        (x # y # zs) \<Rightarrow> Error (''Column '' @ col @ '' in having clause is ambiguous'') |
        [e] \<Rightarrow> interpret_expr e jr (evaluate_identifier_in_having_inside_aggr_function []) evaluate_function_in_having_inside_aggr_function
    )
)" |
"evaluate_identifier_in_having_inside_aggr_function s_exprs col (Some tbl_nm) [] = Error (''Unknown column '' @ tbl_nm @ ''.'' @ col @ '' in having cluase'')" |
"evaluate_identifier_in_having_inside_aggr_function s_exprs col (Some tbl_nm) (cell # rest) = (
  case (s_table_cell_column_name cell = col, lookup_tbl_name tbl_nm id (s_join_result_cell_tbl_name cell)) of 
    (True, Some _) \<Rightarrow> Ok (s_table_cell_value cell) |
    _ \<Rightarrow> evaluate_identifier_in_having_inside_aggr_function s_exprs col (Some tbl_nm) rest
)" |
"evaluate_function_in_having_inside_aggr_function (SF_Max _) jr = Error ''Invalid use of group function''" |
"evaluate_function_in_having_inside_aggr_function (SF_Sum _) jr = Error ''Invalid use of group function''" |
"evaluate_function_in_having_inside_aggr_function (SF_Count _) jr = Error ''Invalid use of group function''" 

fun evaluate_having :: "s_expr \<Rightarrow> s_select_result \<Rightarrow> s_select_result option_err" where 
"evaluate_having expr s_res = 
  s_res
    |> s_select_result
    |> map (\<lambda>sr. interpret_expr expr sr evaluate_identifier_in_having evaluate_function_in_having 
      |> map_oe (\<lambda>res. (sr, res))
    )
    |> sequence_oe
    |> map_oe (filter (\<lambda>(_, res). is_true res))
    |> map_oe (map (\<lambda>(sr, _). sr)) 
    |> map_oe (\<lambda>srs. \<lparr> s_select_result = srs, s_select_result_grouped = s_select_result_grouped s_res  \<rparr>)
"

fun compare_string :: "string \<Rightarrow> string \<Rightarrow> s_compare" where 
"compare_string [] [] = EQ" | 
"compare_string (l # ls) [] = GT" |
"compare_string [] (r # rs) = LT" | 
"compare_string (l # ls) (r # rs) = (
  case nat_of_char l < nat_of_char r of 
    True \<Rightarrow> LT | 
    False \<Rightarrow> (
      case nat_of_char l > nat_of_char r of 
        True \<Rightarrow> GT | 
        False \<Rightarrow> EQ
    )
)"

fun compare_int :: "int \<Rightarrow> int \<Rightarrow> s_compare" where 
"compare_int i1 i2 = (
  case i1 < i2 of 
    True \<Rightarrow> LT |
    False \<Rightarrow> (
      case i1 > i2 of 
        True \<Rightarrow> GT |
        False \<Rightarrow> EQ
    )  
)"

fun compare_s_values :: "s_value \<Rightarrow> s_value \<Rightarrow> s_compare option_err" where 
"compare_s_values (SV_Null) _ = Ok LT" | 
"compare_s_values _ (SV_Null) = Ok GT" | 
"compare_s_values (SV_Int i1) (SV_Int i2) = Ok (compare_int i1 i2)" |
"compare_s_values (SV_String s1) (SV_String s2) = Ok (compare_string s1 s2)" | 
"compare_s_values v1 v2 = Error (''Cannot compare values of different type: '' @ show_s_value v1 @ '' and '' @ show_s_value v2)"

datatype 'a bin_tree 
  = Empty 
  | Node 'a "'a bin_tree" "'a bin_tree"  

fun insert :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> s_compare option_err) \<Rightarrow> 'a bin_tree \<Rightarrow> 'a bin_tree option_err" where 
"insert x c Empty = Ok (Node x Empty Empty)" |
"insert x1 c (Node x2 t1 t2) = (
  c x1 x2
    |> and_then_oe (\<lambda>r. (
      case r of 
        LT \<Rightarrow> insert x1 c t1 
          |> map_oe (\<lambda>t11. Node x2 t11 t2) | 
        _ \<Rightarrow> insert x1 c t2 
          |> map_oe (\<lambda>t22. Node x2 t1 t22)
    )) 
)
"

fun list_of_bin_tree :: "s_compare_type \<Rightarrow> 'a bin_tree \<Rightarrow> 'a list" where 
"list_of_bin_tree _ Empty = []" | 
"list_of_bin_tree (SCT_Asc) (Node x l r) = list_of_bin_tree (SCT_Asc) l @ [x] @ list_of_bin_tree (SCT_Asc) r" |
"list_of_bin_tree (SCT_Desc) (Node x l r) = list_of_bin_tree (SCT_Desc) r @ [x] @ list_of_bin_tree (SCT_Desc) l" 

fun compare_select_rows :: "(s_value list \<times> s_select_row) \<Rightarrow> (s_value list \<times> s_select_row) \<Rightarrow> s_compare option_err" where 
"compare_select_rows ([], _) ([], _) = Ok EQ" | 
"compare_select_rows ((x # xs), _) ([], _) = Error ''Different length of compared lists for compare select rows''" |
"compare_select_rows ([], _) ((x # xs), _) = Error ''Different length of compared lists for compare select rows''" |
"compare_select_rows ((l # ls), lr) ((r # rs), rr) = 
  compare_s_values l r 
    |> and_then_oe (\<lambda>res. (
      case res of 
        EQ \<Rightarrow> compare_select_rows (ls, lr) (rs, rr) | 
        _ \<Rightarrow> Ok res
    ))
"

fun evaluate_identifier_in_order_by :: "s_select_row identifier_evaluator" 
and evaluate_identifier_in_order_by_helper :: "s_join_row identifier_evaluator"
and evaluate_function_in_order_by :: "s_select_row function_evaluator" 
and evaluate_identifier_in_order_by_inside_grouping_function :: "s_select_expr list \<Rightarrow> s_join_row identifier_evaluator"
and evaluate_function_in_order_by_inside_grouping_function :: "s_join_row function_evaluator"  where 
"evaluate_identifier_in_order_by_helper col None jr = (
  case find_in_row col jr s_table_cell_column_name of 
    [] \<Rightarrow> Error (''Unknown column '' @ col @ '' in 'order clause' '') |
    (x # y # zs) \<Rightarrow> Error (''Column '' @ col @ '' in order clause is ambiguous'') | 
    [cell] \<Rightarrow> Ok (s_table_cell_value cell)
)" |
"evaluate_identifier_in_order_by_helper col (Some tbl_nm) [] = Error (''Unknown column '' @ tbl_nm @ ''.'' @ col @ '' in order clause'')" |
"evaluate_identifier_in_order_by_helper col (Some tbl_nm) (cell # rest) = (
  case (s_table_cell_column_name cell = col, lookup_tbl_name tbl_nm id (s_join_result_cell_tbl_name cell)) of 
    (True, Some _) \<Rightarrow> Ok (s_table_cell_value cell) |
    _ \<Rightarrow> evaluate_identifier_in_select_expr_helper col (Some tbl_nm) rest
)"|
"evaluate_identifier_in_order_by col None sr = (
  case find_in_select_exprs col s_select_cell_argument (\<lambda>e. s_select_cell_value) (s_select_row_values sr) of 
    (x # y # zs) \<Rightarrow> Error (''Column '' @ col @ '' in order clause is ambiguous'') |
    [v] \<Rightarrow> Ok v | 
    [] \<Rightarrow> (
      sr 
        |> s_grouped_rows 
        |> map (evaluate_identifier_in_order_by_helper col None)
        |> sequence_oe
        |> and_then_oe (\<lambda>values. 
          case same_values values of 
            None \<Rightarrow> Error (''Cannot group on '' @ col @ '' as the values from grouped rows are ambiguous'') | 
            Some v \<Rightarrow> Ok v
        )
    )
)" | 
"evaluate_identifier_in_order_by col (Some tbl_nm) sr = (
  case find_in_select_exprs_with_tbl_nm col tbl_nm s_select_cell_argument (\<lambda>e. s_select_cell_value) (s_select_row_values sr) of 
    (x # y # zs) \<Rightarrow> Error (''Column '' @ col @ '' in order clause is ambiguous'') |
    [v] \<Rightarrow> Ok v | 
    [] \<Rightarrow> (
      sr 
        |> s_grouped_rows 
        |> map (evaluate_identifier_in_order_by_helper col (Some tbl_nm))
        |> sequence_oe
        |> and_then_oe (\<lambda>values. 
          case same_values values of 
            None \<Rightarrow> Error (''Cannot group on '' @ col @ '' as the values from grouped rows are ambiguous'') | 
            Some v \<Rightarrow> Ok v
        )
    )
)" | 
"evaluate_function_in_order_by (SF_Max e) sr = 
  sr 
    |> s_grouped_rows
    |> map (\<lambda>jr. 
      interpret_expr 
        e 
        jr 
        (evaluate_identifier_in_order_by_inside_grouping_function (s_select_row_values sr |> map s_select_cell_argument)) 
        evaluate_function_in_order_by_inside_grouping_function
    ) 
    |> sequence_oe 
    |> and_then_oe evaluate_max" |
"evaluate_function_in_order_by (SF_Sum e) sr = 
  sr 
    |> s_grouped_rows
    |> map (\<lambda>jr. 
      interpret_expr 
        e 
        jr 
        (evaluate_identifier_in_order_by_inside_grouping_function (s_select_row_values sr |> map s_select_cell_argument)) 
        evaluate_function_in_order_by_inside_grouping_function
    ) 
    |> sequence_oe 
    |> and_then_oe evaluate_sum" | 
"evaluate_function_in_order_by (SF_Count e) sr = 
  sr 
    |> s_grouped_rows
    |> map (\<lambda>jr. 
      interpret_expr 
        e 
        jr 
        (evaluate_identifier_in_order_by_inside_grouping_function (s_select_row_values sr |> map s_select_cell_argument)) 
        evaluate_function_in_order_by_inside_grouping_function
    ) 
    |> sequence_oe 
    |> and_then_oe evaluate_count
    |> map_oe SV_Int
" |
"evaluate_identifier_in_order_by_inside_grouping_function select_exprs col None jr = (
  case find_in_select_exprs col id (\<lambda>e _. e) select_exprs of 
    (x # y # zs) \<Rightarrow> Error (''Column '' @ col @ '' in order clause is ambiguous'') |
    [e] \<Rightarrow> interpret_expr e jr (evaluate_identifier_in_order_by_inside_grouping_function []) evaluate_function_in_order_by_inside_grouping_function |
    [] \<Rightarrow> (
      case find_in_row col jr s_table_cell_column_name of 
        (x # y # zs) \<Rightarrow> Error (''Column '' @ col @ '' in order clause is ambiguous'') |
        [cell] \<Rightarrow> Ok (s_table_cell_value cell) | 
        [] \<Rightarrow> Error (''Unknown column '' @ col @ '' in order clause'')
    )
)" | 
"evaluate_identifier_in_order_by_inside_grouping_function select_exprs col (Some tbl_nm) [] = Error (''Unknown column '' @ tbl_nm @ ''.'' @ col @ '' in order clause'')" |
"evaluate_identifier_in_order_by_inside_grouping_function select_exprs col (Some tbl_nm) (cell # rest) = (
  case (s_table_cell_column_name cell = col, lookup_tbl_name tbl_nm id (s_join_result_cell_tbl_name cell)) of 
    (True, Some _) \<Rightarrow> Ok (s_table_cell_value cell) |
    _ \<Rightarrow> evaluate_identifier_in_order_by_inside_grouping_function select_exprs col (Some tbl_nm) rest
)" | 
"evaluate_function_in_order_by_inside_grouping_function (SF_Max _) _ = Error ''Invalid use of grouping function''" |
"evaluate_function_in_order_by_inside_grouping_function (SF_Sum _) _ = Error ''Invalid use of grouping function''" |
"evaluate_function_in_order_by_inside_grouping_function (SF_Count _) _ = Error ''Invalid use of grouping function''" 

fun evaluate_expr_in_order_by :: "s_expr \<Rightarrow> s_select_row \<Rightarrow> s_value option_err" where 
"evaluate_expr_in_order_by e sr = 
  interpret_expr 
    e 
    sr
    evaluate_identifier_in_order_by
    evaluate_function_in_order_by
"

fun evaluate_order_by :: "s_expr list \<Rightarrow> s_compare_type \<Rightarrow> s_select_result \<Rightarrow> s_select_result option_err" where 
"evaluate_order_by exprs ct s_res = (
  case (filter has_aggregation exprs, s_select_result_grouped s_res) of
    ((x # xs), False) \<Rightarrow> Error (''Expressions in ORDER BY contain aggregate function and apply to the result of a non-aggregated query'') | 
    _ \<Rightarrow> 
      s_res 
        |> s_select_result
        |> map (\<lambda>sr. 
          exprs 
            |> map (\<lambda>e. evaluate_expr_in_order_by e sr) 
            |> sequence_oe 
            |> map_oe (\<lambda>vs. (vs, sr))
        ) 
        |> sequence_oe 
        |> and_then_oe (foldl (\<lambda>tree v. tree |> and_then_oe (insert v compare_select_rows)) (Ok Empty))
        |> map_oe (list_of_bin_tree ct)
        |> map_oe (map snd)
        |> map_oe (\<lambda>vs. s_res\<lparr>s_select_result := vs\<rparr>)
)"
 

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


(* 
how to add indexes/keys, 

how i end up with the order from examples
what can be provable 
how syntax is mapped, what I've got from the documentation, what I've inferred
discuss missing features
how functional programming helped in the reusability of code (w/ examples)
theorems that I would prove
discuss minimality aspect - how semantics and functions 
EXTENDABILITY 
FUNCTIONAL DEPENDENCIES theorems

cannot have count on *
cannot have max on strings - as there is no comparison for strings implemented
Error messages might be a little bit different - there is no syntax matching - for example "Can't group on 'MAX(name)'"
where mysql errors and our implementation does not - functional dependencies
where this implementation errors and mysql does not - comparison of strings
difference in having - because of functional dependencies 
*)

end 