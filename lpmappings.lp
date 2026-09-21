/* dk/lp symbols (on the right) the declarations of which are removed
and whose uses are replaced by the given Coq expressions (on the left) */

/****************************************************************************/
/* STTfa */
/****************************************************************************/

builtin "Type'" ≔ Set;
builtin "Prop" ≔ prop;
builtin "arr" ≔ arr;
builtin "imp" ≔ imp;
builtin "all" ≔ all;

/****************************************************************************/
/* Pure */
/****************************************************************************/

builtin "eq" ≔ eq;

builtin "dummy" ≔ dummy;
builtin "@point" ≔ dummy_pattern;

builtin "HOL2DK_proof" ≔ proof; // unused
builtin "HOL2DK_Appt" ≔ Appt; // unused
builtin "HOL2DK_AppP" ≔ AppP; // unused
builtin "HOL2DK_Abst" ≔ Abst; // unused
builtin "HOL2DK_AbsP" ≔ AbsP; // unused
builtin "HOL2DK_Hyp" ≔ Hyp; // unused
builtin "HOL2DK_Oracle" ≔ Oracle; // unused
builtin "HOL2DK_PClass" ≔ PClass; // unused
builtin "HOL2DK_MinProof" ≔ MinProof; // unused

builtin "itself" ≔ itself;
builtin "type" ≔ {|type|};

builtin "sort_constraint" ≔ sort_constraint;
builtin "@sort_constraint_def" ≔ sort_constraint_def;

builtin "" ≔ prop_const; // is defined as the identity

builtin "term" ≔ term;
builtin "@term_def" ≔ term_def;

builtin "@Logic.eq_refl" ≔ reflexive;
builtin "@Logic.eq_sym" ≔ symmetric;
builtin "@Logic.eq_trans" ≔ transitive;
builtin "@equal_intr" ≔ equal_intr;
builtin "@equal_elim" ≔ equal_elim;

builtin "@abstract_rule" ≔ abstract_rule;
builtin "@combination" ≔ combination;

/* simplification */

builtin "and" ≔ conjunction;
builtin "conjunction_def" ≔ conjunction_def;

/****************************************************************************/
/* Tools.Code_Generator */
/****************************************************************************/

builtin "True" ≔ holds;
builtin "holds_def_raw" ≔ holds_def_raw;

/****************************************************************************/
/* HOL.HOL */
/****************************************************************************/

/* typeclasses */
builtin "type_class" ≔ type_class;
builtin "default_class_pred" ≔ default_class_pred;
builtin "default_class_type" ≔ default_class_type;
builtin "default_class_pred_of_type" ≔ default_class_pred_of_type;
builtin "default" ≔ default_class_default;
builtin "@default_val" ≔ default_class_default_alt;
builtin "default_class" ≔ default_class;
builtin "default_class_def" ≔ default_class_def;
builtin "default_class_type_def" ≔ default_class_type_def;
builtin "default_class_type_def" ≔ default_class_type_def;
builtin "equal_class_pred" ≔ equal_class_pred;
builtin "equal_class_type" ≔ equal_class_type;
builtin "equal_class_pred_of_type" ≔ equal_class_pred_of_type;
builtin "eq" ≔ equal_class_equal_alt;
builtin "equal" ≔ equal_class_equal;
builtin "equal_bis" ≔ equal_class_equal_alt;
builtin "class_equal" ≔ class_equal;
builtin "@class_equal_def" ≔ class_equal_def;
builtin "equal_class" ≔ equal_class;
builtin "equal_class_def" ≔ equal_class_def;
builtin "equal_class_type_def" ≔ equal_class_type_def;
builtin "@equal_class_type_def" ≔ equal_class_type_def;

/* instances */
builtin "itself_equal_pred_instance" ≔ itself_equal_pred_instance;
builtin "equal_itself_inst_equal_itself" ≔ equal_itself_inst_equal_itself;
builtin "@equal_itself_inst_equal_itself_def" ≔ equal_itself_inst_equal_itself_def;
builtin "fun_arity" ≔ fun_arity;
builtin "itself_arity" ≔ itself_arity;
builtin "arity_type_bool" ≔ arity_type_bool;

builtin "@point" ≔ undefined;
builtin "Prop" ≔ bool;
builtin "Trueprop" ≔ Trueprop; // cannot be replaced by ""
builtin "imp" ≔ implies;
builtin "eq" ≔ eq_const;
builtin "ε" ≔ The;
builtin "impI" ≔ impI;
builtin "mp" ≔ mp;
builtin "True_or_False" ≔ True_or_False;
builtin "@eq_reflection" ≔ eq_reflection;
builtin "If" ≔ If;
builtin "If_def_raw" ≔ If_def_raw;
builtin "REMOVE" ≔ not_equal;
builtin "REMOVE" ≔ iff;

/* connectives */

builtin "True" ≔ True;
builtin "True_def_raw" ≔ True_def_raw;

builtin "False" ≔ False;
builtin "False_def_raw" ≔ False_def_raw;

builtin "all" ≔ All;
builtin "All_def_raw" ≔ All_def_raw;

builtin "ex" ≔ Ex;
builtin "Ex_def_raw" ≔ Ex_def_raw;

builtin "Ex1" ≔ Ex1;
builtin "Ex1_def_raw" ≔ Ex1_def_raw;

builtin "not" ≔ Not;
builtin "not_def_raw" ≔ not_def_raw;

builtin "and" ≔ conj;
builtin "and_def_raw" ≔ and_def_raw;

builtin "or" ≔ disj;
builtin "or_def_raw" ≔ or_def_raw;

/* simplifications */

builtin "imp" ≔ simp_implies;
builtin "imp" ≔ induct_implies;
builtin "all" ≔ induct_forall;
builtin "eq" ≔ induct_equal;
builtin "and" ≔ induct_conj;
builtin "True" ≔ induct_true;
builtin "False" ≔ induct_false;

builtin "@refl" ≔ refl;
builtin "@subst" ≔ subst;
builtin "@ext" ≔ ext;
builtin "@the_eq_trivial" ≔ the_eq_trivial;

/****************************************************************************/
/* HOL.Orderings */
/****************************************************************************/

/* typeclasses */
builtin "top_class_pred" ≔ top_class_pred;
builtin "ptPreorderType default_display" ≔ top_class_type;
builtin "top_class_top" ≔ top_class_top;
builtin "@Order.top default_display" ≔ top_class_top_alt;
builtin "top_class" ≔ top_class;
builtin "top_class_def" ≔ top_class_def;
builtin "top_class_type_def" ≔ top_class_type_def;

builtin "bot_class_pred" ≔ bot_class_pred;
builtin "pbPreorderType default_display" ≔ bot_class_type;
builtin "bot" ≔ bot_class_bot;
builtin "@Order.bottom default_display" ≔ bot_class_bot_alt;
builtin "bot_class" ≔ bot_class;
builtin "bot_class_def" ≔ bot_class_def;
builtin "bot_class_type_def" ≔ bot_class_type_def;

builtin "ord_class_pred" ≔ ord_class_pred;
builtin "pPreorderType default_display" ≔ ord_class_type;
builtin "less_eq" ≔ ord_class_less_eq;
builtin "Order.le default_display" ≔ ord_class_less_eq_alt;
builtin "less" ≔ ord_class_less;
builtin "Order.lt default_display" ≔ ord_class_less_alt;
builtin "ord_class" ≔ ord_class;
builtin "ord_class_def" ≔ ord_class_def;
builtin "ord_class_type_def" ≔ ord_class_type_def;

builtin "order_top_class_pred" ≔ order_top_class_pred;
builtin "order_bot_class_pred" ≔ order_bot_class_pred;

builtin "pPreorderType default_display" ≔ preorder_class_type;
builtin "Preorder" ≔ class_preorder;
builtin "class_preorder_def" ≔ class_preorder_def;
builtin "preorder_class" ≔ preorder_class;
builtin "preorder_class_def" ≔ preorder_class_def;
builtin "preorder_class_type_def" ≔ preorder_class_type_def;

builtin "pPOrderType default_display" ≔ order_class_type;
builtin "Pantisymmetric" ≔ class_order_axioms;
builtin "class_order_axioms_def" ≔ class_order_axioms_def;
builtin "order_class" ≔ order_class;
builtin "order_class_def" ≔ order_class_def;
builtin "order_class_type_def" ≔ order_class_type_def;

builtin "pOrderType default_display" ≔ linorder_class_type;
builtin "Ptotal" ≔ class_linorder_axioms;
builtin "class_linorder_axioms_def" ≔ class_linorder_axioms_def;
builtin "linorder_class" ≔ linorder_class;
builtin "linorder_class_def" ≔ linorder_class_def;
builtin "linorder_class_type_def" ≔ linorder_class_type_def;

builtin "pbPOrderType default_display" ≔ order_bot_class_type;
builtin "Pminimal" ≔ class_order_bot_axioms;
builtin "class_order_bot_axioms_def" ≔ class_order_bot_axioms_def;
builtin "order_bot_class" ≔ order_bot_class;
builtin "order_bot_class_def" ≔ order_bot_class_def;
builtin "order_bot_class_type_def" ≔ order_bot_class_type_def;

builtin "ptPOrderType default_display" ≔ order_top_class_type;
builtin "Pmaximal" ≔ class_order_top_axioms;
builtin "class_order_top_axioms_def" ≔ class_order_top_axioms_def;
builtin "order_top_class" ≔ order_top_class;
builtin "order_top_class_def" ≔ order_top_class_def;
builtin "order_top_class_type_def" ≔ order_top_class_type_def;

builtin "dense_order_class_type default_display" ≔ dense_order_class_type;
builtin "dense_linorder_class_type default_display" ≔ dense_linorder_class_type;
builtin "class_dense_order_axioms" ≔ class_dense_order_axioms;
builtin "class_dense_order_axioms_def" ≔ class_dense_order_axioms_def;
builtin "dense_order_class" ≔ dense_order_class;
builtin "dense_order_class_def" ≔ dense_order_class_def;
builtin "dense_order_class_type_def" ≔ dense_order_class_type_def;
builtin "dense_linorder_class" ≔ dense_linorder_class;
builtin "dense_linorder_class_def" ≔ dense_linorder_class_def;
builtin "dense_linorder_class_type_def" ≔ dense_linorder_class_type_def;

builtin "no_top_class_type default_display" ≔ no_top_class_type;
builtin "class_no_top_axioms" ≔ class_no_top_axioms;
builtin "class_no_top_axioms_def" ≔ class_no_top_axioms_def;
builtin "no_top_class" ≔ no_top_class;
builtin "no_top_class_def" ≔ no_top_class_def;
builtin "no_top_class_type_def" ≔ no_top_class_type_def;

builtin "no_bot_class_type default_display" ≔ no_bot_class_type;
builtin "unbounded_dense_linorder_class_type default_display" ≔ unbounded_dense_linorder_class_type;
builtin "class_no_bot_axioms" ≔ class_no_bot_axioms;
builtin "class_no_bot_axioms_def" ≔ class_no_bot_axioms_def;
builtin "no_bot_class" ≔ no_bot_class;
builtin "no_bot_class_def" ≔ no_bot_class_def;
builtin "no_bot_class_type_def" ≔ no_bot_class_type_def;
builtin "unbounded_dense_linorder_class" ≔ unbounded_dense_linorder_class;
builtin "unbounded_dense_linorder_class_def" ≔ unbounded_dense_linorder_class_def;
builtin "unbounded_dense_linorder_class_type_def" ≔ unbounded_dense_linorder_class_type_def;

builtin "wellorder_class_type default_display" ≔ wellorder_class_type;
builtin "well_founded" ≔ class_wellorder_axioms;
builtin "class_wellorder_axioms_def" ≔ class_wellorder_axioms_def;
builtin "wellorder_class" ≔ wellorder_class;
builtin "wellorder_class_def" ≔ wellorder_class_def;
builtin "wellorder_class_type_def" ≔ wellorder_class_type_def;

/* instances */
builtin "ord_class_pred_of_type" ≔ ord_class_pred_of_type;
builtin "preorder_class_pred_of_type" ≔ preorder_class_pred_of_type;
builtin "order_class_pred_of_type" ≔ order_class_pred_of_type;
builtin "linorder_class_pred_of_type" ≔ linorder_class_pred_of_type;
builtin "bot_class_pred_of_type" ≔ bot_class_pred_of_type;
builtin "order_bot_class_pred_of_type" ≔ order_bot_class_pred_of_type;
builtin "top_class_pred_of_type" ≔ top_class_pred_of_type;
builtin "order_top_class_pred_of_type" ≔ order_top_class_pred_of_type;
builtin "dense_order_class_pred_of_type" ≔ dense_order_class_pred_of_type;
builtin "dense_linorder_class_pred_of_type" ≔ dense_linorder_class_pred_of_type;
builtin "no_top_class_pred_of_type" ≔ no_top_class_pred_of_type;
builtin "no_bot_class_pred_of_type" ≔ no_bot_class_pred_of_type;
builtin "unbounded_dense_linorder_class_pred_of_type" ≔ unbounded_dense_linorder_class_pred_of_type;
builtin "wellorder_class_pred_of_type" ≔ wellorder_class_pred_of_type;


builtin "ord_class_pred_of_order_bot_class_pred" ≔ ord_class_pred_of_order_bot_class_pred;
builtin "bot_class_pred_of_order_bot_class_pred" ≔ bot_class_pred_of_order_bot_class_pred;
builtin "ord_class_pred_of_order_top_class_pred" ≔ ord_class_pred_of_order_top_class_pred;
builtin "top_class_pred_of_order_top_class_pred" ≔ top_class_pred_of_order_top_class_pred;

builtin "bool_bot_pred_instance" ≔ bool_bot_pred_instance;
builtin "bool_ord_pred_instance" ≔ bool_ord_pred_instance;
builtin "bool_order_bot_pred_instance" ≔ bool_order_bot_pred_instance;
builtin "bool_order_top_pred_instance" ≔ bool_order_top_pred_instance;
builtin "bool_top_pred_instance" ≔ bool_top_pred_instance;

builtin "fun_bot_pred_instance" ≔ fun_bot_pred_instance;
builtin "fun_ord_pred_instance" ≔ fun_ord_pred_instance;
builtin "fun_order_bot_pred_instance" ≔ fun_order_bot_pred_instance;
builtin "fun_order_top_pred_instance" ≔ fun_order_top_pred_instance;
builtin "fun_top_pred_instance" ≔ fun_top_pred_instance;

builtin "imp" ≔ ord_bool_inst_less_eq_bool;
builtin "ord_bool_inst_less_eq_bool_def" ≔ ord_bool_inst_less_eq_bool_def;
builtin "ord_bool_inst_less_bool" ≔ ord_bool_inst_less_bool;
builtin "ord_bool_inst_less_bool_def" ≔ ord_bool_inst_less_bool_def;
builtin "False" ≔ bot_bool_inst_bot_bool;
builtin "bot_bool_inst_bot_bool_def" ≔ bot_bool_inst_bot_bool_def;
builtin "True" ≔ top_bool_inst_top_bool;
builtin "top_bool_inst_top_bool_def" ≔ top_bool_inst_top_bool_def;

builtin "ord_fun_inst_less_eq_fun" ≔ ord_fun_inst_less_eq_fun;
builtin "ord_fun_inst_less_eq_fun_def" ≔ ord_fun_inst_less_eq_fun_def;
builtin "le_fun_def_raw" ≔ le_fun_def_raw;
builtin "ord_fun_inst_less_fun" ≔ ord_fun_inst_less_fun;
builtin "ord_fun_inst_less_fun_def" ≔ ord_fun_inst_less_fun_def;
builtin "less_fun_def_raw" ≔ less_fun_def_raw;
builtin "bot_fun_inst_bot_fun" ≔ bot_fun_inst_bot_fun;
builtin "bot_fun_inst_bot_fun_def" ≔ bot_fun_inst_bot_fun_def;
builtin "top_fun_inst_top_fun" ≔ top_fun_inst_top_fun;
builtin "top_fun_inst_top_fun_def" ≔ top_fun_inst_top_fun_def;

/****************************************************************************/
/* HOL.Groups */
/****************************************************************************/

/* typeclasses */
builtin "zero_class_pred" ≔ zero_class_pred;
builtin "Algebra.ChoiceBaseAddUMagma.type" ≔ zero_class_type;
builtin "zero_class_zero" ≔ zero_class_zero;
builtin "@Algebra.zero" ≔ zero_class_zero_alt;
builtin "zero_class" ≔ zero_class;
builtin "zero_class_def" ≔ zero_class_def;
builtin "zero_class_type_def" ≔ zero_class_type_def;

builtin "one_class_pred" ≔ one_class_pred;
builtin "one_class_type" ≔ one_class_type;
builtin "one_class_one" ≔ one_class_one;
builtin "@monoid.one" ≔ one_class_one_alt;
builtin "one_class" ≔ one_class;
builtin "one_class_def" ≔ one_class_def;
builtin "one_class_type_def" ≔ one_class_type_def;

builtin "plus_class_pred" ≔ plus_class_pred;
builtin "plus_class_type" ≔ plus_class_type;
builtin "plus" ≔ plus_class_plus;
builtin "Algebra.add" ≔ plus_class_plus_alt;
builtin "plus_class" ≔ plus_class;
builtin "plus_class_def" ≔ plus_class_def;
builtin "plus_class_type_def" ≔ plus_class_type_def;

builtin "minus_class_pred" ≔ minus_class_pred;
builtin "zmodType" ≔ minus_class_type;
builtin "minus" ≔ minus_class_minus;
builtin "subtract" ≔ minus_class_minus_alt;
builtin "minus_class" ≔ minus_class;
builtin "minus_class_def" ≔ minus_class_def;
builtin "minus_class_type_def" ≔ minus_class_type_def;

builtin "uminus_class_pred" ≔ uminus_class_pred;
builtin "zmodType" ≔ uminus_class_type;
builtin "uminus" ≔ uminus_class_uminus;
builtin "Algebra.opp" ≔ uminus_class_uminus_alt;
builtin "uminus_class" ≔ uminus_class;
builtin "uminus_class_def" ≔ uminus_class_def;
builtin "uminus_class_type_def" ≔ uminus_class_type_def;

builtin "times_class_pred" ≔ times_class_pred;
builtin "times_class_type" ≔ times_class_type;
builtin "times" ≔ times_class_times;
builtin "mul" ≔ times_class_times_alt;
builtin "times_class" ≔ times_class;
builtin "times_class_def" ≔ times_class_def;
builtin "times_class_type_def" ≔ times_class_type_def;

builtin "semigroup_add_class_type" ≔ semigroup_add_class_type;
builtin "ssrfun.associative" ≔ class_semigroup_add;
builtin "class_semigroup_add_def" ≔ class_semigroup_add_def;
builtin "semigroup_add_class" ≔ semigroup_add_class;
builtin "semigroup_add_class_type_def" ≔ semigroup_add_class_type_def;
builtin "semigroup_add_class_def" ≔ semigroup_add_class_def;

builtin "nmodType" ≔ ab_semigroup_add_class_type;
builtin "ssrfun.commutative _" ≔ class_ab_semigroup_add_axioms;
builtin "class_ab_semigroup_add_axioms_def" ≔ class_ab_semigroup_add_axioms_def;
builtin "ab_semigroup_add_class" ≔ ab_semigroup_add_class;
builtin "ab_semigroup_add_class_type_def" ≔ ab_semigroup_add_class_type_def;
builtin "ab_semigroup_add_class_def" ≔ ab_semigroup_add_class_def;

builtin "semigroup_mult_class_type" ≔ semigroup_mult_class_type;
builtin "ssrfun.associative" ≔ class_semigroup_mult;
builtin "class_semigroup_mult_def" ≔ class_semigroup_mult_def;
builtin "semigroup_mult_class" ≔ semigroup_mult_class;
builtin "semigroup_mult_class_type_def" ≔ semigroup_mult_class_type_def;
builtin "semigroup_mult_class_def" ≔ semigroup_mult_class_def;

builtin "ab_semigroup_mult_class_type" ≔ ab_semigroup_mult_class_type;
builtin "ssrfun.commutative _" ≔ class_ab_semigroup_mult_axioms;
builtin "class_ab_semigroup_mult_axioms_def" ≔ class_ab_semigroup_mult_axioms_def;
builtin "ab_semigroup_mult_class" ≔ ab_semigroup_mult_class;
builtin "ab_semigroup_mult_class_type_def" ≔ ab_semigroup_mult_class_type_def;
builtin "ab_semigroup_mult_class_def" ≔ ab_semigroup_mult_class_def;

builtin "nmodType" ≔ monoid_add_class_type;
builtin "class_monoid_add_axioms" ≔ class_monoid_add_axioms;
builtin "class_monoid_add_axioms_def" ≔ class_monoid_add_axioms_def;
builtin "monoid_add_class" ≔ monoid_add_class;
builtin "monoid_add_class_type_def" ≔ monoid_add_class_type_def;
builtin "monoid_add_class_def" ≔ monoid_add_class_def;

builtin "nmodType" ≔ comm_monoid_add_class_type;
builtin "class_comm_monoid_add_axioms" ≔ class_comm_monoid_add_axioms;
builtin "class_comm_monoid_add_axioms_def" ≔ class_comm_monoid_add_axioms_def;
builtin "comm_monoid_add_class" ≔ comm_monoid_add_class;
builtin "comm_monoid_add_class_type_def" ≔ comm_monoid_add_class_type_def;
builtin "comm_monoid_add_class_def" ≔ comm_monoid_add_class_def;

builtin "monoid_mult_class_type" ≔ monoid_mult_class_type;
builtin "class_monoid_mult_axioms" ≔ class_monoid_mult_axioms;
builtin "class_monoid_mult_axioms_def" ≔ class_monoid_mult_axioms_def;
builtin "monoid_mult_class" ≔ monoid_mult_class;
builtin "monoid_mult_class_type_def" ≔ monoid_mult_class_type_def;
builtin "monoid_mult_class_def" ≔ monoid_mult_class_def;

builtin "comm_monoid_mult_class_type" ≔ comm_monoid_mult_class_type;
builtin "class_comm_monoid_mult_axioms" ≔ class_comm_monoid_mult_axioms;
builtin "class_comm_monoid_mult_axioms_def" ≔ class_comm_monoid_mult_axioms_def;
builtin "comm_monoid_mult_class" ≔ comm_monoid_mult_class;
builtin "comm_monoid_mult_class_type_def" ≔ comm_monoid_mult_class_type_def;
builtin "comm_monoid_mult_class_def" ≔ comm_monoid_mult_class_def;

builtin "zmodType" ≔ cancel_semigroup_add_class_type;
builtin "class_cancel_semigroup_add_axioms" ≔ class_cancel_semigroup_add_axioms;
builtin "class_cancel_semigroup_add_axioms_def" ≔ class_cancel_semigroup_add_axioms_def;
builtin "cancel_semigroup_add_class" ≔ cancel_semigroup_add_class;
builtin "cancel_semigroup_add_class_type_def" ≔ cancel_semigroup_add_class_type_def;
builtin "cancel_semigroup_add_class_def" ≔ cancel_semigroup_add_class_def;

builtin "zmodType" ≔ cancel_ab_semigroup_add_class_type;
builtin "class_cancel_ab_semigroup_add_axioms" ≔ class_cancel_ab_semigroup_add_axioms;
builtin "class_cancel_ab_semigroup_add_axioms_def" ≔ class_cancel_ab_semigroup_add_axioms_def;
builtin "cancel_ab_semigroup_add_class" ≔ cancel_ab_semigroup_add_class;
builtin "cancel_ab_semigroup_add_class_type_def" ≔ cancel_ab_semigroup_add_class_type_def;
builtin "cancel_ab_semigroup_add_class_def" ≔ cancel_ab_semigroup_add_class_def;

builtin "zmodType" ≔ cancel_comm_monoid_add_class_type;
builtin "cancel_comm_monoid_add_class" ≔ cancel_comm_monoid_add_class;
builtin "cancel_comm_monoid_add_class_def" ≔ cancel_comm_monoid_add_class_def;
builtin "cancel_comm_monoid_add_class_type_def" ≔ cancel_comm_monoid_add_class_type_def;

builtin "comm_monoid_diff_class_type" ≔ comm_monoid_diff_class_type;
builtin "class_comm_monoid_diff_axioms" ≔ class_comm_monoid_diff_axioms;
builtin "class_comm_monoid_diff_axioms_def" ≔ class_comm_monoid_diff_axioms_def;
builtin "comm_monoid_diff_class" ≔ comm_monoid_diff_class;
builtin "comm_monoid_diff_class_def" ≔ comm_monoid_diff_class_def;
builtin "comm_monoid_diff_class_type_def" ≔ comm_monoid_diff_class_type_def;

builtin "zmodType" ≔ group_add_class_type;
builtin "class_group_add_axioms" ≔ class_group_add_axioms;
builtin "class_group_add_axioms_def" ≔ class_group_add_axioms_def;
builtin "group_add_class" ≔ group_add_class;
builtin "group_add_class_def" ≔ group_add_class_def;
builtin "group_add_class_type_def" ≔ group_add_class_type_def;

builtin "zmodType" ≔ ab_group_add_class_type;
builtin "class_ab_group_add_axioms" ≔ class_ab_group_add_axioms;
builtin "class_ab_group_add_axioms_def" ≔ class_ab_group_add_axioms_def;
builtin "ab_group_add_class" ≔ ab_group_add_class;
builtin "ab_group_add_class_def" ≔ ab_group_add_class_def;
builtin "ab_group_add_class_type_def" ≔ ab_group_add_class_type_def;

builtin "porderedNmodType" ≔ ordered_ab_semigroup_add_class_type;
builtin "class_ordered_ab_semigroup_add_axioms" ≔ class_ordered_ab_semigroup_add_axioms;
builtin "class_ordered_ab_semigroup_add_axioms_def" ≔ class_ordered_ab_semigroup_add_axioms_def;
builtin "ordered_ab_semigroup_add_class" ≔ ordered_ab_semigroup_add_class;
builtin "ordered_ab_semigroup_add_class_def" ≔ ordered_ab_semigroup_add_class_def;
builtin "ordered_ab_semigroup_add_class_type_def" ≔ ordered_ab_semigroup_add_class_type_def;

builtin "porderedZmodType" ≔ strict_ordered_ab_semigroup_add_class_type;
builtin "class_strict_ordered_ab_semigroup_add_axioms" ≔ class_strict_ordered_ab_semigroup_add_axioms;
builtin "class_strict_ordered_ab_semigroup_add_axioms_def" ≔ class_strict_ordered_ab_semigroup_add_axioms_def;
builtin "strict_ordered_ab_semigroup_add_class" ≔ strict_ordered_ab_semigroup_add_class;
builtin "strict_ordered_ab_semigroup_add_class_def" ≔ strict_ordered_ab_semigroup_add_class_def;
builtin "strict_ordered_ab_semigroup_add_class_type_def" ≔ strict_ordered_ab_semigroup_add_class_type_def;

builtin "porderedZmodType" ≔ ordered_cancel_ab_semigroup_add_class_type;
builtin "ordered_cancel_ab_semigroup_add_class" ≔ ordered_cancel_ab_semigroup_add_class;
builtin "ordered_cancel_ab_semigroup_add_class_def" ≔ ordered_cancel_ab_semigroup_add_class_def;
builtin "ordered_cancel_ab_semigroup_add_class_type_def" ≔ ordered_cancel_ab_semigroup_add_class_type_def;

builtin "porderedZmodType" ≔ ordered_ab_semigroup_add_imp_le_class_type;
builtin "class_ordered_ab_semigroup_add_imp_le_axioms" ≔ class_ordered_ab_semigroup_add_imp_le_axioms;
builtin "class_ordered_ab_semigroup_add_imp_le_axioms_def" ≔ class_ordered_ab_semigroup_add_imp_le_axioms_def;
builtin "ordered_ab_semigroup_add_imp_le_class" ≔ ordered_ab_semigroup_add_imp_le_class;
builtin "ordered_ab_semigroup_add_imp_le_class_def" ≔ ordered_ab_semigroup_add_imp_le_class_def;
builtin "ordered_ab_semigroup_add_imp_le_class_type_def" ≔ ordered_ab_semigroup_add_imp_le_class_type_def;

builtin "porderedNmodType" ≔ ordered_comm_monoid_add_class_type;
builtin "ordered_comm_monoid_add_class" ≔ ordered_comm_monoid_add_class;
builtin "ordered_comm_monoid_add_class_type_def" ≔ ordered_comm_monoid_add_class_type_def;
builtin "ordered_comm_monoid_add_class_def" ≔ ordered_comm_monoid_add_class_def;

builtin "porderedZmodType" ≔ strict_ordered_comm_monoid_add_class_type;
builtin "strict_ordered_comm_monoid_add_class" ≔ strict_ordered_comm_monoid_add_class;
builtin "strict_ordered_comm_monoid_add_class_type_def" ≔ strict_ordered_comm_monoid_add_class_type_def;
builtin "strict_ordered_comm_monoid_add_class_def" ≔ strict_ordered_comm_monoid_add_class_def;

builtin "porderedZmodType" ≔ ordered_cancel_comm_monoid_add_class_type;
builtin "ordered_cancel_comm_monoid_add_class"  ≔ ordered_cancel_comm_monoid_add_class;
builtin "ordered_cancel_comm_monoid_add_class_type_def" ≔ ordered_cancel_comm_monoid_add_class_type_def;
builtin "ordered_cancel_comm_monoid_add_class_def" ≔ ordered_cancel_comm_monoid_add_class_def;

builtin "porderedZmodType" ≔ ordered_ab_semigroup_monoid_add_imp_le_class_type;
builtin "ordered_ab_semigroup_monoid_add_imp_le_class"  ≔ ordered_ab_semigroup_monoid_add_imp_le_class;
builtin "ordered_ab_semigroup_monoid_add_imp_le_class_type_def" ≔ ordered_ab_semigroup_monoid_add_imp_le_class_type_def;
builtin "ordered_ab_semigroup_monoid_add_imp_le_class_def" ≔ ordered_ab_semigroup_monoid_add_imp_le_class_def;

builtin "porderedZmodType" ≔ ordered_ab_group_add_class_type;
builtin "ordered_ab_group_add_class"  ≔ ordered_ab_group_add_class;
builtin "ordered_ab_group_add_class_type_def" ≔ ordered_ab_group_add_class_type_def;
builtin "ordered_ab_group_add_class_def" ≔ ordered_ab_group_add_class_def;

builtin "orderedNmodType" ≔ linordered_ab_semigroup_add_class_type;
builtin "linordered_ab_semigroup_add_class"  ≔ linordered_ab_semigroup_add_class;
builtin "linordered_ab_semigroup_add_class_type_def" ≔ linordered_ab_semigroup_add_class_type_def;
builtin "linordered_ab_semigroup_add_class_def" ≔ linordered_ab_semigroup_add_class_def;

builtin "orderedZmodType" ≔ linordered_cancel_ab_semigroup_add_class_type;
builtin "linordered_cancel_ab_semigroup_add_class"  ≔ linordered_cancel_ab_semigroup_add_class;
builtin "linordered_cancel_ab_semigroup_add_class_type_def" ≔ linordered_cancel_ab_semigroup_add_class_type_def;
builtin "linordered_cancel_ab_semigroup_add_class_def" ≔ linordered_cancel_ab_semigroup_add_class_def;

builtin "orderedZmodType" ≔ linordered_ab_group_add_class_type;
builtin "linordered_ab_group_add_class"  ≔ linordered_ab_group_add_class;
builtin "linordered_ab_group_add_class_type_def" ≔ linordered_ab_group_add_class_type_def;
builtin "linordered_ab_group_add_class_def" ≔ linordered_ab_group_add_class_def;

builtin "abs_class_pred" ≔ abs_class_pred;
builtin "abs_class" ≔ abs_class;
builtin "numDomainType" ≔ abs_class_type;
builtin "abs_class_type_def" ≔ abs_class_type_def;
builtin "abs_class_def" ≔ abs_class_def;
builtin "abs" ≔ abs_class_abs;
builtin "Num.norm _" ≔ abs_class_abs_alt;

builtin "sgn_class_pred" ≔ sgn_class_pred;
builtin "sgn_class" ≔ sgn_class;
builtin "numDomainType" ≔ sgn_class_type;
builtin "sgn_class_type_def" ≔ sgn_class_type_def;
builtin "sgn_class_def" ≔ sgn_class_def;
builtin "sgn" ≔ sgn_class_sgn;
builtin "Num.Def.sgr _" ≔ sgn_class_sgn_alt;

builtin "realDomainType" ≔ ordered_ab_group_add_abs_class_type;
builtin "class_ordered_ab_group_add_abs_axioms" ≔ class_ordered_ab_group_add_abs_axioms;
builtin "class_ordered_ab_group_add_abs_axioms_def" ≔ class_ordered_ab_group_add_abs_axioms_def;
builtin "ordered_ab_group_add_abs_class" ≔ ordered_ab_group_add_abs_class;
builtin "ordered_ab_group_add_abs_class_type_def" ≔ ordered_ab_group_add_abs_class_type_def;
builtin "ordered_ab_group_add_abs_class_def" ≔ ordered_ab_group_add_abs_class_def;

builtin "canonically_ordered_monoid_add_class_type" ≔ canonically_ordered_monoid_add_class_type;
builtin "class_canonically_ordered_monoid_add_axioms" ≔ class_canonically_ordered_monoid_add_axioms;
builtin "class_canonically_ordered_monoid_add_axioms_def" ≔ class_canonically_ordered_monoid_add_axioms_def;
builtin "canonically_ordered_monoid_add_class" ≔ canonically_ordered_monoid_add_class;
builtin "canonically_ordered_monoid_add_class_type_def" ≔ canonically_ordered_monoid_add_class_type_def;
builtin "canonically_ordered_monoid_add_class_def" ≔ canonically_ordered_monoid_add_class_def;

builtin "comm_monoid_diff_class_type" ≔ ordered_cancel_comm_monoid_diff_class_type;
builtin "ordered_cancel_comm_monoid_diff_class" ≔ ordered_cancel_comm_monoid_diff_class;
builtin "ordered_cancel_comm_monoid_diff_class_type_def" ≔ ordered_cancel_comm_monoid_diff_class_type_def;
builtin "ordered_cancel_comm_monoid_diff_class_def" ≔ ordered_cancel_comm_monoid_diff_class_def;

builtin "monoid_mult_class_pred" ≔ monoid_mult_class_pred;
builtin "monoid_add_class_pred" ≔ monoid_add_class_pred;
builtin "cancel_ab_semigroup_add_class_pred" ≔ cancel_ab_semigroup_add_class_pred;
builtin "cancel_comm_monoid_add_class_pred" ≔ cancel_comm_monoid_add_class_pred;
builtin "group_add_class_pred" ≔ group_add_class_pred;
builtin "ordered_ab_semigroup_add_class_pred" ≔ ordered_ab_semigroup_add_class_pred;
builtin "ordered_comm_monoid_add_class_pred" ≔ ordered_comm_monoid_add_class_pred;
builtin "ordered_cancel_ab_semigroup_add_class_pred" ≔ ordered_cancel_ab_semigroup_add_class_pred;
builtin "ordered_cancel_comm_monoid_add_class_pred" ≔ ordered_cancel_comm_monoid_add_class_pred;
builtin "ordered_ab_group_add_class_pred" ≔ ordered_ab_group_add_class_pred;
builtin "ordered_ab_group_add_abs_class_pred" ≔ ordered_ab_group_add_abs_class_pred;

builtin "ssrfun.associative" ≔ semigroup;
builtin "semigroup_def" ≔ semigroup_def;

builtin "ssrfun.commutative _" ≔ abel_semigroup_axioms;
builtin "abel_semigroup_axioms_def" ≔ abel_semigroup_axioms_def;

builtin "abel_semigroup" ≔ abel_semigroup;
builtin "abel_semigroup_def" ≔ abel_semigroup_def;

builtin "monoid_axioms" ≔ monoid_axioms;
builtin "monoid_axioms_def" ≔ monoid_axioms_def;

builtin "monoid" ≔ monoid;
builtin "monoid_def" ≔ monoid_def;

builtin "comm_monoid_axioms" ≔ comm_monoid_axioms;
builtin "comm_monoid_axioms_def" ≔ comm_monoid_axioms_def;

builtin "comm_monoid" ≔ comm_monoid;
builtin "comm_monoid_def" ≔ comm_monoid_def;

builtin "group_axioms" ≔ group_axioms;
builtin "group_axioms_def" ≔ group_axioms_def;

builtin "group" ≔ group;
builtin "group_def" ≔ group_def;

/* instances */

builtin "minus_class_pred_of_cancel_ab_semigroup_add_class_pred" ≔ minus_class_pred_of_cancel_ab_semigroup_add_class_pred;
builtin "plus_class_pred_of_cancel_ab_semigroup_add_class_pred" ≔ plus_class_pred_of_cancel_ab_semigroup_add_class_pred;
builtin "cancel_ab_semigroup_add_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ cancel_ab_semigroup_add_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "abs_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ abs_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "minus_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ minus_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "ordered_ab_group_add_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ ordered_ab_group_add_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "monoid_add_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ monoid_add_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "ordered_cancel_comm_monoid_add_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ ordered_cancel_comm_monoid_add_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "ordered_comm_monoid_add_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ ordered_comm_monoid_add_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "zero_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ zero_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "uminus_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ uminus_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "ordered_cancel_ab_semigroup_add_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ ordered_cancel_ab_semigroup_add_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "group_add_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ group_add_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "cancel_comm_monoid_add_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ cancel_comm_monoid_add_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "ord_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ ord_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "ordered_ab_semigroup_add_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ ordered_ab_semigroup_add_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "plus_class_pred_of_ordered_ab_group_add_abs_class_pred" ≔ plus_class_pred_of_ordered_ab_group_add_abs_class_pred;
builtin "cancel_ab_semigroup_add_class_pred_of_ordered_ab_group_add_class_pred" ≔ cancel_ab_semigroup_add_class_pred_of_ordered_ab_group_add_class_pred;
builtin "minus_class_pred_of_ordered_ab_group_add_class_pred" ≔ minus_class_pred_of_ordered_ab_group_add_class_pred;
builtin "monoid_add_class_pred_of_ordered_ab_group_add_class_pred" ≔ monoid_add_class_pred_of_ordered_ab_group_add_class_pred;
builtin "ordered_cancel_comm_monoid_add_class_pred_of_ordered_ab_group_add_class_pred" ≔ ordered_cancel_comm_monoid_add_class_pred_of_ordered_ab_group_add_class_pred;
builtin "ordered_comm_monoid_add_class_pred_of_ordered_ab_group_add_class_pred" ≔ ordered_comm_monoid_add_class_pred_of_ordered_ab_group_add_class_pred;
builtin "zero_class_pred_of_ordered_ab_group_add_class_pred" ≔ zero_class_pred_of_ordered_ab_group_add_class_pred;
builtin "uminus_class_pred_of_ordered_ab_group_add_class_pred" ≔ uminus_class_pred_of_ordered_ab_group_add_class_pred;
builtin "ordered_cancel_ab_semigroup_add_class_pred_of_ordered_ab_group_add_class_pred" ≔ ordered_cancel_ab_semigroup_add_class_pred_of_ordered_ab_group_add_class_pred;
builtin "group_add_class_pred_of_ordered_ab_group_add_class_pred" ≔ group_add_class_pred_of_ordered_ab_group_add_class_pred;
builtin "cancel_comm_monoid_add_class_pred_of_ordered_ab_group_add_class_pred" ≔ cancel_comm_monoid_add_class_pred_of_ordered_ab_group_add_class_pred;
builtin "ord_class_pred_of_ordered_ab_group_add_class_pred" ≔ ord_class_pred_of_ordered_ab_group_add_class_pred;
builtin "ordered_ab_semigroup_add_class_pred_of_ordered_ab_group_add_class_pred" ≔ ordered_ab_semigroup_add_class_pred_of_ordered_ab_group_add_class_pred;
builtin "plus_class_pred_of_ordered_ab_group_add_class_pred" ≔ plus_class_pred_of_ordered_ab_group_add_class_pred;
builtin "zero_class_pred_of_monoid_add_class_pred" ≔ zero_class_pred_of_monoid_add_class_pred;
builtin "plus_class_pred_of_monoid_add_class_pred" ≔ plus_class_pred_of_monoid_add_class_pred;
builtin "cancel_ab_semigroup_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred" ≔ cancel_ab_semigroup_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred;
builtin "minus_class_pred_of_ordered_cancel_comm_monoid_add_class_pred" ≔ minus_class_pred_of_ordered_cancel_comm_monoid_add_class_pred;
builtin "monoid_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred" ≔ monoid_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred;
builtin "ordered_comm_monoid_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred" ≔ ordered_comm_monoid_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred;
builtin "zero_class_pred_of_ordered_cancel_comm_monoid_add_class_pred" ≔ zero_class_pred_of_ordered_cancel_comm_monoid_add_class_pred;
builtin "ordered_cancel_ab_semigroup_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred" ≔ ordered_cancel_ab_semigroup_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred;
builtin "cancel_comm_monoid_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred" ≔ cancel_comm_monoid_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred;
builtin "ord_class_pred_of_ordered_cancel_comm_monoid_add_class_pred" ≔ ord_class_pred_of_ordered_cancel_comm_monoid_add_class_pred;
builtin "ordered_ab_semigroup_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred" ≔ ordered_ab_semigroup_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred;
builtin "plus_class_pred_of_ordered_cancel_comm_monoid_add_class_pred" ≔ plus_class_pred_of_ordered_cancel_comm_monoid_add_class_pred;
builtin "monoid_add_class_pred_of_ordered_comm_monoid_add_class_pred" ≔ monoid_add_class_pred_of_ordered_comm_monoid_add_class_pred;
builtin "zero_class_pred_of_ordered_comm_monoid_add_class_pred" ≔ zero_class_pred_of_ordered_comm_monoid_add_class_pred;
builtin "ord_class_pred_of_ordered_comm_monoid_add_class_pred" ≔ ord_class_pred_of_ordered_comm_monoid_add_class_pred;
builtin "ordered_ab_semigroup_add_class_pred_of_ordered_comm_monoid_add_class_pred" ≔ ordered_ab_semigroup_add_class_pred_of_ordered_comm_monoid_add_class_pred;
builtin "plus_class_pred_of_ordered_comm_monoid_add_class_pred" ≔ plus_class_pred_of_ordered_comm_monoid_add_class_pred;
builtin "cancel_ab_semigroup_add_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred" ≔ cancel_ab_semigroup_add_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred;
builtin "minus_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred" ≔ minus_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred;
builtin "ord_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred" ≔ ord_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred;
builtin "ordered_ab_semigroup_add_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred" ≔ ordered_ab_semigroup_add_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred;
builtin "plus_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred" ≔ plus_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred;
builtin "one_class_pred_of_monoid_mult_class_pred" ≔ one_class_pred_of_monoid_mult_class_pred;
builtin "times_class_pred_of_monoid_mult_class_pred" ≔ times_class_pred_of_monoid_mult_class_pred;
builtin "cancel_ab_semigroup_add_class_pred_of_group_add_class_pred" ≔ cancel_ab_semigroup_add_class_pred_of_group_add_class_pred;
builtin "minus_class_pred_of_group_add_class_pred" ≔ minus_class_pred_of_group_add_class_pred;
builtin "monoid_add_class_pred_of_group_add_class_pred" ≔ monoid_add_class_pred_of_group_add_class_pred;
builtin "zero_class_pred_of_group_add_class_pred" ≔ zero_class_pred_of_group_add_class_pred;
builtin "uminus_class_pred_of_group_add_class_pred" ≔ uminus_class_pred_of_group_add_class_pred;
builtin "cancel_comm_monoid_add_class_pred_of_group_add_class_pred" ≔ cancel_comm_monoid_add_class_pred_of_group_add_class_pred;
builtin "plus_class_pred_of_group_add_class_pred" ≔ plus_class_pred_of_group_add_class_pred;
builtin "cancel_ab_semigroup_add_class_pred_of_cancel_comm_monoid_add_class_pred" ≔ cancel_ab_semigroup_add_class_pred_of_cancel_comm_monoid_add_class_pred;
builtin "minus_class_pred_of_cancel_comm_monoid_add_class_pred" ≔ minus_class_pred_of_cancel_comm_monoid_add_class_pred;
builtin "monoid_add_class_pred_of_cancel_comm_monoid_add_class_pred" ≔ monoid_add_class_pred_of_cancel_comm_monoid_add_class_pred;
builtin "zero_class_pred_of_cancel_comm_monoid_add_class_pred" ≔ zero_class_pred_of_cancel_comm_monoid_add_class_pred;
builtin "plus_class_pred_of_cancel_comm_monoid_add_class_pred" ≔ plus_class_pred_of_cancel_comm_monoid_add_class_pred;
builtin "ord_class_pred_of_ordered_ab_semigroup_add_class_pred" ≔ ord_class_pred_of_ordered_ab_semigroup_add_class_pred;
builtin "plus_class_pred_of_ordered_ab_semigroup_add_class_pred" ≔ plus_class_pred_of_ordered_ab_semigroup_add_class_pred;
builtin "zero_class_pred_of_type" ≔ zero_class_pred_of_type;
builtin "one_class_pred_of_type" ≔ one_class_pred_of_type;
builtin "plus_class_pred_of_type" ≔ plus_class_pred_of_type;
builtin "minus_class_pred_of_type" ≔ minus_class_pred_of_type;
builtin "uminus_class_pred_of_type" ≔ uminus_class_pred_of_type;
builtin "times_class_pred_of_type" ≔ times_class_pred_of_type;
builtin "semigroup_add_class_pred_of_type" ≔ semigroup_add_class_pred_of_type;
builtin "ab_semigroup_add_class_pred_of_type" ≔ ab_semigroup_add_class_pred_of_type;
builtin "semigroup_mult_class_pred_of_type" ≔ semigroup_mult_class_pred_of_type;
builtin "ab_semigroup_mult_class_pred_of_type" ≔ ab_semigroup_mult_class_pred_of_type;
builtin "monoid_add_class_pred_of_type" ≔ monoid_add_class_pred_of_type;
builtin "comm_monoid_add_class_pred_of_type" ≔ comm_monoid_add_class_pred_of_type;
builtin "monoid_mult_class_pred_of_type" ≔ monoid_mult_class_pred_of_type;
builtin "comm_monoid_mult_class_pred_of_type" ≔ comm_monoid_mult_class_pred_of_type;
builtin "cancel_semigroup_add_class_pred_of_type" ≔ cancel_semigroup_add_class_pred_of_type;
builtin "cancel_ab_semigroup_add_class_pred_of_type" ≔ cancel_ab_semigroup_add_class_pred_of_type;
builtin "cancel_comm_monoid_add_class_pred_of_type" ≔ cancel_comm_monoid_add_class_pred_of_type;
builtin "comm_monoid_diff_class_pred_of_type" ≔ comm_monoid_diff_class_pred_of_type;
builtin "group_add_class_pred_of_type" ≔ group_add_class_pred_of_type;
builtin "ab_group_add_class_pred_of_type" ≔ ab_group_add_class_pred_of_type;
builtin "ordered_ab_semigroup_add_class_pred_of_type" ≔ ordered_ab_semigroup_add_class_pred_of_type;
builtin "strict_ordered_ab_semigroup_add_class_pred_of_type" ≔ strict_ordered_ab_semigroup_add_class_pred_of_type;
builtin "ordered_cancel_ab_semigroup_add_class_pred_of_type" ≔ ordered_cancel_ab_semigroup_add_class_pred_of_type;
builtin "ordered_ab_semigroup_add_imp_le_class_pred_of_type" ≔ ordered_ab_semigroup_add_imp_le_class_pred_of_type;
builtin "ordered_comm_monoid_add_class_pred_of_type" ≔ ordered_comm_monoid_add_class_pred_of_type;
builtin "strict_ordered_comm_monoid_add_class_pred_of_type" ≔ strict_ordered_comm_monoid_add_class_pred_of_type;
builtin "ordered_cancel_comm_monoid_add_class_pred_of_type" ≔ ordered_cancel_comm_monoid_add_class_pred_of_type;
builtin "ordered_ab_semigroup_monoid_add_imp_le_class_pred_of_type" ≔ ordered_ab_semigroup_monoid_add_imp_le_class_pred_of_type;
builtin "ordered_ab_group_add_class_pred_of_type" ≔ ordered_ab_group_add_class_pred_of_type;
builtin "linordered_ab_semigroup_add_class_pred_of_type" ≔ linordered_ab_semigroup_add_class_pred_of_type;
builtin "linordered_cancel_ab_semigroup_add_class_pred_of_type" ≔ linordered_cancel_ab_semigroup_add_class_pred_of_type;
builtin "linordered_ab_group_add_class_pred_of_type" ≔ linordered_ab_group_add_class_pred_of_type;
builtin "abs_class_pred_of_type" ≔ abs_class_pred_of_type;
builtin "sgn_class_pred_of_type" ≔ sgn_class_pred_of_type;
builtin "ordered_ab_group_add_abs_class_pred_of_type" ≔ ordered_ab_group_add_abs_class_pred_of_type;
builtin "canonically_ordered_monoid_add_class_pred_of_type" ≔ canonically_ordered_monoid_add_class_pred_of_type;
builtin "ordered_cancel_comm_monoid_diff_class_pred_of_type" ≔ ordered_cancel_comm_monoid_diff_class_pred_of_type;