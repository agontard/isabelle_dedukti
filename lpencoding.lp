// dk/lp symbols used for encoding simple type theory

builtin "2 | ($1) -> $2" ≔ arr;
builtin "trivial 1" ≔ El;
builtin "trivial 1" ≔ Prf;
builtin "trivial 1" ≔ Trueprop;

builtin "3 | ($2) = ($3) :> ($1)" ≔ eq_const;
builtin "3 | ($2) = ($3) :> ($1)" ≔ eq;
builtin "1 | ~($1)" ≔ Not;
builtin "2 | ($1) -> $2" ≔ imp;
builtin "2 | ($1) -> $2" ≔ implies;
builtin "2 | ($1) /\ ($2)" ≔ conj;
builtin "2 | ($1) \/ ($2)" ≔ disj;
builtin "quantifier 2 | forall $x, $2" ≔ all;
builtin "quantifier 2 | forall $x, $2" ≔ All;
builtin "quantifier 2 | exists $x, $2" ≔ Ex;
builtin "quantifier 2 | exists! $x, $2" ≔ Ex1;

builtin "4 | if $2 : Prop then $3 else $4" ≔ ord_class_less_eq_alt;
builtin "enclosed 2 | True" ≔ term;
builtin "enclosed 2 | True" ≔ sort_constraint;
builtin "3 | ($2) = ($3) :> ($1)" ≔ equal_itself_inst_equal_itself;

builtin "enclosed 2 | True" ≔ type_class;
builtin "enclosed 2 | True" ≔ default_class;
builtin "enclosed 2 | True" ≔ ord_class;
builtin "enclosed 2 | True" ≔ bot_class;
builtin "enclosed 2 | True" ≔ top_class;
builtin "enclosed 2 | True" ≔ zero_class;
builtin "enclosed 2 | True" ≔ one_class;
builtin "enclosed 2 | True" ≔ plus_class;
builtin "enclosed 2 | True" ≔ times_class;
builtin "enclosed 2 | True" ≔ minus_class;
builtin "enclosed 2 | True" ≔ uminus_class;
builtin "enclosed 2 | True" ≔ abs_class;
builtin "enclosed 2 | True" ≔ sgn_class;

builtin "3 | ($2) <= ($3)" ≔ ord_class_less_eq_alt;
builtin "3 | ($2) < ($3)" ≔ ord_class_less_alt;
builtin "1 | 0" ≔ zero_class_zero_alt;
builtin "1 | 1" ≔ zero_class_1_alt;
builtin "3 | ($2) + ($3)" ≔ plus_class_plus_alt;
builtin "3 | ($2) * ($3)" ≔ times_class_times_alt;
builtin "3 | ($2) - ($3)" ≔ minus_class_minus_alt;
builtin "2 | -($2)" ≔ uminus_class_uminus_alt;
builtin "enclosed 2 | `| $2 : $1 |" ≔ abs_class_abs_alt;