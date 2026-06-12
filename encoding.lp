// dk/lp symbols used for encoding simple type theory

builtin "Set" ≔ STTfa.Set;
builtin "prop" ≔ STTfa.prop;
builtin "arr" ≔ STTfa.arr;
builtin "El" ≔ STTfa.El;
builtin "Prf" ≔ STTfa.Prf;

builtin "eq" ≔ Pure.eq;
builtin "not" ≔ HOL_HOL.Not;
builtin "imp" ≔ STTfa.imp;
builtin "and" ≔ HOL_HOL.conj;
builtin "or" ≔ HOL_HOL.disj;
builtin "all" ≔ STTfa.all;
builtin "ex" ≔ HOL_HOL.Ex;
