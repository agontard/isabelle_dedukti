From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat.
From mathcomp Require Export ssrbool eqtype choice.
From mathcomp Require Import order seq monoid nmodule orderedzmod.
From mathcomp Require boolp.

(* Set the default display to ring display to be able to
   align ordered groups *)
Definition default_display : Order.disp_t.
Proof. exact: ring_display. Defined.

(* Override mathcomp declaration of function order with our own. *)

HB.instance Definition _ (T : Type) (T' : T -> eqType) :=
  boolp.gen_eqMixin (forall t : T, T' t).

HB.instance Definition _ (T : Type) (T' : T -> eqType) :=
  boolp.gen_choiceMixin (forall t : T, T' t).

Module FunOrder.

Local Notation asboolP := boolp.asboolP.
Local Notation not_existsP := boolp.not_existsP.
Local Notation funeqE := boolp.funeqE.
Local Notation funext := boolp.funext.

Section FunPreorder.
Import Order.TTheory.
Variables (aT : Type) (d : Order.disp_t) (T : preorderType d).
Local Notation "`[< P >]" := (boolp.asbool P).
Implicit Types f g h : aT -> T.

Definition lef f g := `[< forall x, (f x <= g x)%O >].
Local Notation "f <= g" := (lef f g).

Fact lef_refl : reflexive lef. Proof. by move=> f; apply/asboolP => x. Qed.

Fact lef_trans : transitive lef.
Proof.
move=> g f h /asboolP fg /asboolP gh; apply/asboolP => x.
by rewrite (le_trans (fg x)).
Qed.

#[export]
HB.instance Definition _ := @Order.Le_isPreorder.Build default_display
  (aT -> T) lef lef_refl lef_trans.
End FunPreorder.

Section FunOrder.
Import Order.TTheory.
Variables (aT : Type) (d : Order.disp_t) (T : porderType d).

Fact lef_anti : antisymmetric (<=%O : rel (aT -> T)).
Proof.
move=> f g => /andP[/asboolP fg /asboolP gf]; rewrite funeqE => x.
by apply/eqP; rewrite eq_le fg gf.
Qed.

#[export]
HB.instance Definition _ := Order.Preorder_isPOrder.Build default_display
  (aT -> T) lef_anti.
End FunOrder.

Section FunLattice.
Import Order.TTheory.
Variables (aT : Type) (d : Order.disp_t) (T : latticeType d).
Implicit Types f g h : aT -> T.

Definition meetf f g := fun x => Order.meet (f x) (g x).
Definition joinf f g := fun x => Order.join (f x) (g x).

Lemma meetfC : commutative meetf.
Proof. move=> f g; apply/funext => x; exact: meetC. Qed.

Lemma joinfC : commutative joinf.
Proof. move=> f g; apply/funext => x; exact: joinC. Qed.

Lemma meetfA : associative meetf.
Proof. move=> f g h; apply/funext => x; exact: meetA. Qed.

Lemma joinfA : associative joinf.
Proof. move=> f g h; apply/funext => x; exact: joinA. Qed.

Lemma joinfKI g f : meetf f (joinf f g) = f.
Proof. apply/funext => x; exact: joinKI. Qed.

Lemma meetfKU g f : joinf f (meetf f g) = f.
Proof. apply/funext => x; exact: meetKU. Qed.

Lemma lef_meet f g : (f <= g)%O = (meetf f g == f).
Proof.
apply/idP/idP => [/asboolP f_le_g|/eqP <-].
- apply/eqP/funext => x; exact/meet_l/f_le_g.
- apply/asboolP => x; exact: leIr.
Qed.

#[export]
HB.instance Definition _ := Order.POrder_isLattice.Build _ (aT -> T)
  meetfC joinfC meetfA joinfA joinfKI meetfKU lef_meet.

End FunLattice.
Module Exports.
HB.reexport.
End Exports.
End FunOrder.
HB.export FunOrder.Exports.

(* Defined before importing numdomain for HB to be happy. *)
#[short(type=orderedNmodType)]
HB.structure Definition OrderedNmodule :=
  {T of Num.POrderedNmodule T & Order.Total default_display T}.

#[short(type=orderedZmodType)]
HB.structure Definition OrderedZmodule :=
  {T of Num.POrderedZmodule T & Order.Total default_display T}.

Import Order Order.Theory Order.Def ssralg ssrnum GRing.Theory Num.Theory.
Import boolp.
From mathcomp Require Export classical_sets.
Unset SsrOldRewriteGoalsOrder. (* Remove upon requiring mathcomp-algebra >= 2.6.0 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Seen in mathcomp-analysis/classical/functions.v, very useful as sometimes,
   Search can encounter internal objects that are both useless and so big
   that a single one can sometimes clog the entire space printed by Search *)
Add Search Blacklist "__canonical__".
Add Search Blacklist "__functions_".
Add Search Blacklist "_factory_".
Add Search Blacklist "_mixin_".
Add Search Blacklist "phant_Build".
Add Search Blacklist "_subdef".

Set Bullet Behavior "Strict Subproofs".

(****************************************************************************)
(* Type of non-empty types, used to interpret HOL-Light types. *)
(****************************************************************************)

Notation Type' := pointedType.

HB.factory Record HOL_isPointed T := {point : T}.

Notation is_Type' := (HOL_isPointed.Build _).

(* in classical context, is a factory for pointedType *)
HB.builders Context T of HOL_isPointed T.

HB.instance Definition _ := gen_eqMixin T.

HB.instance Definition _ := gen_choiceMixin T.

HB.instance Definition _ := isPointed.Build _ point.

HB.end.

Definition dummy : Type' := Prop.

(****************************************************************************)
(* Curryfied versions of some Rocq connectives. *)
(****************************************************************************)

Definition imp (p q : Prop) : Prop := p -> q.

Definition all (A:Type) (P:A->Prop) := forall x:A, P x.

(****************************************************************************)
(* Extensionalities *)
(****************************************************************************)

(* tactic ext should cover almost all cases of need with functional and propositional
   extensionality and their combinations. *)

(* Axiom propext : forall P Q, P <-> Q -> P = Q *)
Lemma prop_ext : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P = Q.
Proof.
  by move=> *; eqProp.
Qed.

(* Axiom functional_extensionality_dep :
   forall f g, (forall x, f x = g x) -> f = g *)
Notation fun_ext := functional_extensionality_dep.

(****************************************************************************)
(* Coercion from Prop to bool? *)
(****************************************************************************)

Coercion asbool : Sortclass >-> bool.

Definition If (A : Type') (P : Prop) (x y : A) := if P then x else y.

(****************************************************************************)
(* Hilbert's ε operator. *)
(****************************************************************************)

Definition ε (A : Type') (P : A -> Prop) := get P.

(****************************************************************************)
(* Big bunch of useful tactics. *)
(****************************************************************************)
(****************************************************************************)
(* Notation to easily rewrite a view. *)
(****************************************************************************)

Coercion reflect_eq : reflect >-> eq.
Coercion propext : iff >-> eq.
(* Would this be useful ?
   Coercion funext : eqfun >-> eq.
*)

Notation "H **" := (H : _ = _).

(* Example:
Goal forall b n F, F n <-> F 0 -> ~~ b /\ F n -> ~ b /\ F 0.
  by move=> ? ? ? equiv ? ; rewrite negP** -equiv**.
Qed.
*)

(****************************************************************************)
(* Tactics for extensionality. *)
(****************************************************************************)

(* tactic ext should cover almost all cases of need with functional and propositional
   extensionality and their combinations. *)

(* use /` during ssr intropattern to ext all,
   /f` to only use funext,
   and /n` for n between 1 and 5 to ext exactly n arguments / hypotheses. *)

(* applies them to all arguments and propositions at once *)
Tactic Notation "ext" :=
  let rec ext' := (let H := fresh in
    first [apply functional_extensionality_dep | eqProp] => H ; try ext' ; move:H)
  in ext'.

(* with a counter added to the context to apply it for exactly n arguments/propositions *)
Variant internal_witness : forall A, A -> Type :=
  w0 A : forall a : A, internal_witness a.

Definition addone : forall n, internal_witness n -> internal_witness n.+1 :=
  fun n _ => w0 n.+1.

Ltac typecheck A a := assert_succeeds let s:=fresh in set (s := a : A).

Tactic Notation "ext" integer(n) :=
  let ext0 x w := (first [apply functional_extensionality_dep | eqProp] => x ; set (w := w0 x))
   (* choosing the fresh variables inside ext0 fails to create new variable names. *)
  in do n (let x := fresh in let w := fresh in ext0 x w) ;
  repeat match goal with | x : _ |- _  =>
  lazymatch goal with w : internal_witness x |- _ => clear w ; revert x end end.

Ltac funext :=
  let rec funext' := (let x := fresh "x" in
    apply functional_extensionality_dep => x ; try funext' ; move:x)
  in funext'.

Notation "`" := (ltac:(try ext)) (at level 0, only parsing).
Notation "f`" := (ltac:(try funext)) (at level 0, only parsing).

Notation "1`" := (ltac:(first [apply functional_extensionality_dep | eqProp])) (at level 0, only parsing).

Notation "2`" := (ltac:( let H := fresh in first [apply funext | eqProp] =>H ;
                         first [apply funext | eqProp] ; move: H ))
                           (at level 0, only parsing).

Notation "3`" := (ltac:( let H1 := fresh in first [apply funext | eqProp] =>H1 ;
                         let H2 := fresh in first [apply funext | eqProp] =>H2 ;
                         first [apply funext | eqProp] ; move: H1 H2 ))
                           (at level 0, only parsing).

Notation "4`" := (ltac:( let H1 := fresh in first [apply funext | eqProp] =>H1 ;
                         let H2 := fresh in first [apply funext | eqProp] =>H2 ;
                         let H3 := fresh in first [apply funext | eqProp] =>H3 ;
                         first [apply funext | eqProp] ; move: H1 H2 H3))
                           (at level 0, only parsing).

Notation "5`" := (ltac:( let H1 := fresh in first [apply funext | eqProp] =>H1 ;
                         let H2 := fresh in first [apply funext | eqProp] =>H2 ;
                         let H3 := fresh in first [apply funext | eqProp] =>H3 ;
                         let H4 := fresh in first [apply funext | eqProp] =>H4 ;
                         first [apply funext | eqProp] ; move: H1 H2 H3 H4))
                           (at level 0, only parsing).

(* Definition test (n m k : nat) (f : nat -> nat -> nat) := f = f.
Goal True -> test = test. move => * /f`* /3` H n0 m0. *)

(****************************************************************************)
(* Change top hypothesis of the form [f = g] with                           *)
(* [forall x1 ... xn, f x1 ... xn = g x1 ... xn] or the opposite.           *)
(****************************************************************************)

Lemma gen_fun1 A B (f g : forall a : A, B a) : f = g <-> forall a, f a = g a.
Proof.
  by split=>[->|? /f`].
Qed.

Lemma gen_fun2 A B C (f g : forall (a:A) (b:B a), C a b) : f = g <->
  forall a b, f a b = g a b.
Proof.
  by split=>[->|? /f`].
Qed.

Lemma gen_fun3 A B C D (f g: forall (a:A) (b:B a) (c:C a b),D a b c): f = g <->
  forall a b c, f a b c = g a b c.
Proof.
  by split=>[->|? /f`].
Qed.

Lemma gen_fun4 A B C D E (f g: forall (a:A) (b:B a)
  (c:C a b) (d:D a b c), E a b c d) : f = g <->
    forall a b c d, f a b c d = g a b c d.
Proof.
  by split=>[->|? /f`].
Qed.

Lemma gen_fun5 A B C D E F (f g: forall (a:A) (b:B a) (c:C a b)
  (d:D a b c) (e:E a b c d), F a b c d e):  f = g <->
  forall a b c d e, f a b c d e = g a b c d e.
Proof.
  by split=>[->|? /f`].
Qed.

(* /[gen] in an intro pattern to replace partial functional equality in
   the top assumption with fully quantified equality unless the functions
   have more than 5 arguments. /[funext] replaces quantified equality with
   function equality instead. *)
Ltac move_gen_fun := move/gen_fun5 || move/gen_fun4 || move/gen_fun3
  || move/gen_fun2 || move/gen_fun1 ||
  fail "top assumption is not a (possibly quantified) function equality".

Notation "[ 'funext' ]" := ltac:(lazymatch goal with
  | |- _ = _ -> _ =>
    fail "top assumption is an equality, no extensionality can apply"
  | |- _ => move_gen_fun end).

Notation "[ 'gen' ]" := ltac:(try move/[funext] ; move_gen_fun).

(****************************************************************************)
(* specialize the top assumption during intros [move=> ... /[spec x] *)
(****************************************************************************)

Ltac spec_tactic x := let H := fresh "_top_" in move=>H ; move:{H}(H x).

Notation "[ 'spec' specarg1 ]" := ltac:(spec_tactic specarg1).

Notation "[ 'spec' specarg1 | specarg2 ]" := ltac:( spec_tactic specarg1 ; spec_tactic specarg2).

Notation "[ 'spec' specarg1 | specarg2 | specarg3 ]" :=
  ltac:(spec_tactic specarg1 ; spec_tactic specarg2 ; spec_tactic specarg3).

Notation "[ 'spec' ]" :=
  ltac:(unfold all,imp ; let H := fresh "_top_" in let arg := fresh "x" in lazymatch goal with
  | |- (forall _: ?A, _) -> _ => have arg : A ;
    last (move=>H ; move:{H} arg (H arg) ; try move=> _)
  | |- _ => fail "not a product type in top assumption" end).

Notation "[ 'spec' 'by' [ ] ]" := ltac:(move/[spec] ; first by []).

(****************************************************************************)
(* replaces [ε ?P] with x such that [P x], adding [exists x, P x] as a goal *)
(****************************************************************************)

Definition ε_spec {A : Type'} {P : A -> Prop} : (exists x, P x) -> P (ε P) := @getPex _ P.

Ltac ε_spec_tactic tac := let x := fresh "x" in lazymatch goal with
  |- context[@ε ?T0 ?P] => let T := (eval cbn in T0) in
      have /[spec] := @ε_spec T0 P ; [tac | move: (@ε T0 P) ] ;
      change T0 with T end.

Tactic Notation "ε_spec" := ε_spec_tactic idtac.

Tactic Notation "ε_spec" "by" tactic(tac) := ε_spec_tactic ltac:(by tac).
Tactic Notation "ε_spec" "by" "[" "]" := ε_spec by unshelve eexists ; eauto 1.

(****************************************************************************)
(* Repeating exists. *)
(****************************************************************************)

Tactic Notation "exist" uconstr(x1) uconstr(x2) :=
  exists x1 ; exists x2.

Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) :=
  exists x1 ; exists x2 ; exists x3.

Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) :=
  exists x1 ; exists x2 ; exists x3 ; exists x4.

Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) uconstr(x5) :=
  exists x1 ; exists x2 ; exists x3 ; exists x4 ; exists x5.

(****************************************************************************)
(* Alignment automation tactics. *)
(****************************************************************************)

(****************************************************************************)
(* For the ε operator *)
(****************************************************************************)

(* The definition of an HOL-Light function that is recursively defined
on some inductive type usually looks like:

  [ε (fun g => forall uv, P (g uv)) uv0]

  where P does not depend on uv (unused variable). *)

(* [gobble f uv] replaces the occurrences of [f uv] by a new symbol
named [f] too and removes [uv] from the context, assuming that [f uv]
does not actually depends on [uv]. *)
Ltac gobble f uv :=
  cbv beta in * ; (* Simplifies application of uv so only [f u] is left. *)
  let g := fresh in
  set (g := f uv) in * ;
  clearbody g ; simpl in g ;
  clear f uv ; rename g into f.

Lemma align_ε (A : Type') (P : A -> Prop) a : P a -> (forall x, P a -> P x -> a = x) -> a = ε P.
Proof.
  by move => ha ; apply ; last ε_spec by exists a.
Qed.

Ltac remove_unused uv := repeat match goal with
  | H : context [(fun=> ?x) uv] |- _ => change ((fun=> _) uv) with x in H end.

(* From a goal of the form [a = ε (fun a' => forall uv, P (a' uv)) uv0],
align_ε generates two subgoals [P a] and [forall x, P a -> P x -> a = x]. *)
Ltac align_ε :=
  let rec aux :=
    lazymatch goal with
    | |- _ ?x = ε _ ?x => apply (f_equal (fun f => f x)) ; aux
    | |- ?a = ε _ ?r =>
        (* Replace the goal by (fun _ => a = ε ?P) *)
        apply (f_equal (fun g => g r) (x := fun _ => a)) ;
        aux ;
        [ intros _
        | let a' := fresh in
          let uv := fresh in
          let H' := fresh in
          let H := fresh in
          intros a' H H' ; ext 1=> uv ;
          specialize (H uv) ; (* As [P] starts with [forall uv] *)
          specialize (H' uv) ;
          gobble a' uv ;
          revert a' H H' (* Revert [a'], [P a] and [P a'] to reuse them in other tactics *)
        ]
    | |- _ = (@ε ?T _) => apply (align_ε (A := (T : Type')))
        (* Replaces the goal [a = ε P] with two goals [P a] and
           [forall x, P a => P x => x = a]. *)
    end
  in aux.

(****************************************************************************)
(* For if ... then ... else ... over Prop *)
(****************************************************************************)

Lemma is_True P : (P = True) = P.
Proof.
  by ext=> // ->.
Qed.

(* From a proof of P (either a hypothesis or a lemma), rewrite P into True. *)
Ltac is_True H :=
  let H' := fresh in set (H' := H) ;
  match type of H' with ?P => rewrite <- (is_True P) in H' ;
    rewrite -> H' in * ; clear H' ; try clear H end.

Lemma is_False P : (P = False) = (~ P).
Proof.
  by ext=> // ->.
Qed.

(* From hypothesis H : ~P, rewrite P into False *)
Ltac is_False H :=
  let H' := fresh in set (H' := H) ;
  match type of H' with ~?P => rewrite <- (is_False P) in H' ;
    rewrite -> H' in * ; clear H' ; try clear H end.

(* The following are useful tools to work with COND :
   - Tactic if_triv replaces [if P then x else y] in the goal with either x or y
     assuming P or ~P is derivable with easy.
   - Tactic if_intro transforms a goal [P (if Q then x else y)]
     into two goals [Q -> P x] and [~Q -> P y] and
     simplifies all other [if Q then x' else y'] even if x<>x' or y<>y'
   - Lemma if_elim destructs hypothesis [if P then Q else R]
     as if it were (P /\ Q) \/ (~P /\ R) *)

Lemma if_True (A : Type) (x y : A) : (if True then x else y) = x.
Proof.
  by rewrite/asbool ; case pselect.
Qed.

Lemma if_False (A : Type) (x y : A) : (if False then x else y) = y.
Proof.
by rewrite/asbool ; case pselect.
Qed.

Lemma if_triv_True (A : Type) (P : Prop) (x y : A) : P -> (if P then x else y) = x.
Proof.
  by rewrite -{1}(is_True P) => -> ; exact (if_True _ _).
Qed.

Lemma if_triv_False (A : Type) (P : Prop) (x y : A) : ~P -> (if P then x else y) = y.
Proof.
  by rewrite -{1}(is_False P) => -> ; exact (if_False _ _).
Qed.

Tactic Notation "if_triv" "by" tactic(tac) :=
  rewrite/If ;
  (rewrite if_triv_True ; first by tac) ||
  (rewrite if_triv_False ; first by tac) ||
  fail "no conditional term to simplify".

Tactic Notation "if_triv" := if_triv by idtac.

(* /1= in intro/rewrite pattern *)
Ltac ssrsimpl1 := repeat if_triv.

(* If needed, specify which P is trivial *)
Tactic Notation "if_triv" constr(P) :=
  rewrite/If ;
  (rewrite (if_triv_True _ P) ; [easy | auto]) +
  (rewrite (if_triv_False _ P) ; [easy | auto]).

Tactic Notation "if_triv" "using" constr(H) :=
  rewrite/If ; let H' := fresh in set (H' := H) ;
  (rewrite if_triv_True ; first by auto using H') ||
  (rewrite if_triv_False ; first by auto using H') ; clear H'.

Tactic Notation "if_triv" constr(P) "using" constr(H) :=
  rewrite/If ; let H' := fresh in set (H' := H) ;
  (rewrite (if_triv_True _ P) ; first by auto using H') ||
  (rewrite (if_triv_False _ P) ; first by auto using H') ; clear H'.

Lemma if_intro (A : Type) (Q : Prop) (P : A -> Prop) (x y : A) :
  (Q -> P x) -> (~Q -> P y) -> P (if Q then x else y).
Proof. case (pselect Q)=> [? /1= + _ | ? /1= _]; exact. Qed.

(* applies if_intro then also clears all if with
   the same hypothesis *)

Ltac if_intro :=
  rewrite/If ;
  let H := fresh in
  apply if_intro => H ;
  [ repeat rewrite (if_triv_True _ _ H)
  | repeat rewrite (if_triv_False _ _ H)] ;
  move : H.

(* /c` in intropattern, c for case. *)
Notation "c`" := (ltac:(if_intro)) (at level 0, only parsing).

Lemma if_elim (P Q R G : Prop) : (if P then Q else R) -> (P -> Q -> G) -> (~ P -> R -> G) -> G.
Proof.
  by case (pselect P) => H /1= ; auto.
Qed.

(****************************************************************************)
(* Pure. *)
(****************************************************************************)

Definition itself (A:Type') : Type := unit.

Definition type A : itself A := tt.

Definition equal_intr : forall A : Prop, forall B : Prop, (A -> B) -> (B -> A) -> A = B := @prop_ext.

Lemma equal_elim : forall A : Prop, forall B : Prop, A = B -> A -> B.
Proof. by move=>> ->. Qed.

Lemma abstract_rule : forall (a b : Type') (f g : a -> b),
  (forall x : a, f x = g x) -> f = g.
Proof. by move=>> /[funext]. Qed.

Lemma combination (a b : Type') (f g : a -> b) (x y : a) :
  f = g -> x = y -> f x = g y.
Proof. by move=> -> ->. Qed.

Lemma conjunction_def A B : (A /\ B) = forall C, (A -> B -> C) -> C.
Proof. ext=> [[] ? ? ?|] ; exact. Qed.

Definition term (a : Type') : a -> Prop := xpredpT.

Lemma term_def (A : Type') (x : A) : term x = (forall P : Prop, P -> P).
Proof. by ext. Qed.

Definition sort_constraint (a : Type') : (itself a) -> Prop := xpredpT.

Lemma sort_constraint_def : forall a : Type', @eq Prop (@sort_constraint a (type a)) (@term (itself a) (type a)).
Proof. reflexivity. Qed.

(****************************************************************************)
(* Tools.Code_Generator. *)
(****************************************************************************)

Lemma holds_def_raw : @eq Prop True (@eq (Prop -> Prop) (fun x : Prop => x) (fun x : Prop => x)).
Proof. by ext. Qed.

(****************************************************************************)
(* HOL.HOL. *)
(****************************************************************************)

Definition Trueprop : Prop -> Prop := fun P => P.

HB.mixin Record default_class_mixin (A : Type') T := { default : A }.

#[short (type = default_class_pred)]
HB.structure Definition default_class_ (A : Type') := { T of default_class_mixin A T }.

HB.mixin Record equal_class_mixin (A : Type') T := { equal : A -> A -> Prop }.

#[short (type = equal_class_pred)]
HB.structure Definition equal_class_ (A : Type') := { T of equal_class_mixin A T }.

Definition fodder : Set := False.
Definition fodder2 : Set := False.
Definition fodder3 : Set := False.
Definition fodder4 : Set := False.
Definition fodder5 : Set := False.

Existing Class default_class_pred.

Existing Class equal_class_pred.

HB.mixin Record hasOtherEqual T := {
  equal_bis : T -> T -> Prop;
  equal_bis_def (x y : T) : equal_bis x y <-> x = y
}.

#[short(type=equal_class_type)]
HB.structure Definition equal_class_struct := { T of Pointed T & hasOtherEqual T }.

HB.mixin Record hasDefault T := {
  default_val : T
}.

#[short(type=default_class_type)]
HB.structure Definition default_class_struct := { T of Pointed T & hasDefault T }.

HB.instance Definition _ (A : default_class_type) := default_class_mixin.Build A fodder default_val.
HB.instance Definition _ (A : equal_class_type) := equal_class_mixin.Build A fodder equal_bis.

Lemma mk_equal_class_type (T : Type') : forall x y : T, x = y <-> x = y.
Proof. by []. Qed.

HB.instance Definition _ A := Pointed.on (itself A).
HB.instance Definition _ A := hasOtherEqual.Build (itself A) (@mk_equal_class_type _).
HB.instance Definition _ A := equal_class_mixin.Build (itself A) fodder2 eq.

Instance default_pred_of_type (A : default_class_type) : default_class_pred A := fodder.
Instance equal_pred_of_type (A : equal_class_type) : equal_class_pred A := fodder.
Instance itself_equal_pred_instance : forall A, equal_class_pred (itself A) := fun=> fodder2.

Lemma True_def_raw : True = ((fun x : Prop => x) = (fun x : Prop => x)).
Proof. by ext. Qed.

Lemma All_def_raw : forall a : Type', (@all a) = (fun P : a -> Prop => P = (fun x : a => True)).
Proof. by move=>> /` // > ->. Qed.

Lemma Ex_def_raw : forall a : Type', (@ex a) = (fun P : a -> Prop => forall Q : Prop, (forall x : a, P x -> Q) -> Q).
Proof.
  move=> A /` P => [[x Hx] Q HPQ |] ; first exact (HPQ x Hx).
  apply ; exact: ex_intro.
Qed.

Lemma False_def_raw : False = (forall P : Prop, P).
Proof. ext ; [case | exact]. Qed.

Lemma not_def_raw : not = (fun P : Prop => P -> False).
Proof. reflexivity. Qed.

Lemma and_def_raw : and = (fun P : Prop => fun Q : Prop => forall R : Prop, (P -> Q -> R) -> R).
Proof. ext=> P Q => [[? ?] >|] ; exact. Qed.

Lemma or_def_raw : or = (fun P : Prop => fun Q : Prop => forall R : Prop, (P -> R) -> (Q -> R) -> R).
Proof. by ext=> P Q => [[] ? >|] ; last apply ; auto. Qed.

Definition Ex1 (A : Type') : (A -> Prop) -> Prop := fun P => exists! x, P x.

Lemma Ex1_def_raw (A : Type') : @eq ((A -> Prop) -> Prop) (@Ex1 A) (fun P : A -> Prop => exists x : A, and (P x) (forall y : A, (P y) -> @eq A y x)).
Proof.
  by ext=> P [x [? H]] ; exists x ; split=> // y Py ; rewrite (H y Py).
Qed.

Lemma If_def_raw (A : Type') : @eq (Prop -> A -> A -> A) (@If A) (fun P : Prop => fun x : A => fun y : A => @ε A (fun z : A => and ((@eq Prop P True) -> @eq A z x) ((@eq Prop P False) -> @eq A z y))).
Proof.
  ext=> P x y ; align_ε ; first by split=> -> ; rewrite/If ?if_True ?if_False.
  move=> f' [CT CF] [f'T f'F] ; case : (EM P).
  - by move/propT => H ; rewrite (CT H) f'T.
  - by move/propF => H ; rewrite (CF H) f'F.
Qed.

Definition class_equal (A : Type') (eq_sym : A -> A -> Prop) : Prop :=
  forall x y, eq_sym x y <-> (x = y).

Lemma class_equal_def (A : Type') (equal : A -> A -> Prop) : @eq Prop (@class_equal A equal) (forall x : A, forall y : A, @eq Prop (equal x y) (@eq A x y)).
Proof. by rewrite/class_equal=> /` Heq ? ? ; rewrite (Heq _ _)**. Qed.

Definition type_class : Type' -> Prop := xpredpT.

Definition equal_itself_inst_equal_itself {A : Type'} : (itself A) -> (itself A) -> Prop := eq.

Lemma equal_itself_inst_equal_itself_def : forall A : Type', @eq ((itself A) -> (itself A) -> Prop) (@equal (itself A) _) (@equal_itself_inst_equal_itself A).
Proof. reflexivity. Qed.

Definition default_class (A : Type') {wildcard_2 : default_class_pred A} : Prop := True.
Arguments default_class _ {_}.

Lemma default_class_def (A : Type') {wildcard_4 : default_class_pred A} : @eq Prop (default_class A) (type_class A).
Proof. reflexivity. Qed.

Lemma default_class_type_def : forall (A : default_class_type), default_class A.
Proof. by []. Qed.

Definition equal_class (A : Type') {wildcard_3 : equal_class_pred A} : Prop := forall x y : A, (equal x y) <-> (x = y).
Arguments equal_class _ {_}.

Lemma equal_class_def (A : Type') {wildcard_5 : equal_class_pred A} : @eq Prop (equal_class A) (and (type_class A) (Trueprop (@class_equal A (@equal A _)))).
Proof. by rewrite andB. Qed.

Lemma equal_class_type_def : forall (A : equal_class_type), equal_class A.
Proof. move=>> ; exact: equal_bis_def. Qed.

Lemma impI : forall P Q, ((Trueprop P) -> Trueprop Q) -> Trueprop (P -> Q).
Proof. by []. Qed.

Lemma mp : forall P Q, (Trueprop (P -> Q)) -> (Trueprop P) -> Trueprop Q.
Proof. by []. Qed.

Lemma True_or_False : forall P, Trueprop (P = True \/ P = False).
Proof.
  by move=> P ; case: (EM P) => ? ; [left | right] ; ext.
Qed.

Lemma eq_reflection : forall a : Type', (type_class a) -> @all a (fun x : a => @all a (fun y : a => (Trueprop (@eq a x y)) -> @eq a x y)).
Proof. by rewrite/all. Qed.

Lemma refl : forall a : Type', (type_class a) -> @all a (fun t : a => Trueprop (@eq a t t)).
Proof. by rewrite/all. Qed.

Lemma subst : forall a : Type', (type_class a) -> @all a (fun t : a => @all a (fun s : a => @all (a -> Prop) (fun P : a -> Prop => (Trueprop (@eq a s t)) -> (Trueprop (P s)) -> Trueprop (P t)))).
Proof. by move=> ? _ > ->. Qed.

Lemma ext : forall a : Type', forall b : Type', (type_class a) -> (type_class b) -> @all (a -> b) (fun f : a -> b => @all (a -> b) (fun g : a -> b => (@all a (fun x : a => Trueprop (@eq b (f x) (g x)))) -> Trueprop (@eq (a -> b) f g))).
Proof. by move=>> _ _ ? ? ? /`. Qed.

Lemma the_eq_trivial : forall A : Type', (type_class A) -> @all A (fun a : A => Trueprop (@eq A (@ε A (fun x : A => @eq A x a)) a)).
Proof. by intros a _ x ; ε_spec by exists x. Qed.

Lemma fun_arity : forall A : Type', forall B : Type', imp (type_class A) (imp (type_class B) (type_class (A -> B))).
Proof. by []. Qed.

Lemma itself_arity : forall A : Type', imp (type_class A) (type_class (itself A)).
Proof. by []. Qed.

Lemma arity_type_bool : type_class Prop.
Proof. by []. Qed.

(****************************************************************************)
(* HOL.Orderings. *)
(****************************************************************************)

(*** Class predicates ***)
HB.mixin Record top_class_mixin (A : Type) T := { top_class_top : A }.

#[short (type = top_class_pred)]
HB.structure Definition top_class_ (A : Type) := { T of top_class_mixin A T }.

HB.mixin Record ord_class_mixin (A : Type) T := { less_eq : A -> A -> Prop; less : A -> A -> Prop }.

#[short (type = ord_class_pred)]
HB.structure Definition ord_class_ (A : Type) := { T of ord_class_mixin A T }.

HB.mixin Record bot_class_mixin (A : Type) T := { bot : A }.

#[short (type = bot_class_pred)]
HB.structure Definition bot_class_ (A : Type) := { T of bot_class_mixin A T }.

#[short (type = order_bot_class_pred)]
HB.structure Definition order_bot_class_ (A : Type) := { T of bot_class_mixin A T & ord_class_mixin A T }.

#[short (type = order_top_class_pred)]
HB.structure Definition order_top_class_ (A : Type) := { T of top_class_mixin A T & ord_class_mixin A T }.

Existing Class top_class_pred.
Existing Class bot_class_pred.
Existing Class ord_class_pred.
Existing Class order_bot_class_pred.
Existing Class order_top_class_pred.

Instance ord_class_pred_of_order_bot_class_pred A :
  (order_bot_class_pred A) -> ord_class_pred A := id.
Instance bot_class_pred_of_order_bot_class_pred A :
  (order_bot_class_pred A) -> bot_class_pred A := id.
Instance top_class_pred_of_order_top_class_pred A :
  (order_top_class_pred A) -> top_class_pred A := id.
Instance ord_class_pred_of_order_top_class_pred A :
  (order_top_class_pred A) -> ord_class_pred A := id.

(*** Class types ***)
(* In mathcomp, ordered types are parametrised by a dull argument
   (called a display), basically of type unit * unit, to allow multiple
   ordered structures with unique notations on a same type.
   Since we must have one type, we fix our display to be the default display
   (tt,tt). (other displays are defined by making them opaque) *)

#[short(type=pPreorderType)]
HB.structure Definition PointedPreorder d := { T of Pointed T & Preorder d T }.

#[short(type=pPOrderType)]
HB.structure Definition PointedPOrder d := { T of Pointed T & POrder d T }.

#[short(type=pOrderType)]
HB.structure Definition PointedTotal d := { T of Pointed T & Total d T }.

(* It would be possible to not require pointedness (bottom is a point)
   but then it could cause problems when mixing both top and bottom
   (or bottom and 0, which is already declared as making a type pointed) *)
#[short(type=pbPreorderType)]
HB.structure Definition PointedBPreorder d := { T of Pointed T & BPreorder d T }.

#[short(type=pbPOrderType)]
HB.structure Definition PointedBPOrder d := { T of Pointed T & BPOrder d T }.

#[short(type=ptPreorderType)]
HB.structure Definition PointedTPreorder d := { T of Pointed T & TPreorder d T }.

#[short(type=ptPOrderType)]
HB.structure Definition PointedTPOrder d := { T of Pointed T & TPOrder d T }.

Open Scope order_scope.
HB.mixin Record isDenseOrder d T of POrder d T := {
  lt_dense (x y : T) : x < y -> (exists z : T, (x < z /\ z < y))
}.

#[short(type=dense_order_class_type)]
HB.structure Definition dense_order_class_struct d := { T of PointedPOrder d T & isDenseOrder d T }.

#[short(type=dense_linorder_class_type)]
HB.structure Definition dense_linorder_class_struct d := { T of PointedTotal d T & isDenseOrder d T }.

HB.mixin Record hasNoTop d T of Preorder d T := {
  gt_ex (x : T) : exists y : T, y > x
}.

#[short(type=no_top_class_type)]
HB.structure Definition no_top_class_struct d := { T of PointedPOrder d T & hasNoTop d T }.

HB.mixin Record hasNoBot d T of Preorder d T := {
  lt_ex (x : T) : exists y : T, y < x
}.

#[short(type=no_bot_class_type)]
HB.structure Definition no_bot_class_struct d := { T of PointedPOrder d T & hasNoBot d T }.

#[short(type=unbounded_dense_linorder_class_type)]
HB.structure Definition unbounded_dense_linorder_class_struct d :=
  { T of dense_linorder_class_struct d T & hasNoTop d T & hasNoBot d T }.

HB.mixin Record isWellorder d T of Total d T := {
  wf_lt : well_founded (lt : T -> T -> Prop)
}.

#[short(type=wellorder_class_type)]
HB.structure Definition wellorder_class_struct d :=
  { T of PointedTotal d T & isWellorder d T }.

(*** Class instances ***)

Module Prop_order.
Local Notation le := (fun P Q : Prop => `[< P -> Q >]).
Local Notation lt := (fun P Q => `[< ~P /\ Q >]).
Local Notation d := default_display.

Lemma lt_def : forall x y, lt x y = le x y && ~~ le y x.
Proof.
  move=> P Q ; apply is_true_inj ; rewrite -andP** -negP** 3!asboolE.
  ext => -[] ; last (split ; last apply contrapT) ; tauto.
Qed.

Lemma le_refl : reflexive le.
Proof. move=> ? ; exact/asboolP. Qed.

Lemma le_trans : transitive le.
Proof. move=>> ; rewrite 3!asboolE ; tauto. Qed.

#[export]
HB.instance Definition _ := isPreorder.Build d Prop lt_def le_refl le_trans.

Lemma le0x : forall x, le False x.
Proof. move=>> ; exact/asboolP. Qed.

#[export]
HB.instance Definition _ := hasBottom.Build d Prop le0x.

Lemma lex1 : forall x, le x True.
Proof. move=>> ; exact/asboolP. Qed.

#[export]
HB.instance Definition _ := hasTop.Build d Prop lex1.

Lemma le_anti : antisymmetric le.
Proof. by move=> ? ? /andP [] /asboolP ? /asboolP ? /`. Qed.

#[export]
HB.instance Definition _ := Preorder_isPOrder.Build d Prop le_anti.

Lemma le_total : total (<=%O : rel Prop).
Proof.
  move=> P ? ; apply/orP ; rewrite 2!asboolE ; case: (EM P) ; tauto.
Qed.

#[export]
HB.instance Definition _ := POrder_isTotal.Build d Prop le_total.

Lemma wf_lt : well_founded lt.
Proof.
  by move=> ? ; split=> ? /asboolP [? _] ; split=> ? /asboolP [_ ?].
Qed.

#[export]
HB.instance Definition _ := isWellorder.Build d Prop wf_lt.

Module Exports.
HB.reexport.
End Exports.
End Prop_order.

HB.export Prop_order.Exports.

Lemma fun_leP {A : Type} {d} {B : preorderType d} {f g : A -> B} :
  reflect (forall x, f x <= g x) (f <= g).
Proof. exact:asboolP. Qed.

Lemma fun_ltP (A : Type) d (B : preorderType d) (f g : A -> B) :
  reflect ((forall x, f x <= g x) /\ exists x, g x > f x) (f < g).
Proof.
  case: (@idP (_ < _))=> [/andP [/asboolP ? /negP nlegf]| nltfg] ; constructor.
  - split ; rewrite // not_existsP => ? ; apply/nlegf/asboolP=> ?.
    by rewrite comparable_leNgt ; [apply/orP ; right | apply/negP].
  - case=> ? [x ?] ; apply/nltfg/andP ; split ; first exact/asboolP.
    apply/negP=> /asboolP /[spec x]; rewrite comparable_leNgt; [|by move/negP].
    by apply/orP ; right.
Qed.

Module MoreFunOrder.
Section FunOrder.
Context (A : Type).
Local Notation d := default_display.

Section BPreorder.
Context (db : disp_t) (B : bPreorderType db).

Lemma le0x : forall f : A -> B, (fun=> bottom) <= f.
Proof. move=>> ; exact/asboolP. Qed.

#[export]
HB.instance Definition _ := hasBottom.Build d (A -> B) le0x.
End BPreorder.

Section TPreorder.
Context (db : disp_t) (B : tPreorderType db).

Lemma lex1 : forall f : A -> B, f <= (fun=> top).
Proof. move=>> ; exact/asboolP. Qed.

#[export]
HB.instance Definition _ := hasTop.Build d (A -> B) lex1.

End TPreorder.

Section DenseOrder.
Context (db : disp_t) (B : dense_order_class_type db).

Lemma lt_dense (f g : A -> B) : f < g -> (exists h : A -> B, (f < h /\ h < g)).
Proof.
  case/fun_ltP=> lefg [x /lt_dense [hx [ltfxhx lthxgx]]].
  exists (fun x0 => if x0 = x then hx else f x0).
  split ; apply/fun_ltP ; split=> *.
  1,3 : if_intro => // -> ; exact: ltW.
  1,2 : by exists x=> /1=.
Qed.

#[export]
HB.instance Definition _ := isDenseOrder.Build d (A -> B) lt_dense.
End DenseOrder.
End FunOrder.

Section PointedFunOrder.
Context (A : Type').
Local Notation d := default_display.

Section NoTop.
Context (db : disp_t) (B : no_top_class_type db).

Lemma gt_ex (f : A -> B) : exists g, g > f.
Proof.
  have [y gtyfp] := gt_ex (f point).
  exists (fun x : A => if x = point then y else f x) ; apply/fun_ltP ; split.
  - move=> ? /c` // -> ; exact: ltW.
  - by exists point => /1=.
Qed.

HB.instance Definition _ := hasNoTop.Build d (A -> B) gt_ex.
End NoTop.

Section NoBot.
Context (db : disp_t) (B : no_bot_class_type db).

Lemma lt_ex (f : A -> B) : exists g, g < f.
Proof.
  have [y gtyfp] := lt_ex (f point).
  exists (fun x : A => if x = point then y else f x) ; apply/fun_ltP ; split.
  - move=> ? /c` // -> ; exact: ltW.
  - by exists point => /1=.
Qed.

HB.instance Definition _ := hasNoBot.Build d (A -> B) lt_ex.
End NoBot.
End PointedFunOrder.

Module Exports.
HB.reexport.
End Exports.
End MoreFunOrder.

HB.export MoreFunOrder.Exports.

(* HB.instance Definition _ := bot_class_mixin.Build Prop fodder False.
HB.instance Definition _ := ord_class_mixin.Build Prop fodder
  (fun P Q => P -> Q) (fun P Q => ~P /\ Q).
HB.instance Definition _ := top_class_mixin.Build Prop fodder True. *)

HB.instance Definition _ d (T : pPreorderType d) :=
  ord_class_mixin.Build T fodder le lt.
HB.instance Definition _ d (T : pbPreorderType d) :=
  bot_class_mixin.Build T fodder bottom.
HB.instance Definition _ d (T : ptPreorderType d) :=
  top_class_mixin.Build T fodder top.

(* HB.saturate (_ -> _) does not work... *)
HB.instance Definition _ d T (T' : pPreorderType d) :=
  Pointed.on (T -> T').
HB.instance Definition _ d T (T' : pbPreorderType d) :=
  Pointed.on (T -> T').
HB.instance Definition _ d T (T' : ptPreorderType d) :=
  Pointed.on (T -> T').
HB.instance Definition _ d T (T' : pPOrderType d) :=
  Pointed.on (T -> T').
HB.instance Definition _ d T (T' : pbPOrderType d) :=
  Pointed.on (T -> T').
HB.instance Definition _ d T (T' : ptPOrderType d) :=
  Pointed.on (T -> T').

HB.instance Definition _ A B (_ : bot_class_pred B) :=
  bot_class_mixin.Build (A -> B) fodder2 (fun=> bot).
HB.instance Definition _ A B (_ : top_class_pred B) :=
  top_class_mixin.Build (A -> B) fodder2 (fun=> top_class_top).

HB.factory Record ord_of_less_eq A T := { less_eq : A -> A -> Prop }.
HB.builders Context A T of ord_of_less_eq A T.
HB.instance Definition _ := ord_class_mixin.Build A T less_eq
  (fun x y => less_eq x y /\ ~ less_eq y x).
HB.end.

HB.instance Definition _ A B (_ : ord_class_pred B) :=
  ord_class_mixin.Build (A -> B) fodder2
  (fun f g => `[< forall x, less_eq (f x) (g x) >])
  (fun f g => `[< forall x, less_eq (f x) (g x) >] &&
    ~~ `[< forall x, less_eq (g x) (f x) >]).

Instance bool_bot_pred_instance : bot_class_pred Prop := fodder.
Instance bool_ord_pred_instance : ord_class_pred Prop := fodder.
Instance bool_order_bot_pred_instance : order_bot_class_pred Prop := fodder.
Instance bool_order_top_pred_instance : order_top_class_pred Prop := fodder.
Instance bool_top_pred_instance : top_class_pred Prop := fodder.
Instance ord_class_pred_of_type d (A : pPreorderType d) : ord_class_pred A := fodder.
Instance preorder_class_pred_of_type d (A : pPreorderType d) : ord_class_pred A := fodder.
Instance order_class_pred_of_type d (A : pPOrderType d) : ord_class_pred A := fodder.
Instance linorder_class_pred_of_type d (A : pOrderType d) : ord_class_pred A := fodder.
Instance bot_class_pred_of_type d (A : pbPreorderType d) : bot_class_pred A := fodder.
Instance order_bot_class_pred_of_type d (A : pbPOrderType d) : order_bot_class_pred A := fodder.
Instance top_class_pred_of_type d (A : ptPreorderType d) : top_class_pred A := fodder.
Instance order_top_class_pred_of_type d (A : ptPOrderType d) : order_top_class_pred A := fodder.
Instance dense_order_class_pred_of_type d (A : dense_order_class_type d) : ord_class_pred A := fodder.
Instance dense_linorder_class_pred_of_type d (A : dense_linorder_class_type d) : ord_class_pred A := fodder.
Instance no_top_class_pred_of_type d (A : no_top_class_type d) : ord_class_pred A := fodder.
Instance no_bot_class_pred_of_type d (A : no_bot_class_type d) : ord_class_pred A := fodder.
Instance unbounded_dense_linorder_class_pred_of_type d (A : unbounded_dense_linorder_class_type d) : ord_class_pred A := fodder.
Instance wellorder_class_pred_of_type d (A : wellorder_class_type d) : ord_class_pred A := fodder.
Instance fun_bot_pred_instance (A B : Type') (_ : bot_class_pred B) :
  bot_class_pred (A -> B) := fodder2.
Instance fun_ord_pred_instance (A B : Type') (_ : ord_class_pred B) :
  ord_class_pred (A -> B) := fodder2.
Instance fun_order_bot_pred_instance (A B : Type') (_ : order_bot_class_pred B) :
  order_bot_class_pred (A -> B) := fodder2.
Instance fun_order_top_pred_instance (A B : Type') (_ : order_top_class_pred B) :
  order_top_class_pred (A -> B) := fodder2.
Instance fun_top_pred_instance (A B : Type') (_ : top_class_pred B) :
  top_class_pred (A -> B) := fodder2.

Definition ord_bool_inst_less_bool (P Q : Prop) : Prop := ~P /\ Q.
Definition ord_fun_inst_less_eq_fun {A : Type'} {B : Type'} {_ : ord_class_pred B}
  (f g : A -> B) : Prop := less_eq f g.
Definition ord_fun_inst_less_fun {A : Type'} {B : Type'} {_ : ord_class_pred B}
  (f g : A -> B) : Prop := less f g.
Definition bot_fun_inst_bot_fun {A : Type'} (B : Type') {_ : bot_class_pred B} : A -> B :=
  bot.
Definition top_fun_inst_top_fun {A : Type'} (B : Type') {_ : top_class_pred B} : A -> B :=
  top_class_top.

Lemma ord_bool_inst_less_eq_bool_def : @eq (Prop -> Prop -> Prop) (@less_eq Prop _) imp.
Proof. by funext=>> ; rewrite [LHS]asboolE. Qed.
Lemma le_fun_def_raw (A B : Type') {_ : ord_class_pred B} : @eq ((A -> B) -> (A -> B) -> Prop) (@ord_fun_inst_less_eq_fun A B _) (fun f g : A -> B => forall x : A, @less_eq B _ (f x) (g x)).
Proof.
  by funext=> * ; rewrite/ord_fun_inst_less_eq_fun/less_eq/= asboolE.
Qed.
Lemma ord_bool_inst_less_bool_def : @eq (Prop -> Prop -> Prop) (@less Prop _) ord_bool_inst_less_bool.
Proof. by funext=>> ; rewrite [LHS]asboolE. Qed.
Lemma less_fun_def_raw (A B : Type') {_ : ord_class_pred B} : @eq ((A -> B) -> (A -> B) -> Prop) (@ord_fun_inst_less_fun A B _) (fun f g : A -> B => and (@less_eq (A -> B) _ f g) (not (@less_eq (A -> B) _ g f))).
Proof.
  by funext=> * ; rewrite/ord_fun_inst_less_fun/less/less_eq/= -andP** -negP**.
Qed.

Lemma bot_bool_inst_bot_bool_def : @eq Prop (@bot Prop _) False.
Proof. reflexivity. Qed.
Lemma top_bool_inst_top_bool_def : @eq Prop (@top_class_top Prop _) True.
Proof. reflexivity. Qed.
Lemma ord_fun_inst_less_eq_fun_def : forall A : Type', forall B : Type', forall {wildcard_33 : ord_class_pred B}, @eq ((A -> B) -> (A -> B) -> Prop) (@less_eq (A -> B) _) (@ord_fun_inst_less_eq_fun A B _).
Proof. reflexivity. Qed.
Lemma ord_fun_inst_less_fun_def : forall A : Type', forall B : Type', forall {wildcard_34 : ord_class_pred B}, @eq ((A -> B) -> (A -> B) -> Prop) (@less (A -> B) _) (@ord_fun_inst_less_fun A B _).
Proof. reflexivity. Qed.
Lemma bot_fun_inst_bot_fun_def : forall A : Type', forall B : Type', forall {wildcard_35 : bot_class_pred B}, @eq (A -> B) (@bot (A -> B) _) (@bot_fun_inst_bot_fun A B _).
Proof. reflexivity. Qed.
Lemma top_fun_inst_top_fun_def : forall A : Type', forall B : Type', forall {wildcard_36 : top_class_pred B}, @eq (A -> B) (@top_class_top (A -> B) _) (@top_fun_inst_top_fun A B _).
Proof. reflexivity. Qed.

(*** Class definitions ***)

Definition ord_class (A : Type')  {_ : ord_class_pred A} : Prop := True.
Arguments ord_class _ {_}.
Definition top_class (A : Type') {_ : top_class_pred A} : Prop := True.
Arguments top_class _ {_}.
Definition bot_class (A : Type') {_ : bot_class_pred A} : Prop := True.
Arguments bot_class _ {_}.

Lemma ord_class_def (A : Type') {wildcard_59 : ord_class_pred A} : @eq Prop (ord_class A) (type_class A).
Proof. reflexivity. Qed.
Lemma bot_class_def (A : Type') {wildcard_59 : bot_class_pred A} : @eq Prop (bot_class A) (type_class A).
Proof. reflexivity. Qed.
Lemma top_class_def (A : Type') {wildcard_59 : top_class_pred A} : @eq Prop (top_class A) (type_class A).
Proof. reflexivity. Qed.

Lemma ord_class_type_def (A : pPreorderType default_display) : ord_class A.
Proof. by []. Qed.
Lemma bot_class_type_def (A : pbPreorderType default_display) : bot_class A.
Proof. by []. Qed.
Lemma top_class_type_def (A : ptPreorderType default_display) : top_class A.
Proof. by []. Qed.

Lemma iffE : eq = iff.
Proof. by ext=> [> ->|> []|> []]. Qed.

(* Propositional relations and link with mathcomp's boolean ones *)
Section Prelations.
Context {A : Type}.
Implicit Types (R le lt : A -> A -> Prop).

Definition Preflexive R : Prop := forall x, R x x.

Lemma PreflexiveE : Preflexive = @reflexive A.
Proof. by ext=> * ? ; apply/asboolP. Qed.

Lemma reflexiveE : @reflexive A = Preflexive.
Proof. reflexivity. Qed.

Definition Ptransitive R : Prop := forall z x y, R x z -> R z y -> R x y.

Lemma PtransitiveE : Ptransitive = @transitive A.
Proof. ext=> ? HTr ?> /asboolP /HTr {}HTr /asboolP /HTr ? ; exact/asboolP. Qed.

Lemma transitiveE : @transitive A = Ptransitive.
Proof. reflexivity. Qed.

Definition is_lt_of lt le := forall x y, lt x y <-> le x y /\ ~le y x.

Definition Preorder le lt : Prop :=
  is_lt_of lt le /\ Preflexive le /\ Ptransitive le.

Lemma PreorderP {le lt} :
  Preorder le lt <-> (is_lt_of lt le /\ wochoice.preorder le).
Proof. by rewrite/Preorder PreflexiveE PtransitiveE. Qed.

Lemma preorderP {leb} :
  @wochoice.preorder A leb <-> Preorder leb (fun x y => leb x y && ~~ leb y x).
Proof.
  rewrite/wochoice.preorder reflexiveE transitiveE.
  by split=> [|[_]] [] ; split => // ? ? ; rewrite -andP** -negP**.
Qed.

Definition Pantisymmetric R : Prop := forall x y, R x y -> R y x -> x = y.

Lemma PantisymmetricE : Pantisymmetric = @antisymmetric A.
Proof.
  ext=> ? HAs ? ? => [/andP []|] /asboolP ? /asboolP ? ; first exact:HAs.
  exact/HAs/andP.
Qed.

Lemma antisymmetricP (R : rel A) : antisymmetric R <-> Pantisymmetric R.
Proof.
  by split=> HAs ? ? => [|/andP []] * ; apply: HAs ; first apply/andP.
Qed.

Lemma antisymmetricE : @antisymmetric A = Pantisymmetric.
Proof. by funext=>> /` /antisymmetricP. Qed.

Definition Porder le lt := Preorder le lt /\ Pantisymmetric le.

Lemma PorderP {le lt} :
  Porder le lt <-> (is_lt_of lt le /\ wochoice.partial_order le).
Proof. by rewrite/Porder PreorderP** -andA PantisymmetricE. Qed.

Lemma partial_orderP {leb} :
  @wochoice.partial_order A leb <-> Porder leb (fun x y => leb x y && ~~ leb y x).
Proof.
  by rewrite/wochoice.partial_order preorderP** antisymmetricE.
Qed.

Definition Ptotal R : Prop := forall x y, R x y \/ R y x.

Lemma PtotalE : Ptotal = @total A.
Proof.
  by ext=> ?+ x y =>/[spec x|y]=>[+ /ltac:(apply/orP)|/orP]; rewrite 2!asboolE.
Qed.

Lemma totalP (R : rel A) : total R <-> Ptotal R.
Proof.
  by split=> + x y => /[spec x | y] => [/orP | + /ltac:(apply/orP)].
Qed.

Lemma totalE : @total A = Ptotal.
Proof. by funext=>> /` /totalP. Qed.

Definition Ptotal_order le lt := Porder le lt /\ Ptotal le.

Lemma Ptotal_orderP {le lt} :
  Ptotal_order le lt <-> (is_lt_of lt le /\ wochoice.total_order le).
Proof. by rewrite/Ptotal_order PorderP** -andA PtotalE. Qed.

Lemma total_orderP {leb} :
  @wochoice.total_order A leb <-> Ptotal_order leb (fun x y => leb x y && ~~ leb y x).
Proof.
  by rewrite/wochoice.total_order partial_orderP** totalE.
Qed.

Definition Pminimal x R := forall y, R x y.

Lemma PminimalP R x : Pminimal x R -> wochoice.minimal R x.
Proof. by move=> ? ? _ ; rewrite asboolE. Qed.

Definition Pmaximal R x := forall y, R y x.

Lemma PmaximalP R x : Pmaximal R x -> wochoice.maximal R x.
Proof. by move=> ? ? _ ; rewrite asboolE. Qed.

End Prelations.

Unset Implicit Arguments.

Lemma class_preorder_def (A : Type') (le : A -> A -> Prop) (lt : A -> A -> Prop) : @eq Prop (@Preorder A le lt) (and (forall x : A, forall y : A, @eq Prop (lt x y) (and (le x y) (not (le y x)))) (and (forall x : A, le x x) (forall x : A, forall y : A, forall z : A, (le x y) -> (le y z) -> le x z))).
Proof.
  by congr and ; [ rewrite iffE | congr and => /` H > /H /[apply] ].
Qed.

Definition preorder_class (A : Type') {_ : ord_class_pred A} : Prop := Preorder less_eq less.

Lemma preorder_class_def (A : Type') {_ : ord_class_pred A} : @eq Prop (preorder_class A) (and (ord_class A) (Trueprop (@Preorder A (@less_eq A _) (@less A _)))).
Proof. by rewrite andB. Qed.

Lemma is_lt_ofP d (T : preorderType d) : @is_lt_of T lt le.
Proof.
  by move=> * ; rewrite [X in is_true X]Order.lt_def -andP** -negP**.
Qed.

Lemma preorder_class_type_def (A : pPreorderType default_display) : preorder_class A.
Proof.
  split ; [exact:is_lt_ofP | split ; [exact: le_refl | exact: le_trans]].
Qed.

Lemma class_order_axioms_def (A : Type') (less_eq : A -> A -> Prop) : @eq Prop (@Pantisymmetric A less_eq) (forall x : A, forall y : A, (less_eq x y) -> (less_eq y x) -> @eq A x y).
Proof. reflexivity. Qed.

Definition order_class (A : Type') {_ : ord_class_pred A} : Prop := Porder less_eq less.

Lemma order_class_def (A : Type') {_ : ord_class_pred A} : @eq Prop (order_class A) (and (preorder_class A) (Trueprop (@Pantisymmetric A (@less_eq A _)))).
Proof. reflexivity. Qed.

Lemma order_class_type_def (A : pPOrderType default_display) : order_class A.
Proof.
  split ; [exact: preorder_class_type_def | exact/antisymmetricP/le_anti].
Qed.

Lemma class_linorder_axioms_def (A : Type') (less_eq : A -> A -> Prop) : @eq Prop (@Ptotal A less_eq) (forall x : A, forall y : A, or (less_eq x y) (less_eq y x)).
Proof. reflexivity. Qed.

Definition linorder_class (A : Type') {_ : ord_class_pred A} : Prop := Ptotal_order less_eq less.

Lemma linorder_class_def (A : Type') {_ : ord_class_pred A} : @eq Prop (linorder_class A) (and (order_class A) (Trueprop (@Ptotal A (@less_eq A _)))).
Proof. reflexivity. Qed.

Lemma linorder_class_type_def (A : pOrderType default_display) : linorder_class A.
Proof.
  split ; [exact: order_class_type_def | exact/totalP/le_total].
Qed.

Lemma class_order_bot_axioms_def (A : Type') (bot : A) (less_eq : A -> A -> Prop) : @eq Prop (@Pminimal A bot less_eq) (@all A (less_eq bot)).
Proof. reflexivity. Qed.

Definition order_bot_class (A : Type') {_ : order_bot_class_pred A} : Prop := order_class A /\ Pminimal (bot : A) less_eq.

Lemma order_bot_class_def (A : Type') {_ : order_bot_class_pred A} : @eq Prop (order_bot_class A) (and (bot_class A) (and (order_class A) (Trueprop (@Pminimal A (@bot A _) (@less_eq A _))))).
Proof. by rewrite andB. Qed.

Lemma order_bot_class_type_def (A : pbPOrderType default_display) : order_bot_class A.
Proof. split ; [exact: order_class_type_def | exact: le0x]. Qed.

Lemma class_order_top_axioms_def (A : Type') (less_eq : A -> A -> Prop) (top : A) : @eq Prop (@Pmaximal A less_eq top) (forall a : A, less_eq a top).
Proof. reflexivity. Qed.

Definition order_top_class (A : Type') {_ : order_top_class_pred A} : Prop :=
  order_class A /\ Pmaximal less_eq (top_class_top : A).

Lemma order_top_class_def (A : Type') {_ : order_top_class_pred A} : @eq Prop (order_top_class A) (and (order_class A) (and (top_class A) (Trueprop (@Pmaximal A (@less_eq A _) (@top_class_top A _))))).
Proof. by rewrite andB. Qed.

Lemma order_top_class_type_def (A : ptPOrderType default_display) : order_top_class A.
Proof. split ; [exact: order_class_type_def | exact: lex1]. Qed.

Definition class_dense_order_axioms {A : Type'} (lt : A -> A -> Prop) : Prop :=
  forall x z, lt x z -> exists y, lt x y /\ lt y z.

Lemma class_dense_order_axioms_def (A : Type') (less : A -> A -> Prop) : @eq Prop (@class_dense_order_axioms A less) (forall x : A, forall y : A, (less x y) -> exists z : A, and (less x z) (less z y)).
Proof. reflexivity. Qed.

Definition dense_order_class (A : Type') {_ : ord_class_pred A} : Prop :=
  order_class A /\ class_dense_order_axioms less.

Lemma dense_order_class_def (A : Type') {_ : ord_class_pred A} : @eq Prop (dense_order_class A) (and (order_class A) (Trueprop (@class_dense_order_axioms A (@less A _)))).
Proof. reflexivity. Qed.

Lemma dense_order_class_type_def (A : dense_order_class_type default_display) : dense_order_class A.
Proof. split ; [exact: order_class_type_def | exact: lt_dense]. Qed.

Definition dense_linorder_class (A : Type') {_ : ord_class_pred A} : Prop :=
  linorder_class A /\ class_dense_order_axioms less.

Lemma dense_linorder_class_def (A : Type') {_ : ord_class_pred A} : @eq Prop (dense_linorder_class A) (and (dense_order_class A) (linorder_class A)).
Proof. by ext=> -[[]] ; split. Qed.

Lemma dense_linorder_class_type_def (A : dense_linorder_class_type default_display) : dense_linorder_class A.
Proof. split ; [exact: linorder_class_type_def | exact: lt_dense]. Qed.

Definition class_no_top_axioms {A : Type'} (lt: (A -> A -> Prop)) : Prop :=
  forall x, exists y, lt x y.
Definition class_no_bot_axioms {A : Type'} (lt: (A -> A -> Prop)) : Prop :=
  forall x, exists y, lt y x.

Lemma class_no_top_axioms_def (A : Type') (less : A -> A -> Prop) : @eq Prop (@class_no_top_axioms A less) (forall x : A, @ex A (less x)).
Proof. reflexivity. Qed.
Lemma class_no_bot_axioms_def (A : Type') (less : A -> A -> Prop) : @eq Prop (@class_no_bot_axioms A less) (forall x : A, exists y : A, less y x).
Proof. reflexivity. Qed.

Definition no_top_class (A : Type') {_ : ord_class_pred A} : Prop :=
  order_class A /\ class_no_top_axioms less.
Definition no_bot_class (A : Type') {_ : ord_class_pred A} : Prop :=
  order_class A /\ class_no_bot_axioms less.

Lemma no_top_class_def (A : Type') {_ : ord_class_pred A} : @eq Prop (no_top_class A) (and (order_class A) (Trueprop (@class_no_top_axioms A (@less A _)))).
Proof. reflexivity. Qed.
Lemma no_bot_class_def (A : Type') {_ : ord_class_pred A} : @eq Prop (no_bot_class A) (and (order_class A) (Trueprop (@class_no_bot_axioms A (@less A _)))).
Proof. reflexivity. Qed.

Lemma no_top_class_type_def (A : no_top_class_type default_display) : no_top_class A.
Proof. split ; [exact: order_class_type_def | exact: gt_ex]. Qed.
Lemma no_bot_class_type_def (A : no_bot_class_type default_display) : no_bot_class A.
Proof. split ; [exact: order_class_type_def | exact: lt_ex]. Qed.

Definition unbounded_dense_linorder_class (A : Type') {_ : ord_class_pred A} : Prop :=
  dense_linorder_class A /\ class_no_top_axioms less /\ class_no_bot_axioms less.

Lemma unbounded_dense_linorder_class_def (A : Type') {_ : ord_class_pred A} : @eq Prop (unbounded_dense_linorder_class A) (and (dense_linorder_class A) (and (no_bot_class A) (no_top_class A))).
Proof. by ext=> -[[[? ?] ?]]=> [[]|[[_ ?] [_]]]. Qed.

Lemma unbounded_dense_linorder_class_type_def (A : unbounded_dense_linorder_class_type default_display) : unbounded_dense_linorder_class A.
Proof.
  split ; first exact: dense_linorder_class_type_def.
  split ; [exact: gt_ex | exact: lt_ex].
Qed.

Lemma class_wellorder_axioms_def (A : Type') (lt : A -> A -> Prop) : @eq Prop (@well_founded A lt) (forall P : A -> Prop, forall a : A, (forall x : A, (forall y : A, (lt y x) -> P y) -> P x) -> P a).
Proof.
  ext=> ltwf=> [P x IHlt | x] ; last exact/(ltwf (Acc lt))/Acc_intro.
  elim: x/ltwf=> * ; exact: IHlt.
Qed.

Definition wellorder_class (A : Type') {_ : ord_class_pred A} : Prop :=
  linorder_class A /\ well_founded less.

Lemma wellorder_class_def (A : Type') {wildcard_54 : ord_class_pred A} : @eq Prop (wellorder_class A) (and (linorder_class A) (Trueprop (@well_founded A (@less A _)))).
Proof. reflexivity. Qed.

Lemma wellorder_class_type_def (A : wellorder_class_type default_display) : wellorder_class A.
Proof. split ; [exact: linorder_class_type_def | exact: wf_lt]. Qed.

Set Implicit Arguments.
(****************************************************************************)
(* HOL.Groups. *)
(****************************************************************************)

(*** Class predicates ***)

HB.mixin Record zero_class_mixin (A : Type') T := { zero_class_zero : A }.

#[short (type = zero_class_pred)]
HB.structure Definition zero_class_ (A : Type') := { T of zero_class_mixin A T }.

HB.mixin Record one_class_mixin (A : Type') T := { one_class_one : A }.

#[short (type = one_class_pred)]
HB.structure Definition one_class_ (A : Type') := { T of one_class_mixin A T }.

HB.mixin Record plus_class_mixin (A : Type') T := { plus : A -> A -> A }.

#[short (type = plus_class_pred)]
HB.structure Definition plus_class_ (A : Type') := { T of plus_class_mixin A T }.

HB.mixin Record minus_class_mixin (A : Type') T := { minus : A -> A -> A }.

#[short (type = minus_class_pred)]
HB.structure Definition minus_class_ (A : Type') := { T of minus_class_mixin A T }.

HB.mixin Record uminus_class_mixin (A : Type') T := { uminus : A -> A }.

#[short (type = uminus_class_pred)]
HB.structure Definition uminus_class_ (A : Type') := { T of uminus_class_mixin A T }.

HB.mixin Record times_class_mixin (A : Type') T := { times : A -> A -> A }.

#[short (type = times_class_pred)]
HB.structure Definition times_class_ (A : Type') := { T of times_class_mixin A T }.

HB.mixin Record abs_class_mixin (A : Type') T := { abs : A -> A }.

#[short (type = abs_class_pred)]
HB.structure Definition abs_class_ (A : Type') := { T of abs_class_mixin A T }.

HB.mixin Record sgn_class_mixin (A : Type') T := { sgn : A -> A }.

#[short (type = sgn_class_pred)]
HB.structure Definition sgn_class_ (A : Type') := { T of sgn_class_mixin A T }.

#[short (type = monoid_mult_class_pred)]
HB.structure Definition monoid_mult_class_ (A : Type') :=
  { T of times_class_ A T & one_class_ A T }.

#[short (type = monoid_add_class_pred)]
HB.structure Definition monoid_add_class_ (A : Type') :=
  { T of plus_class_ A T & zero_class_ A T }.

#[short (type = cancel_ab_semigroup_add_class_pred)]
HB.structure Definition cancel_ab_semigroup_add_class_ (A : Type') :=
  { T of plus_class_ A T & minus_class_ A T }.

#[short (type = cancel_comm_monoid_add_class_pred)]
HB.structure Definition cancel_comm_monoid_add_class_ (A : Type') :=
  { T of monoid_add_class_ A T & minus_class_ A T }.

#[short (type = group_add_class_pred)]
HB.structure Definition group_add_class_ (A : Type') :=
  { T of cancel_comm_monoid_add_class_ A T & uminus_class_ A T }.

#[short (type = ordered_ab_semigroup_add_class_pred)]
HB.structure Definition ordered_ab_semigroup_add_class_ (A : Type') :=
  { T of plus_class_ A T & ord_class_ A T }.

#[short (type = ordered_comm_monoid_add_class_pred)]
HB.structure Definition ordered_comm_monoid_add_class_ (A : Type') :=
  { T of monoid_add_class_ A T & ord_class_ A T }.

#[short (type = ordered_cancel_ab_semigroup_add_class_pred)]
HB.structure Definition ordered_cancel_ab_semigroup_add_class_ (A : Type') :=
  { T of cancel_ab_semigroup_add_class_ A T & ord_class_ A T }.

#[short (type = ordered_cancel_comm_monoid_add_class_pred)]
HB.structure Definition ordered_cancel_comm_monoid_add_class_ (A : Type') :=
  { T of cancel_comm_monoid_add_class_ A T & ord_class_ A T }.

#[short (type = ordered_ab_group_add_class_pred)]
HB.structure Definition ordered_ab_group_add_class_ (A : Type') :=
  { T of group_add_class_ A T & ord_class_ A T }.

#[short (type = ordered_ab_group_add_abs_class_pred)]
HB.structure Definition ordered_ab_group_add_abs_class_ (A : Type') :=
  { T of ordered_ab_group_add_class_ A T & abs_class_ A T }.

Existing Class sgn_class_pred.
Existing Class cancel_ab_semigroup_add_class_pred.
Existing Class ordered_ab_group_add_abs_class_pred.
Existing Class abs_class_pred.
Existing Class one_class_pred.
Existing Class minus_class_pred.
Existing Class ordered_ab_group_add_class_pred.
Existing Class monoid_add_class_pred.
Existing Class ordered_cancel_comm_monoid_add_class_pred.
Existing Class ordered_comm_monoid_add_class_pred.
Existing Class zero_class_pred.
Existing Class uminus_class_pred.
Existing Class ordered_cancel_ab_semigroup_add_class_pred.
Existing Class monoid_mult_class_pred.
Existing Class group_add_class_pred.
Existing Class cancel_comm_monoid_add_class_pred.
Existing Class ordered_ab_semigroup_add_class_pred.
Existing Class times_class_pred.
Existing Class plus_class_pred.

Instance minus_class_pred_of_cancel_ab_semigroup_add_class_pred A :
  (cancel_ab_semigroup_add_class_pred A) -> minus_class_pred A := id.
Instance plus_class_pred_of_cancel_ab_semigroup_add_class_pred A :
  (cancel_ab_semigroup_add_class_pred A) -> plus_class_pred A := id.
Instance cancel_ab_semigroup_add_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> cancel_ab_semigroup_add_class_pred A := id.
Instance abs_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> abs_class_pred A := id.
Instance minus_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> minus_class_pred A := id.
Instance ordered_ab_group_add_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> ordered_ab_group_add_class_pred A := id.
Instance monoid_add_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> monoid_add_class_pred A := id.
Instance ordered_cancel_comm_monoid_add_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> ordered_cancel_comm_monoid_add_class_pred A := id.
Instance ordered_comm_monoid_add_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> ordered_comm_monoid_add_class_pred A := id.
Instance zero_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> zero_class_pred A := id.
Instance uminus_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> uminus_class_pred A := id.
Instance ordered_cancel_ab_semigroup_add_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> ordered_cancel_ab_semigroup_add_class_pred A := id.
Instance group_add_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> group_add_class_pred A := id.
Instance cancel_comm_monoid_add_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> cancel_comm_monoid_add_class_pred A := id.
Instance ord_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> ord_class_pred A := id.
Instance ordered_ab_semigroup_add_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> ordered_ab_semigroup_add_class_pred A := id.
Instance plus_class_pred_of_ordered_ab_group_add_abs_class_pred A :
  (ordered_ab_group_add_abs_class_pred A) -> plus_class_pred A := id.
Instance cancel_ab_semigroup_add_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> cancel_ab_semigroup_add_class_pred A := id.
Instance minus_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> minus_class_pred A := id.
Instance monoid_add_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> monoid_add_class_pred A := id.
Instance ordered_cancel_comm_monoid_add_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> ordered_cancel_comm_monoid_add_class_pred A := id.
Instance ordered_comm_monoid_add_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> ordered_comm_monoid_add_class_pred A := id.
Instance zero_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> zero_class_pred A := id.
Instance uminus_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> uminus_class_pred A := id.
Instance ordered_cancel_ab_semigroup_add_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> ordered_cancel_ab_semigroup_add_class_pred A := id.
Instance group_add_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> group_add_class_pred A := id.
Instance cancel_comm_monoid_add_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> cancel_comm_monoid_add_class_pred A := id.
Instance ord_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> ord_class_pred A := id.
Instance ordered_ab_semigroup_add_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> ordered_ab_semigroup_add_class_pred A := id.
Instance plus_class_pred_of_ordered_ab_group_add_class_pred A :
  (ordered_ab_group_add_class_pred A) -> plus_class_pred A := id.
Instance zero_class_pred_of_monoid_add_class_pred A :
  (monoid_add_class_pred A) -> zero_class_pred A := id.
Instance plus_class_pred_of_monoid_add_class_pred A :
  (monoid_add_class_pred A) -> plus_class_pred A := id.
Instance cancel_ab_semigroup_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred A :
  (ordered_cancel_comm_monoid_add_class_pred A) -> cancel_ab_semigroup_add_class_pred A := id.
Instance minus_class_pred_of_ordered_cancel_comm_monoid_add_class_pred A :
  (ordered_cancel_comm_monoid_add_class_pred A) -> minus_class_pred A := id.
Instance monoid_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred A :
  (ordered_cancel_comm_monoid_add_class_pred A) -> monoid_add_class_pred A := id.
Instance ordered_comm_monoid_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred A :
  (ordered_cancel_comm_monoid_add_class_pred A) -> ordered_comm_monoid_add_class_pred A := id.
Instance zero_class_pred_of_ordered_cancel_comm_monoid_add_class_pred A :
  (ordered_cancel_comm_monoid_add_class_pred A) -> zero_class_pred A := id.
Instance ordered_cancel_ab_semigroup_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred A :
  (ordered_cancel_comm_monoid_add_class_pred A) -> ordered_cancel_ab_semigroup_add_class_pred A := id.
Instance cancel_comm_monoid_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred A :
  (ordered_cancel_comm_monoid_add_class_pred A) -> cancel_comm_monoid_add_class_pred A := id.
Instance ord_class_pred_of_ordered_cancel_comm_monoid_add_class_pred A :
  (ordered_cancel_comm_monoid_add_class_pred A) -> ord_class_pred A := id.
Instance ordered_ab_semigroup_add_class_pred_of_ordered_cancel_comm_monoid_add_class_pred A :
  (ordered_cancel_comm_monoid_add_class_pred A) -> ordered_ab_semigroup_add_class_pred A := id.
Instance plus_class_pred_of_ordered_cancel_comm_monoid_add_class_pred A :
  (ordered_cancel_comm_monoid_add_class_pred A) -> plus_class_pred A := id.
Instance monoid_add_class_pred_of_ordered_comm_monoid_add_class_pred A :
  (ordered_comm_monoid_add_class_pred A) -> monoid_add_class_pred A := id.
Instance zero_class_pred_of_ordered_comm_monoid_add_class_pred A :
  (ordered_comm_monoid_add_class_pred A) -> zero_class_pred A := id.
Instance ord_class_pred_of_ordered_comm_monoid_add_class_pred A :
  (ordered_comm_monoid_add_class_pred A) -> ord_class_pred A := id.
Instance ordered_ab_semigroup_add_class_pred_of_ordered_comm_monoid_add_class_pred A :
  (ordered_comm_monoid_add_class_pred A) -> ordered_ab_semigroup_add_class_pred A := id.
Instance plus_class_pred_of_ordered_comm_monoid_add_class_pred A :
  (ordered_comm_monoid_add_class_pred A) -> plus_class_pred A := id.
Instance cancel_ab_semigroup_add_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred A :
  (ordered_cancel_ab_semigroup_add_class_pred A) -> cancel_ab_semigroup_add_class_pred A := id.
Instance minus_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred A :
  (ordered_cancel_ab_semigroup_add_class_pred A) -> minus_class_pred A := id.
Instance ord_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred A :
  (ordered_cancel_ab_semigroup_add_class_pred A) -> ord_class_pred A := id.
Instance ordered_ab_semigroup_add_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred A :
  (ordered_cancel_ab_semigroup_add_class_pred A) -> ordered_ab_semigroup_add_class_pred A := id.
Instance plus_class_pred_of_ordered_cancel_ab_semigroup_add_class_pred A :
  (ordered_cancel_ab_semigroup_add_class_pred A) -> plus_class_pred A := id.
Instance one_class_pred_of_monoid_mult_class_pred A :
  (monoid_mult_class_pred A) -> one_class_pred A := id.
Instance times_class_pred_of_monoid_mult_class_pred A :
  (monoid_mult_class_pred A) -> times_class_pred A := id.
Instance cancel_ab_semigroup_add_class_pred_of_group_add_class_pred A :
  (group_add_class_pred A) -> cancel_ab_semigroup_add_class_pred A := id.
Instance minus_class_pred_of_group_add_class_pred A :
  (group_add_class_pred A) -> minus_class_pred A := id.
Instance monoid_add_class_pred_of_group_add_class_pred A :
  (group_add_class_pred A) -> monoid_add_class_pred A := id.
Instance zero_class_pred_of_group_add_class_pred A :
  (group_add_class_pred A) -> zero_class_pred A := id.
Instance uminus_class_pred_of_group_add_class_pred A :
  (group_add_class_pred A) -> uminus_class_pred A := id.
Instance cancel_comm_monoid_add_class_pred_of_group_add_class_pred A :
  (group_add_class_pred A) -> cancel_comm_monoid_add_class_pred A := id.
Instance plus_class_pred_of_group_add_class_pred A :
  (group_add_class_pred A) -> plus_class_pred A := id.
Instance cancel_ab_semigroup_add_class_pred_of_cancel_comm_monoid_add_class_pred A :
  (cancel_comm_monoid_add_class_pred A) -> cancel_ab_semigroup_add_class_pred A := id.
Instance minus_class_pred_of_cancel_comm_monoid_add_class_pred A :
  (cancel_comm_monoid_add_class_pred A) -> minus_class_pred A := id.
Instance monoid_add_class_pred_of_cancel_comm_monoid_add_class_pred A :
  (cancel_comm_monoid_add_class_pred A) -> monoid_add_class_pred A := id.
Instance zero_class_pred_of_cancel_comm_monoid_add_class_pred A :
  (cancel_comm_monoid_add_class_pred A) -> zero_class_pred A := id.
Instance plus_class_pred_of_cancel_comm_monoid_add_class_pred A :
  (cancel_comm_monoid_add_class_pred A) -> plus_class_pred A := id.
Instance ord_class_pred_of_ordered_ab_semigroup_add_class_pred A :
  (ordered_ab_semigroup_add_class_pred A) -> ord_class_pred A := id.
Instance plus_class_pred_of_ordered_ab_semigroup_add_class_pred A :
  (ordered_ab_semigroup_add_class_pred A) -> plus_class_pred A := id.

Open Scope group_scope.
Open Scope ring_scope.

#[short(type=plus_class_type)]
HB.structure Definition plus_class_struct :=
  { T of Algebra.BaseAddMagma T & Pointed T }.

#[short(type=semigroup_add_class_type)]
HB.structure Definition semigroup_add_class_struct := 
  { T of Algebra.AddSemigroup T & Pointed T }.

Definition subtract {T : baseZmodType} (x y : T) := x - y.

#[short(type=times_class_type)]
HB.structure Definition times_class_struct := 
  { T of ChoiceMagma T & Pointed T }.

#[short(type=semigroup_mult_class_type)]
HB.structure Definition semigroup_mult_class_struct := 
  { T of Semigroup T & Pointed T }.

#[short(type=one_class_type)]
HB.structure Definition one_class_struct :=
  { T of ChoiceBaseUMagma T & Pointed T }.

HB.mixin Record ab_semigroup_mult_class_content T & Magma T := {
  mulgC : commutative (@mul T)
}.

#[short(type=ab_semigroup_mult_class_type)]
HB.structure Definition ab_semigroup_mult_class_struct := 
  { T of ab_semigroup_mult_class_content T & semigroup_mult_class_struct T }.

#[short(type=monoid_mult_class_type)]
HB.structure Definition monoid_mult_class_struct := 
  { T of Monoid T & Pointed T }.

#[short(type=comm_monoid_mult_class_type)]
HB.structure Definition comm_monoid_mult_class_struct := 
  { T of monoid_mult_class_struct T & ab_semigroup_mult_class_content T }.

(* Trivial group (default solution unless it is possible to
   define the correct structures low in the hierarchy) *)
HB.mixin Record comm_monoid_diff_class_content T & Pointed T := {
  all_eq0 : @all_equal_to T point
}.

#[short(type=comm_monoid_diff_class_type)]
HB.structure Definition comm_monoid_diff_class_struct :=
  { T of comm_monoid_diff_class_content T & Pointed T }.

HB.mixin Record canonically_ordered_monoid_add_class_content T & Num.POrderNmodule T := {
  le_diff_pos x y : x <= y <-> exists z : T, y = x + z
}.

#[short(type=canonically_ordered_monoid_add_class_type)]
HB.structure Definition canonically_ordered_monoid_add_class_struct :=
  {T of canonically_ordered_monoid_add_class_content T & Num.POrderedNmodule T}.

(* Couldn't manage to use HB.reexport so did it by hand. *)
Module Triv_group.
Module Theory.
Section Theory.
Context {T : comm_monoid_diff_class_type}.
Local Notation "'0'" := (point : T).
Local Notation "'+%T'" := (fun _ _ : T => point : T).
Local Infix "+" := +%T.
Local Notation "<=%T" := (fun _ _ : T => true).
Local Infix "<=" := <=%T.

Lemma addrA : associative +%T. Proof. by []. Qed.
Lemma addrC : commutative +%T. Proof. by []. Qed.
Lemma add0r : left_id 0 +%T. Proof. by move=>> ; rewrite 2! all_eq0. Qed.

Lemma addNr : left_inverse 0 (fun=> 0) +%T.
Proof. by move=>> ; rewrite all_eq0. Qed.

Lemma le_refl : reflexive <=%T.
Proof. by []. Qed.
Lemma le_anti : antisymmetric <=%T.
Proof. by move=>> _ ; rewrite 2!all_eq0. Qed.
Lemma le_trans : transitive <=%T.
Proof. by []. Qed.
Lemma ler_wD2l x : {homo +%T x : y z / y <= z}.
Proof. by []. Qed.
Lemma le_diff_pos x y : x <= y <-> exists z, y = x + z.
Proof. split=> // ? ; exists x ; exact:all_eq0. Qed.
End Theory.
End Theory.

Module Exports.
Import Theory.
HB.instance Definition _ (T : comm_monoid_diff_class_type) :=
  Algebra.isNmodule.Build T addrA addrC add0r.
HB.instance Definition _ (T : comm_monoid_diff_class_type) :=
  Algebra.Nmodule_isZmodule.Build T addNr.
HB.instance Definition _ (T : comm_monoid_diff_class_type) :=
  Order.Le_isPOrder.Build default_display T le_refl le_anti le_trans.
HB.instance Definition _ (T : comm_monoid_diff_class_type) :=
  Num.Add_isHomo.Build T ler_wD2l.
HB.instance Definition _ (T : comm_monoid_diff_class_type) :=
  canonically_ordered_monoid_add_class_content.Build T le_diff_pos.
End Exports.
End Triv_group.

Export Triv_group.Exports.

Local Notation "'P0.on' T" := (isPointed.Build T 0) (at level 200).

HB.instance Definition _ (T : Algebra.ChoiceBaseAddUMagma.type) := P0.on T.
HB.instance Definition _ (T : addUMagmaType) := P0.on T.
HB.instance Definition _ (T : nmodType) := P0.on T.
HB.instance Definition _ (T : zmodType) := P0.on T.
HB.instance Definition _ (T : comm_monoid_diff_class_type) := P0.on T.
HB.instance Definition _ (T : porderedNmodType) := P0.on T.
HB.instance Definition _ (T : canonically_ordered_monoid_add_class_type) :=
  P0.on T.
HB.instance Definition _ (T : porderedZmodType) := P0.on T.
HB.instance Definition _ (T : orderedNmodType) := P0.on T.
HB.instance Definition _ (T : orderedZmodType) := P0.on T.
HB.instance Definition _ (T : numDomainType) := P0.on T.
HB.instance Definition _ (T : realDomainType) := P0.on T.

(*** Class instances ***)

HB.instance Definition _ (T : Algebra.ChoiceBaseAddUMagma.type) :=
  zero_class_mixin.Build T fodder 0.
HB.instance Definition _ (T : one_class_type) :=
  one_class_mixin.Build T fodder monoid.one.
HB.instance Definition _ (T : plus_class_type) :=
  plus_class_mixin.Build T fodder +%R.
HB.instance Definition _ (T : zmodType) :=
  minus_class_mixin.Build T fodder subtract.
HB.instance Definition _ (T : zmodType) :=
  uminus_class_mixin.Build T fodder -%R.
HB.instance Definition _ (T : times_class_type) :=
  times_class_mixin.Build T fodder mul.
HB.saturate fodder.
HB.instance Definition _ (T : comm_monoid_diff_class_type) :=
  plus_class_mixin.Build T fodder3 +%R.
HB.instance Definition _ (T : comm_monoid_diff_class_type) :=
  minus_class_mixin.Build T fodder3 subtract.
HB.instance Definition _ (T : comm_monoid_diff_class_type) :=
  zero_class_mixin.Build T fodder3 0.
HB.instance Definition _ (T : comm_monoid_diff_class_type) :=
  ord_class_mixin.Build T fodder3 <=%O <%O.
HB.instance Definition _ (T : porderedNmodType) :=
  ord_class_mixin.Build T fodder4 <=%O <%O.
HB.instance Definition _ (T : porderedNmodType) :=
  plus_class_mixin.Build T fodder4 +%R.
HB.instance Definition _ (T : porderedNmodType) :=
  zero_class_mixin.Build T fodder4 0.
HB.instance Definition _ (T : porderedZmodType) :=
  uminus_class_mixin.Build T fodder4 -%R.
HB.instance Definition _ (T : porderedZmodType) :=
  minus_class_mixin.Build T fodder4 subtract.
HB.instance Definition _ (T : numDomainType) :=
  abs_class_mixin.Build T fodder4 Num.norm.
HB.instance Definition _ (T : numDomainType) :=
  sgn_class_mixin.Build T fodder4 Num.Def.sgr.

Instance zero_class_pred_of_type (A : Algebra.ChoiceBaseAddUMagma.type) : zero_class_pred A := fodder.
Instance one_class_pred_of_type (A : one_class_type) : one_class_pred A := fodder.
Instance plus_class_pred_of_type (A : plus_class_type) : plus_class_pred A := fodder.
Instance minus_class_pred_of_type (A : zmodType) : minus_class_pred A := fodder.
Instance uminus_class_pred_of_type (A : zmodType) : uminus_class_pred A := fodder.
Instance times_class_pred_of_type (A : times_class_type) : times_class_pred A := fodder.
Instance semigroup_add_class_pred_of_type (A : semigroup_add_class_type) : plus_class_pred A := fodder.
Instance ab_semigroup_add_class_pred_of_type (A : nmodType) : plus_class_pred A := fodder.
Instance semigroup_mult_class_pred_of_type (A : semigroup_mult_class_type) : times_class_pred A := fodder.
Instance ab_semigroup_mult_class_pred_of_type (A : ab_semigroup_mult_class_type) : times_class_pred A := fodder.
Instance monoid_add_class_pred_of_type (A : nmodType) : monoid_add_class_pred A := fodder.
Instance comm_monoid_add_class_pred_of_type (A : nmodType) : monoid_add_class_pred A := fodder.
Instance monoid_mult_class_pred_of_type (A : monoid_mult_class_type) : monoid_mult_class_pred A := fodder.
Instance comm_monoid_mult_class_pred_of_type (A : comm_monoid_mult_class_type) : monoid_mult_class_pred A := fodder.
Instance cancel_semigroup_add_class_pred_of_type (A : nmodType) : plus_class_pred A := fodder.
Instance cancel_ab_semigroup_add_class_pred_of_type (A : zmodType) : cancel_ab_semigroup_add_class_pred A := fodder.
Instance cancel_comm_monoid_add_class_pred_of_type (A : zmodType) : cancel_comm_monoid_add_class_pred A := fodder.
Instance comm_monoid_diff_class_pred_of_type (A : comm_monoid_diff_class_type) : cancel_comm_monoid_add_class_pred A := fodder3.
Instance group_add_class_pred_of_type (A : zmodType) : group_add_class_pred A := fodder.
Instance ab_group_add_class_pred_of_type (A : zmodType) : group_add_class_pred A := fodder.
Instance ordered_ab_semigroup_add_class_pred_of_type (A : porderedNmodType) : ordered_ab_semigroup_add_class_pred A := fodder4.
Instance strict_ordered_ab_semigroup_add_class_pred_of_type (A : porderedZmodType) : ordered_ab_semigroup_add_class_pred A := fodder4.
Instance ordered_cancel_ab_semigroup_add_class_pred_of_type (A : porderedZmodType) : ordered_cancel_ab_semigroup_add_class_pred A := fodder4.
Instance ordered_ab_semigroup_add_imp_le_class_pred_of_type (A : porderedZmodType) : ordered_cancel_ab_semigroup_add_class_pred A := fodder4.
Instance ordered_comm_monoid_add_class_pred_of_type (A : porderedNmodType) : ordered_comm_monoid_add_class_pred A := fodder4.
Instance strict_ordered_comm_monoid_add_class_pred_of_type (A : porderedZmodType) : ordered_comm_monoid_add_class_pred A := fodder4.
Instance ordered_cancel_comm_monoid_add_class_pred_of_type (A : porderedZmodType) : ordered_cancel_comm_monoid_add_class_pred A := fodder4.
Instance ordered_ab_semigroup_monoid_add_imp_le_class_pred_of_type (A : porderedZmodType) : ordered_cancel_comm_monoid_add_class_pred A := fodder4.
Instance ordered_ab_group_add_class_pred_of_type (A : porderedZmodType) : ordered_ab_group_add_class_pred A := fodder4.
Instance linordered_ab_semigroup_add_class_pred_of_type (A : orderedNmodType) : ordered_ab_semigroup_add_class_pred A := fodder4.
Instance linordered_cancel_ab_semigroup_add_class_pred_of_type (A : orderedZmodType) : ordered_cancel_ab_semigroup_add_class_pred A := fodder4.
Instance linordered_ab_group_add_class_pred_of_type (A : orderedZmodType) : ordered_ab_group_add_class_pred A := fodder4.
Instance abs_class_pred_of_type (A : numDomainType) : abs_class_pred A := fodder4.
Instance sgn_class_pred_of_type (A : numDomainType) : sgn_class_pred A := fodder4.
Instance ordered_ab_group_add_abs_class_pred_of_type (A : realDomainType) : ordered_ab_group_add_abs_class_pred A := fodder4.
Instance canonically_ordered_monoid_add_class_pred_of_type (A : canonically_ordered_monoid_add_class_type) : ordered_comm_monoid_add_class_pred A := fodder4.
Instance ordered_cancel_comm_monoid_diff_class_pred_of_type (A : comm_monoid_diff_class_type) : ordered_cancel_comm_monoid_add_class_pred A := fodder3.

(*** Class definitions ***)
Unset Implicit Arguments.
Definition zero_class (A : Type') {_ : zero_class_pred A} : Prop := True.
Lemma zero_class_def (A : Type') {_ : zero_class_pred A} : @eq Prop (zero_class A) (type_class A).
Proof. exact (@Logic.eq_refl Prop (zero_class A)). Qed.
Definition one_class (A : Type') {_ : one_class_pred A} : Prop := True.
Lemma one_class_def (A : Type') {_ : one_class_pred A} : @eq Prop (one_class A) (type_class A).
Proof. exact (@Logic.eq_refl Prop (one_class A)). Qed.
Definition plus_class (A : Type') {_ : plus_class_pred A} : Prop := True.
Lemma plus_class_def (A : Type') {_ : plus_class_pred A} : @eq Prop (plus_class A) (type_class A).
Proof. exact (@Logic.eq_refl Prop (plus_class A)). Qed.
Definition minus_class (A : Type') {_ : minus_class_pred A} : Prop := True.
Lemma minus_class_def (A : Type') {_ : minus_class_pred A} : @eq Prop (minus_class A) (type_class A).
Proof. exact (@Logic.eq_refl Prop (minus_class A)). Qed.
Definition uminus_class (A : Type') {_ : uminus_class_pred A} : Prop := True.
Lemma uminus_class_def (A : Type') {_ : uminus_class_pred A} : @eq Prop (uminus_class A) (type_class A).
Proof. exact (@Logic.eq_refl Prop (uminus_class A)). Qed.
Definition times_class (A : Type') {_ : times_class_pred A} : Prop := True.
Lemma times_class_def (A : Type') {_ : times_class_pred A} : @eq Prop (times_class A) (type_class A).
Proof. exact (@Logic.eq_refl Prop (times_class A)). Qed.

Lemma zero_class_type_def (A : Algebra.ChoiceBaseAddUMagma.type) : zero_class A.
Proof. by []. Qed.
Lemma one_class_type_def (A : one_class_type) : one_class A.
Proof. by []. Qed.
Lemma plus_class_type_def (A : plus_class_type) : plus_class A.
Proof. by []. Qed.
Lemma minus_class_type_def (A : zmodType) : minus_class A.
Proof. by []. Qed.
Lemma uminus_class_type_def (A : zmodType) : uminus_class A.
Proof. by []. Qed.
Lemma times_class_type_def (A : times_class_type) : times_class A.
Proof. by []. Qed.

Lemma class_semigroup_add_def (A : Type') (plus : A -> A -> A) : @eq Prop (@associative A plus) (forall a : A, forall b : A, forall c : A, @eq A (plus (plus a b) c) (plus a (plus b c))).
Proof. by ext=> + > => ->. Qed.
Definition semigroup_add_class (A : Type') {_ : plus_class_pred A} : Prop :=
  associative plus.
Lemma semigroup_add_class_type_def : forall (A : semigroup_add_class_type), semigroup_add_class A.
Proof. exact: addrA. Qed.
Lemma semigroup_add_class_def (A : Type') {_ : plus_class_pred A} : @eq Prop (semigroup_add_class A) (and (plus_class A) (Trueprop (@associative A (@plus A _)))).
Proof. by ext=> [|[]]. Qed.

Lemma class_ab_semigroup_add_axioms_def (A : Type') (plus : A -> A -> A) : @eq Prop (@commutative _ A plus) (forall a : A, forall b : A, @eq A (plus a b) (plus b a)).
Proof. exact (@Logic.eq_refl Prop (@commutative _ A plus)). Qed.
Definition ab_semigroup_add_class (A : Type') {_ : plus_class_pred A} : Prop :=
  associative plus /\ commutative plus.
Lemma ab_semigroup_add_class_type_def (A : nmodType) : ab_semigroup_add_class A.
Proof. split ; [exact: addrA | exact: addrC]. Qed.
Lemma ab_semigroup_add_class_def (A : Type') {_ : plus_class_pred A} : @eq Prop (ab_semigroup_add_class A) (and (semigroup_add_class A) (Trueprop (@commutative _ A (@plus A _)))).
Proof. exact (@Logic.eq_refl Prop (ab_semigroup_add_class A)). Qed.

Lemma class_semigroup_mult_def (A : Type') (times : A -> A -> A) : @eq Prop (@associative A times) (forall a : A, forall b : A, forall c : A, @eq A (times (times a b) c) (times a (times b c))).
Proof. exact: class_semigroup_add_def. Qed.
Definition semigroup_mult_class (A : Type') {_ : times_class_pred A} : Prop :=
  associative times.
Lemma semigroup_mult_class_type_def (A : semigroup_mult_class_type) : semigroup_mult_class A.
Proof. exact : mulgA. Qed.
Lemma semigroup_mult_class_def (A : Type') {_ : times_class_pred A} : @eq Prop (semigroup_mult_class A) (and (times_class A) (Trueprop (@associative A (@times A _)))).
Proof. by ext=> [|[]]. Qed.

Lemma class_ab_semigroup_mult_axioms_def (A : Type') (times : A -> A -> A) : @eq Prop (@commutative _ A times) (forall a : A, forall b : A, @eq A (times a b) (times b a)).
Proof. exact (@Logic.eq_refl Prop (@commutative _ A times)). Qed.
Definition ab_semigroup_mult_class (A : Type') {_ : times_class_pred A} : Prop :=
  associative times /\ commutative times.
Lemma ab_semigroup_mult_class_type_def (A : ab_semigroup_mult_class_type) : ab_semigroup_mult_class A.
Proof. split ; [exact: mulgA | exact: mulgC]. Qed.
Lemma ab_semigroup_mult_class_def (A : Type') {_ : times_class_pred A} : @eq Prop (ab_semigroup_mult_class A) (and (semigroup_mult_class A) (Trueprop (@commutative _ A (@times A _)))).
Proof. exact (@Logic.eq_refl Prop (ab_semigroup_mult_class A)). Qed.

Definition class_monoid_add_axioms {A : Type'} (op : A -> A -> A) (id : A) : Prop :=
  left_id id op /\ right_id id op.
Lemma class_monoid_add_axioms_def (A : Type') (plus : A -> A -> A) (zero : A) : @eq Prop (@class_monoid_add_axioms A plus zero) (and (forall a : A, @eq A (plus zero a) a) (forall a : A, @eq A (plus a zero) a)).
Proof. exact (@Logic.eq_refl Prop (@class_monoid_add_axioms A plus zero)). Qed.
Definition monoid_add_class (A : Type') {_ : monoid_add_class_pred A} : Prop :=
  @associative A plus /\ @left_id A A zero_class_zero plus /\
  @right_id A A zero_class_zero plus.
Lemma monoid_add_class_type_def (A : nmodType) : monoid_add_class A.
Proof.
  do! split ; [exact: addrA | exact: add0r | exact: addr0].
Qed.
Lemma monoid_add_class_def (A : Type') {_ : monoid_add_class_pred A} : @eq Prop (monoid_add_class A) (and (semigroup_add_class A) (and (zero_class A) (Trueprop (@class_monoid_add_axioms A (@plus A _) (@zero_class_zero A _))))).
Proof. by ext ; do! (case=> ?). Qed.

Definition class_comm_monoid_add_axioms {A : Type'} (op : A -> A -> A) (id : A) : Prop :=
  left_id id op.
Lemma class_comm_monoid_add_axioms_def (A : Type') (plus : A -> A -> A) (zero : A) : @eq Prop (@class_comm_monoid_add_axioms A plus zero) (forall a : A, @eq A (plus zero a) a).
Proof. exact (@Logic.eq_refl Prop (@class_comm_monoid_add_axioms A plus zero)). Qed.
Definition comm_monoid_add_class (A : Type') {_ : monoid_add_class_pred A} : Prop :=
  @associative A plus /\ @commutative A A plus /\
  @left_id A A zero_class_zero plus.
Lemma comm_monoid_add_class_type_def (A : nmodType) : comm_monoid_add_class A.
Proof.
  do! split ; [exact: addrA | exact: addrC | exact: add0r].
Qed.
Lemma comm_monoid_add_class_def (A : Type') {_ : monoid_add_class_pred A} : @eq Prop (comm_monoid_add_class A) (and (ab_semigroup_add_class A) (and (zero_class A) (Trueprop (@class_comm_monoid_add_axioms A (@plus A _) (@zero_class_zero A _))))).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition class_monoid_mult_axioms {A : Type'} (id : A) (op : A -> A -> A) : Prop :=
  left_id id op /\ right_id id op.
Lemma class_monoid_mult_axioms_def (A : Type') (one : A) (times : A -> A -> A) : @eq Prop (@class_monoid_mult_axioms A one times) (and (forall a : A, @eq A (times one a) a) (forall a : A, @eq A (times a one) a)).
Proof. exact (@Logic.eq_refl Prop (@class_monoid_mult_axioms A one times)). Qed.
Definition monoid_mult_class (A : Type') {_ : monoid_mult_class_pred A} : Prop :=
  @associative A times /\ @left_id A A one_class_one times /\
  @right_id A A one_class_one times.
Lemma monoid_mult_class_type_def (A : monoid_mult_class_type) : monoid_mult_class A.
Proof. do! split ; [exact: mulgA | exact: mul1g | exact: mulg1]. Qed.
Lemma monoid_mult_class_def (A : Type') {_ : monoid_mult_class_pred A} : @eq Prop (monoid_mult_class A) (and (one_class A) (and (semigroup_mult_class A) (Trueprop (@class_monoid_mult_axioms A (@one_class_one A _) (@times A _))))).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition class_comm_monoid_mult_axioms {A : Type'} (op : A -> A -> A) (id : A) :=
  left_id id op.
Lemma class_comm_monoid_mult_axioms_def (A : Type') (times : A -> A -> A) (one : A) : @eq Prop (@class_comm_monoid_mult_axioms A times one) (forall a : A, @eq A (times one a) a).
Proof. exact (@Logic.eq_refl Prop (@class_comm_monoid_mult_axioms A times one)). Qed.
Definition comm_monoid_mult_class (A : Type') {_ : monoid_mult_class_pred A} : Prop :=
  @associative A times /\ @commutative A A times /\
  @left_id A A one_class_one times.
Lemma comm_monoid_mult_class_type_def (A : comm_monoid_mult_class_type) : comm_monoid_mult_class A.
Proof. do! split ; [exact: mulgA | exact: mulgC | exact: mul1g]. Qed.
Lemma comm_monoid_mult_class_def (A : Type') {_ : monoid_mult_class_pred A} : @eq Prop (comm_monoid_mult_class A) (and (ab_semigroup_mult_class A) (and (one_class A) (Trueprop (@class_comm_monoid_mult_axioms A (@times A _) (@one_class_one A _))))).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition class_cancel_semigroup_add_axioms {A : Type'} (op : A -> A -> A) : Prop :=
  left_injective op /\ right_injective op.

Lemma class_cancel_semigroup_add_axioms_def (A : Type') (plus : A -> A -> A) : @eq Prop (@class_cancel_semigroup_add_axioms A plus) (and (forall a : A, forall b : A, forall c : A, (@eq A (plus a b) (plus a c)) -> @eq A b c) (forall b : A, forall a : A, forall c : A, (@eq A (plus b a) (plus c a)) -> @eq A b c)).
Proof. ext ; firstorder. Qed.
Definition cancel_semigroup_add_class (A : Type') {_ : plus_class_pred A} : Prop :=
  associative plus /\ left_injective plus /\ right_injective plus.
Lemma cancel_semigroup_add_class_type_def (A : zmodType) : cancel_semigroup_add_class A.
Proof. do! split ; [exact: addrA | exact: addIr | exact: addrI]. Qed.
Lemma cancel_semigroup_add_class_def (A : Type') {_ : plus_class_pred A} : @eq Prop (cancel_semigroup_add_class A) (and (semigroup_add_class A) (Trueprop (@class_cancel_semigroup_add_axioms A (@plus A _)))).
Proof. exact (@Logic.eq_refl Prop (cancel_semigroup_add_class A)). Qed.

Definition class_cancel_ab_semigroup_add_axioms {A : Type'} : (A -> A -> A) -> (A -> A -> A) -> Prop := fun plus minus : A -> A -> A => and (forall a : A, forall b : A, @eq A (minus (plus a b) a) b) (forall a : A, forall b : A, forall c : A, @eq A (minus (minus a b) c) (minus a (plus b c))).
Lemma class_cancel_ab_semigroup_add_axioms_def (A : Type') (plus minus : A -> A -> A) : @eq Prop (@class_cancel_ab_semigroup_add_axioms A plus minus) (and (forall a : A, forall b : A, @eq A (minus (plus a b) a) b) (forall a : A, forall b : A, forall c : A, @eq A (minus (minus a b) c) (minus a (plus b c)))).
Proof. exact (@Logic.eq_refl Prop (@class_cancel_ab_semigroup_add_axioms A plus minus)). Qed.
Definition cancel_ab_semigroup_add_class (A : Type') {_ : cancel_ab_semigroup_add_class_pred A} : Prop :=
  @associative A plus /\ @commutative A A plus /\
  @class_cancel_ab_semigroup_add_axioms A plus minus.
Lemma cancel_ab_semigroup_add_class_type_def (A : zmodType) : cancel_ab_semigroup_add_class A.
Proof.
  do! split ; [exact: addrA | exact: addrC | |].
  - by move=> x y ; rewrite [LHS]addrC addrA (addrC (- x)) subrr add0r.
  - by move=> x y z ; rewrite -{2}(subrK y x) [RHS]addrKA.
Qed.
Lemma cancel_ab_semigroup_add_class_def (A : Type') {_ : cancel_ab_semigroup_add_class_pred A} : @eq Prop (cancel_ab_semigroup_add_class A) (and (ab_semigroup_add_class A) (and (minus_class A) (Trueprop (@class_cancel_ab_semigroup_add_axioms A (@plus A _) (@minus A _))))).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition cancel_comm_monoid_add_class (A : Type') {_ : cancel_comm_monoid_add_class_pred A} : Prop :=
  @associative A plus /\ @commutative A A plus /\
  @left_id A A zero_class_zero plus /\
  @class_cancel_ab_semigroup_add_axioms A plus minus.
Lemma cancel_comm_monoid_add_class_type_def (A : zmodType) : cancel_comm_monoid_add_class A.
Proof.
 case: (cancel_ab_semigroup_add_class_type_def A)=> [?[]] ; do! split => //.
 exact: add0r.
Qed.
Lemma cancel_comm_monoid_add_class_def (A : Type') {_ : cancel_comm_monoid_add_class_pred A} : @eq Prop (cancel_comm_monoid_add_class A) (and (cancel_ab_semigroup_add_class A) (comm_monoid_add_class A)).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition class_comm_monoid_diff_axioms {A : Type'} (sub : A -> A -> A) (_0 : A) : Prop :=
  left_zero _0 sub.
Lemma class_comm_monoid_diff_axioms_def (A : Type') (minus : A -> A -> A) (zero : A) : @eq Prop (@class_comm_monoid_diff_axioms A minus zero) (forall a : A, @eq A (minus zero a) zero).
Proof. exact (@Logic.eq_refl Prop (@class_comm_monoid_diff_axioms A minus zero)). Qed.
Definition comm_monoid_diff_class (A : Type') {_ : cancel_comm_monoid_add_class_pred A} : Prop := 
  @associative A plus /\ @commutative A A plus /\
  @left_id A A zero_class_zero plus /\
  @left_zero A A zero_class_zero minus /\
  @class_cancel_ab_semigroup_add_axioms A plus minus.
Lemma comm_monoid_diff_class_type_def (A : comm_monoid_diff_class_type) : comm_monoid_diff_class A.
Proof.
  by case: (cancel_comm_monoid_add_class_type_def A)=> [?[?[]]].
Qed.
Lemma comm_monoid_diff_class_def (A : Type') {_ : cancel_comm_monoid_add_class_pred A} : @eq Prop (comm_monoid_diff_class A) (and (cancel_comm_monoid_add_class A) (Trueprop (@class_comm_monoid_diff_axioms A (@minus A _) (@zero_class_zero A _)))).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition is_subtraction {A} (add : A -> A -> A) (opp : A -> A)
  (sub : A -> A -> A) := sub = fun x y => (add x (opp y)).

Lemma subtractP {T : zmodType} : @is_subtraction T +%R -%R subtract.
Proof. by []. Qed.

Definition class_group_add_axioms {A : Type'} (sub add : A -> A -> A) (_0 : A) (opp : A -> A) : Prop :=
  left_inverse _0 opp add /\ is_subtraction add opp sub.
Lemma class_group_add_axioms_def (A : Type') (minus plus : A -> A -> A) (zero : A) (uminus : A -> A) : @eq Prop (@class_group_add_axioms A minus plus zero uminus) (and (forall a : A, @eq A (plus (uminus a) a) zero) (forall a : A, forall b : A, @eq A (plus a (uminus b)) (minus a b))).
Proof. by ext => -[li] => /[funext] ; split. Qed.
Definition group_add_class (A : Type') {_ : group_add_class_pred A} : Prop :=
  @associative A plus /\ @left_id A A zero_class_zero plus /\
  @right_id A A zero_class_zero plus /\
  @left_inverse A A A zero_class_zero uminus plus /\
  @is_subtraction A plus uminus minus.
Lemma group_add_class_type_def (A : zmodType) : group_add_class A.
Proof.
  do! split ; [exact: addrA | exact:add0r | exact: addr0 | exact: addNr].
Qed.
Lemma group_add_class_def (A : Type') {_ : group_add_class_pred A} : @eq Prop (group_add_class A) (and (and (minus_class A) (monoid_add_class A)) (and (uminus_class A) (Trueprop (@class_group_add_axioms A (@minus A _) (@plus A _) (@zero_class_zero A _) (@uminus A _))))).
Proof. by ext ; firstorder trivial. Qed.

Definition class_ab_group_add_axioms {A : Type'} add _0 sub opp :=
  @class_group_add_axioms A sub add _0 opp.
Lemma class_ab_group_add_axioms_def (A : Type') (plus : A -> A -> A) (zero : A) (minus : A -> A -> A) (uminus : A -> A) : @eq Prop (@class_ab_group_add_axioms A plus zero minus uminus) (and (forall a : A, @eq A (plus (uminus a) a) zero) (forall a : A, forall b : A, @eq A (minus a b) (plus a (uminus b)))).
Proof. by ext => -[li] => /[funext] ; split. Qed.
Definition ab_group_add_class (A : Type') {_ : group_add_class_pred A} : Prop :=
  @associative A plus /\ @commutative A A plus /\
  @left_id A A zero_class_zero plus /\
  @left_inverse A A A zero_class_zero uminus plus /\
  @is_subtraction A plus uminus minus.
Lemma ab_group_add_class_type_def (A : zmodType) : ab_group_add_class A.
Proof.
  do! split ; [exact: addrA | exact: addrC | exact:add0r | exact: addNr].
Qed.
Lemma ab_group_add_class_def (A : Type') {_ : group_add_class_pred A} : @eq Prop (ab_group_add_class A) (and (and (comm_monoid_add_class A) (minus_class A)) (and (uminus_class A) (Trueprop (@class_ab_group_add_axioms A (@plus A _) (@zero_class_zero A _) (@minus A _) (@uminus A _))))).
Proof. by ext ; firstorder. Qed.

Definition class_ordered_ab_semigroup_add_axioms {A : Type'} (add : A -> A -> A) (le : A -> A -> Prop) : Prop :=
  forall x : A, {homo add x : y z / le y z}.
Lemma class_ordered_ab_semigroup_add_axioms_def (A : Type') (plus : A -> A -> A) (less_eq : A -> A -> Prop) : @eq Prop (@class_ordered_ab_semigroup_add_axioms A plus less_eq) (forall a : A, forall b : A, forall c : A, (less_eq a b) -> less_eq (plus c a) (plus c b)).
Proof. ext=>H ???? ; exact: H. Qed.
Definition ordered_ab_semigroup_add_class (A : Type') {_ : ordered_ab_semigroup_add_class_pred A} : Prop :=
  ab_semigroup_add_class A /\ @Porder A less_eq less /\
  forall x : A, {homo plus x : y z / less_eq y z}.
Lemma ordered_ab_semigroup_add_class_type_def (A : porderedNmodType) : ordered_ab_semigroup_add_class A.
Proof.
  split ; first exact: ab_semigroup_add_class_type_def.
  split ; [exact: order_class_type_def | exact: Num.ler_wD2l].
Qed.
Lemma ordered_ab_semigroup_add_class_def (A : Type') {_ : ordered_ab_semigroup_add_class_pred A} : @eq Prop (ordered_ab_semigroup_add_class A) (and (ab_semigroup_add_class A) (and (order_class A) (Trueprop (@class_ordered_ab_semigroup_add_axioms A (@plus A _) (@less_eq A _))))).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition class_strict_ordered_ab_semigroup_add_axioms {A : Type'} (add : A -> A -> A) (lt : A -> A -> Prop) : Prop :=
  forall x x' y y', lt x x' -> lt y y' -> lt (add x y) (add x' y').
Lemma class_strict_ordered_ab_semigroup_add_axioms_def (A : Type') (plus : A -> A -> A) (less : A -> A -> Prop) : @eq Prop (@class_strict_ordered_ab_semigroup_add_axioms A plus less) (forall a : A, forall b : A, forall c : A, forall d : A, (less a b) -> (less c d) -> less (plus a c) (plus b d)).
Proof. exact (@Logic.eq_refl Prop (@class_strict_ordered_ab_semigroup_add_axioms A plus less)). Qed.
Definition strict_ordered_ab_semigroup_add_class (A : Type') {_ : ordered_ab_semigroup_add_class_pred A} : Prop :=
  ab_semigroup_add_class A /\ @Porder A less_eq less /\
  (forall x : A, {homo plus x : y z / less_eq y z}) /\
  forall x x' y y' : A, less x x' -> less y y' -> less (plus x y) (plus x' y').
Lemma strict_ordered_ab_semigroup_add_class_type_def (A : porderedZmodType) : strict_ordered_ab_semigroup_add_class A.
Proof.
  case:(ordered_ab_semigroup_add_class_type_def A) => ? [? ?].
  do 3! split => // ; exact: ltrD.
Qed.
Lemma strict_ordered_ab_semigroup_add_class_def (A : Type') {_ : ordered_ab_semigroup_add_class_pred A} : @eq Prop (strict_ordered_ab_semigroup_add_class A) (and (ordered_ab_semigroup_add_class A) (Trueprop (@class_strict_ordered_ab_semigroup_add_axioms A (@plus A _) (@less A _)))).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition ordered_cancel_ab_semigroup_add_class (A : Type') {_ : ordered_cancel_ab_semigroup_add_class_pred A} : Prop :=
  cancel_ab_semigroup_add_class A /\ @Porder A less_eq less /\
  forall x : A, {homo plus x : y z / less_eq y z}.
Lemma ordered_cancel_ab_semigroup_add_class_type_def (A : porderedZmodType) : ordered_cancel_ab_semigroup_add_class A.
Proof.
  split ; first exact: cancel_ab_semigroup_add_class_type_def.
  by case:(ordered_ab_semigroup_add_class_type_def A).
Qed.
Lemma ordered_cancel_ab_semigroup_add_class_def (A : Type') {_ : ordered_cancel_ab_semigroup_add_class_pred A} : @eq Prop (ordered_cancel_ab_semigroup_add_class A) (and (cancel_ab_semigroup_add_class A) (ordered_ab_semigroup_add_class A)).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition class_ordered_ab_semigroup_add_imp_le_axioms {A : Type'} (add : A -> A -> A) (le : A -> A -> Prop) : Prop :=
  forall x y z, le (add x y) (add x z) -> le y z.
Lemma class_ordered_ab_semigroup_add_imp_le_axioms_def (A : Type') (plus : A -> A -> A) (less_eq : A -> A -> Prop) : @eq Prop (@class_ordered_ab_semigroup_add_imp_le_axioms A plus less_eq) (forall c : A, forall a : A, forall b : A, (less_eq (plus c a) (plus c b)) -> less_eq a b).
Proof. by []. Qed.
Definition ordered_ab_semigroup_add_imp_le_class (A : Type') {_ : ordered_cancel_ab_semigroup_add_class_pred A} : Prop :=
  cancel_ab_semigroup_add_class A /\ @Porder A less_eq less /\
  forall x : A, {mono plus x : y z / less_eq y z}.
Lemma ordered_ab_semigroup_add_imp_le_class_type_def (A : porderedZmodType) : ordered_ab_semigroup_add_imp_le_class A.
Proof.
  case: (ordered_cancel_ab_semigroup_add_class_type_def A) => [? [? _]].
  (do 2! split=> //)=> ? ? ? ; congr is_true ; exact: lerD2l.
Qed.
Lemma ordered_ab_semigroup_add_imp_le_class_def (A : Type') {_ : ordered_cancel_ab_semigroup_add_class_pred A} : @eq Prop (ordered_ab_semigroup_add_imp_le_class A) (and (ordered_cancel_ab_semigroup_add_class A) (Trueprop (@class_ordered_ab_semigroup_add_imp_le_axioms A (@plus A _) (@less_eq A _)))).
Proof.
  ext=> [[? [? pleM]]|[[? [? pleH]] plerH]] ; do! split => //.
  1,2 : by move=> ? ? ? ; rewrite pleM.
  move=> ? ? ? /` ; [exact: plerH | exact: pleH].
Qed.

Definition ordered_comm_monoid_add_class (A : Type') {_ : ordered_comm_monoid_add_class_pred A} : Prop :=
  comm_monoid_add_class A /\ @Porder A less_eq less /\
  forall x : A, {homo plus x : y z / less_eq y z}.
Lemma ordered_comm_monoid_add_class_type_def (A : porderedNmodType) : ordered_comm_monoid_add_class A.
Proof.
  case: (ordered_ab_semigroup_add_class_type_def A) => _ ; split => //.
  exact: comm_monoid_add_class_type_def.
Qed.
Lemma ordered_comm_monoid_add_class_def (A : Type') {_ : ordered_comm_monoid_add_class_pred A} : @eq Prop (ordered_comm_monoid_add_class A) (and (comm_monoid_add_class A) (ordered_ab_semigroup_add_class A)).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition strict_ordered_comm_monoid_add_class (A : Type') {_ : ordered_comm_monoid_add_class_pred A} : Prop :=
  comm_monoid_add_class A /\ @Porder A less_eq less /\
  (forall x : A, {homo plus x : y z / less_eq y z}) /\
  forall x x' y y' : A, less x x' -> less y y' -> less (plus x y) (plus x' y').
Lemma strict_ordered_comm_monoid_add_class_type_def (A : porderedZmodType) : strict_ordered_comm_monoid_add_class A.
Proof.
  case: (strict_ordered_ab_semigroup_add_class_type_def A) => _ ; split => //.
  exact: comm_monoid_add_class_type_def.
Qed.
Lemma strict_ordered_comm_monoid_add_class_def (A : Type') {_ : ordered_comm_monoid_add_class_pred A} : @eq Prop (strict_ordered_comm_monoid_add_class A) (and (comm_monoid_add_class A) (strict_ordered_ab_semigroup_add_class A)).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition ordered_cancel_comm_monoid_add_class (A : Type') {_ : ordered_cancel_comm_monoid_add_class_pred A} : Prop :=
  cancel_comm_monoid_add_class A /\ @Porder A less_eq less /\
  forall x : A, {homo plus x : y z / less_eq y z}.
Lemma ordered_cancel_comm_monoid_add_class_type_def (A : porderedZmodType) : ordered_cancel_comm_monoid_add_class A.
Proof.
  case: (ordered_ab_semigroup_add_class_type_def A) => _ ; split => //.
  exact: cancel_comm_monoid_add_class_type_def.
Qed.
Lemma ordered_cancel_comm_monoid_add_class_def (A : Type') {_ : ordered_cancel_comm_monoid_add_class_pred A} : @eq Prop (ordered_cancel_comm_monoid_add_class A) (and (cancel_ab_semigroup_add_class A) (ordered_comm_monoid_add_class A)).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition ordered_ab_semigroup_monoid_add_imp_le_class (A : Type') {_ : ordered_cancel_comm_monoid_add_class_pred A} : Prop :=
  cancel_comm_monoid_add_class A /\ @Porder A less_eq less /\
  forall x : A, {mono plus x : y z / less_eq y z}.
Lemma ordered_ab_semigroup_monoid_add_imp_le_class_type_def (A : porderedZmodType) : ordered_ab_semigroup_monoid_add_imp_le_class A.
Proof.
  case: (ordered_ab_semigroup_add_imp_le_class_type_def A) => _ ; split => //.
  exact: cancel_comm_monoid_add_class_type_def.
Qed.
Lemma ordered_ab_semigroup_monoid_add_imp_le_class_def (A : Type') {_ : ordered_cancel_comm_monoid_add_class_pred A} : @eq Prop (ordered_ab_semigroup_monoid_add_imp_le_class A) (and (monoid_add_class A) (ordered_ab_semigroup_add_imp_le_class A)).
Proof.
  ext=> [[[? [pC [? ?]]] [? ?]]|].
  - by (do! split => //) => ? ; rewrite pC.
  - by do! ((do? case) => ?).
Qed.

Definition ordered_ab_group_add_class (A : Type') {_ : ordered_ab_group_add_class_pred A} : Prop :=
  ab_group_add_class A /\ @Porder A less_eq less /\
  forall x : A, {homo plus x : y z / less_eq y z}.
Lemma ordered_ab_group_add_class_type_def (A : porderedZmodType) : ordered_ab_group_add_class A.
Proof. 
  case: (ordered_ab_semigroup_add_class_type_def A) => _ ; split => //.
  exact: ab_group_add_class_type_def.
Qed.
Lemma ordered_ab_group_add_class_def (A : Type') {_ : ordered_ab_group_add_class_pred A} : @eq Prop (ordered_ab_group_add_class A) (and (ab_group_add_class A) (ordered_ab_semigroup_add_class A)).
Proof. by ext ; firstorder trivial. Qed.

Definition linordered_ab_semigroup_add_class (A : Type') {_ : ordered_ab_semigroup_add_class_pred A} : Prop :=
  ab_semigroup_add_class A /\ @Ptotal_order A less_eq less /\
  forall x : A, {homo plus x : y z / less_eq y z}.
Lemma linordered_ab_semigroup_add_class_type_def (A : orderedNmodType) : linordered_ab_semigroup_add_class A.
Proof.
  case : (ordered_ab_semigroup_add_class_type_def A) => _ []; split.
  - exact: ab_semigroup_add_class_type_def.
  - (do 2! split=> //) ; exact/totalP/le_total.
Qed.
Lemma linordered_ab_semigroup_add_class_def (A : Type') {_ : ordered_ab_semigroup_add_class_pred A} : @eq Prop (linordered_ab_semigroup_add_class A) (and (ordered_ab_semigroup_add_class A) (linorder_class A)).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition linordered_cancel_ab_semigroup_add_class (A : Type') {_ : ordered_cancel_ab_semigroup_add_class_pred A} : Prop :=
  cancel_ab_semigroup_add_class A /\ @Ptotal_order A less_eq less /\
  forall x : A, {homo plus x : y z / less_eq y z}.
Lemma linordered_cancel_ab_semigroup_add_class_type_def (A : orderedZmodType) : linordered_cancel_ab_semigroup_add_class A.
Proof.
  case : (linordered_ab_semigroup_add_class_type_def A) => _ ; split=> //.
  exact: cancel_ab_semigroup_add_class_type_def.
Qed.
Lemma linordered_cancel_ab_semigroup_add_class_def (A : Type') {_ : ordered_cancel_ab_semigroup_add_class_pred A} : @eq Prop (linordered_cancel_ab_semigroup_add_class A) (and (ordered_cancel_ab_semigroup_add_class A) (linorder_class A)).
Proof. by ext ; do! ((do? case) => ?). Qed.

Definition linordered_ab_group_add_class (A : Type') {_ : ordered_ab_group_add_class_pred A} : Prop :=
  ab_group_add_class A /\ @Ptotal_order A less_eq less /\
  forall x : A, {homo plus x : y z / less_eq y z}.
Lemma linordered_ab_group_add_class_type_def (A : orderedZmodType) : linordered_ab_group_add_class A.
Proof.
  case : (linordered_ab_semigroup_add_class_type_def A) => _ ; split=> //.
  exact: ab_group_add_class_type_def.
Qed.
Lemma linordered_ab_group_add_class_def (A : Type') {_ : ordered_ab_group_add_class_pred A} : @eq Prop (linordered_ab_group_add_class A) (and (ordered_ab_group_add_class A) (linorder_class A)).
Proof. by ext ; firstorder trivial. Qed.

Definition abs_class (A : Type') {_ : abs_class_pred A} : Prop := True.
Lemma abs_class_type_def (A : numDomainType) : abs_class A.
Proof. by []. Qed.
Lemma abs_class_def (A : Type') {_ : abs_class_pred A} : @eq Prop (abs_class A) (type_class A).
Proof. exact (@Logic.eq_refl Prop (abs_class A)). Qed.

Definition sgn_class (A : Type') {_ : sgn_class_pred A} : Prop := True.
Lemma sgn_class_type_def (A : numDomainType) : sgn_class A.
Proof. by []. Qed.
Lemma sgn_class_def (A : Type') {_ : sgn_class_pred A} : @eq Prop (sgn_class A) (type_class A).
Proof. exact (@Logic.eq_refl Prop (sgn_class A)). Qed.

Definition class_ordered_ab_group_add_abs_axioms {A : Type'} : (A -> A) -> (A -> A -> A) -> A -> (A -> A) -> (A -> A -> Prop) -> Prop := fun (abs : A -> A) (plus : A -> A -> A) (zero : A) (uminus : A -> A) (less_eq : A -> A -> Prop) => and (and (forall a : A, less_eq zero (abs a)) (forall a : A, less_eq a (abs a))) (and (forall a : A, forall b : A, (less_eq a b) -> (less_eq (uminus a) b) -> less_eq (abs a) b) (and (forall a : A, @eq A (abs (uminus a)) (abs a)) (forall a : A, forall b : A, less_eq (abs (plus a b)) (plus (abs a) (abs b))))).
Lemma class_ordered_ab_group_add_abs_axioms_def (A : Type') (abs : A -> A) (plus : A -> A -> A) (zero : A) (uminus : A -> A) (less_eq : A -> A -> Prop) : @eq Prop (@class_ordered_ab_group_add_abs_axioms A abs plus zero uminus less_eq) (and (and (forall a : A, less_eq zero (abs a)) (forall a : A, less_eq a (abs a))) (and (forall a : A, forall b : A, (less_eq a b) -> (less_eq (uminus a) b) -> less_eq (abs a) b) (and (forall a : A, @eq A (abs (uminus a)) (abs a)) (forall a : A, forall b : A, less_eq (abs (plus a b)) (plus (abs a) (abs b)))))).
Proof. exact (@Logic.eq_refl Prop (@class_ordered_ab_group_add_abs_axioms A abs plus zero uminus less_eq)). Qed.
Definition ordered_ab_group_add_abs_class (A : Type') {_ : ordered_ab_group_add_abs_class_pred A} : Prop :=
  ordered_ab_group_add_class A /\ @class_ordered_ab_group_add_abs_axioms A abs plus zero_class_zero uminus less_eq.
Lemma ordered_ab_group_add_abs_class_type_def (A : realDomainType) : ordered_ab_group_add_abs_class A.
Proof.
  split ; [exact: ordered_ab_group_add_class_type_def | do! split].
  - exact: normr_ge0.
  - exact:ler_norm.
  - move=> ? ? ? ? ; cbn ; rewrite ler_norml lerNl ; exact/andP.
  - exact: normrN.
  - exact: ler_normD.
Qed.
Lemma ordered_ab_group_add_abs_class_def (A : Type') {_ : ordered_ab_group_add_abs_class_pred A} : @eq Prop (ordered_ab_group_add_abs_class A) (and (abs_class A) (and (ordered_ab_group_add_class A) (Trueprop (@class_ordered_ab_group_add_abs_axioms A (@abs A _) (@plus A _) (@zero_class_zero A _) (@uminus A _) (@less_eq A _))))).
Proof. by ext=> [|[ _]]. Qed.

Definition class_canonically_ordered_monoid_add_axioms {A : Type'} (add : A -> A -> A) (le : A -> A -> Prop) : Prop :=
  forall x y, le x y <-> exists z, y = add x z.
Lemma class_canonically_ordered_monoid_add_axioms_def (A : Type') (plus : A -> A -> A) (less_eq : A -> A -> Prop) : @eq Prop (@class_canonically_ordered_monoid_add_axioms A plus less_eq) (forall a : A, forall b : A, @eq Prop (less_eq a b) (exists c : A, @eq A b (plus a c))).
Proof. by ext=> + x y => /[spec x | y] => [[*] /` | ->]. Qed.
Definition canonically_ordered_monoid_add_class (A : Type') {_ : ordered_comm_monoid_add_class_pred A} : Prop :=
  comm_monoid_add_class A /\ @Porder A less_eq less /\
  @class_canonically_ordered_monoid_add_axioms A plus less_eq.
Lemma canonically_ordered_monoid_add_class_type_def (A : canonically_ordered_monoid_add_class_type) : canonically_ordered_monoid_add_class A.
Proof.
  case: (ordered_comm_monoid_add_class_type_def A) => [? [? _]].
  (do 2! split=> //) ; exact: le_diff_pos.
Qed.
Lemma canonically_ordered_monoid_add_class_def (A : Type') {_ : ordered_comm_monoid_add_class_pred A} : @eq Prop (canonically_ordered_monoid_add_class A) (and (comm_monoid_add_class A) (and (order_class A) (Trueprop (@class_canonically_ordered_monoid_add_axioms A (@plus A _) (@less_eq A _))))).
Proof. exact (@Logic.eq_refl Prop (canonically_ordered_monoid_add_class A)). Qed.

Definition ordered_cancel_comm_monoid_diff_class (A : Type') {_ : ordered_cancel_comm_monoid_add_class_pred A} : Prop :=
  comm_monoid_diff_class A /\ @Porder A less_eq less /\
  (forall x : A, {mono plus x : y z / less_eq y z}) /\
  @class_canonically_ordered_monoid_add_axioms A plus less_eq.
Lemma ordered_cancel_comm_monoid_diff_class_type_def (A : comm_monoid_diff_class_type) : ordered_cancel_comm_monoid_diff_class A.
Proof.
  split ; first exact: comm_monoid_diff_class_type_def.
  case: (ordered_ab_semigroup_add_imp_le_class_type_def A) => _ [].
  do 2! (split ; first assumption) ; exact: le_diff_pos.
Qed.

Lemma ordered_cancel_comm_monoid_diff_class_def (A : Type') {_ : ordered_cancel_comm_monoid_add_class_pred A} : @eq Prop (ordered_cancel_comm_monoid_diff_class A) (and (canonically_ordered_monoid_add_class A) (and (comm_monoid_diff_class A) (ordered_ab_semigroup_add_imp_le_class A))).
Proof. by ext ; do! ((do? case) => ?). Qed.

Lemma semigroup_def (A : Type') (f : A -> A -> A) : @eq Prop (@associative A f) (forall a : A, forall b : A, forall c : A, @eq A (f (f a b) c) (f a (f b c))).
Proof. by ext=> + ? ? ? => ->. Qed.

Lemma abel_semigroup_axioms_def (A : Type') (f : A -> A -> A) : @eq Prop (@commutative _ A f) (forall a : A, forall b : A, @eq A (f a b) (f b a)).
Proof. by []. Qed.

Definition abel_semigroup {A : Type'}  (f : A -> A -> A) : Prop :=
  associative f /\ commutative f.
Lemma abel_semigroup_def (A : Type') (f : A -> A -> A) : @eq Prop (@abel_semigroup A f) (and (@associative A f) (@commutative _ A f)).
Proof. by []. Qed.

Definition monoid_axioms {A : Type'} (f : A -> A -> A) (z : A) : Prop :=
  left_id z f /\ right_id z f.
Lemma monoid_axioms_def (A : Type') (f : A -> A -> A) (z : A) : @eq Prop (@monoid_axioms A f z) (and (forall a : A, @eq A (f z a) a) (forall a : A, @eq A (f a z) a)).
Proof. by []. Qed.

Definition monoid {A : Type'} (f : A -> A -> A) (z : A) : Prop :=
  associative f /\ left_id z f /\ right_id z f.
Lemma monoid_def (A : Type') (f : A -> A -> A) (z : A) : @eq Prop (@monoid A f z) (and (@associative A f) (@monoid_axioms A f z)).
Proof. by []. Qed.

Definition comm_monoid_axioms {A : Type'} (f : A -> A -> A) (z : A) : Prop :=
  right_id z f.
Lemma comm_monoid_axioms_def (A : Type') (f : A -> A -> A) (z : A) : @eq Prop (@comm_monoid_axioms A f z) (forall a : A, @eq A (f a z) a).
Proof. by []. Qed.

Definition comm_monoid {A : Type'} (f : A -> A -> A) (z : A) : Prop := 
  associative f /\ commutative f /\ right_id z f.
Lemma comm_monoid_def (A : Type') (f : A -> A -> A) (z : A) : @eq Prop (@comm_monoid A f z) (and (@abel_semigroup A f) (@comm_monoid_axioms A f z)).
Proof. exact:andA. Qed.

Definition group_axioms {A : Type'} (f : A -> A -> A) (z : A) (inverse : A -> A) : Prop :=
  left_id z f /\ left_inverse z inverse f.
Lemma group_axioms_def (A : Type') (f : A -> A -> A) (z : A) (inverse : A -> A) : @eq Prop (@group_axioms A f z inverse) (and (forall a : A, @eq A (f z a) a) (forall a : A, @eq A (f (inverse a) a) z)).
Proof. by []. Qed.

Definition group {A : Type'} (f : A -> A -> A) (z : A) (inverse : A -> A) : Prop :=
 associative f /\ left_id z f /\ left_inverse z inverse f.
Lemma group_def (A : Type') (f : A -> A -> A) (z : A) (inverse : A -> A) : @eq Prop (@group A f z inverse) (and (@associative A f) (@group_axioms A f z inverse)).
Proof. by []. Qed.