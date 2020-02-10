(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Relations.
Require Import Ensembles.
From ATBR Require Import ATBR Model_StdRelations.



Definition inter {A:Type} (r1 r2 : relation A) :=
  fun x => fun y => (r1 x y) /\
                    (r2 x y).

Module RelNotations.

Infix " <+> " := (union _) (at level 49, right associativity).
Infix " <*> " := inter (at level 50, left associativity).
Infix " ;; " := comp (at level 41, right associativity).
Infix " == " := (same_relation _) (at level 70).
Infix " ⊆ " := (inclusion _) (at level 75).
Notation "R ⁺" := (clos_trans _ R) (at level 20).
Notation "R ?" := (clos_refl _ R) (at level 15).
Notation "R **" := (clos_refl_trans _ R) (at level 25).
Notation "R ^-1" := (transp _ R) (at level 14).

End RelNotations.

Import RelNotations.

(** Axiom of extensionality for relations define as predicates

If two relations relate the same elements, they are equal *)

Axiom ext_rel : forall (A:Type) (r1 r2 : relation A),
  (r1 == r2) -> r1 = r2.

Definition dom {A:Type} (r:relation A) : Ensemble A :=
  fun x => exists y, r x y.

Definition ran {A:Type} (r:relation A) : Ensemble A :=
  fun y => exists x, r x y.

Definition udr {A:Type} (r: relation A) : Ensemble A :=
  Union _ (dom r) (ran r).

Definition partial_order {A:Type} (r:relation A) (xs:Ensemble A) : Prop :=
  Included _ (udr r) xs /\
  (*transitivity*)
  (forall x1 x2 x3, (r x1 x2) /\ (r x2 x3) -> (r x1 x3)) /\
  (*irreflexivity*)
  (forall x, ~(r x x)).

Definition linear_strict_order {A:Type} (r:relation A) (xs:Ensemble A) : Prop :=
  Included _(Union _ (dom r) (ran r)) xs /\
  (*transitivity*)
  (forall x1 x2 x3, (r x1 x2) /\ (r x2 x3) -> (r x1 x3)) /\
  (*irreflexivity*)
  (forall x, ~(r x x)) /\
  (*linear on xs*)
  (forall x1 x2, (x1 <> x2) -> (In _ xs x1) -> (In _ xs x2) ->
    (r x1 x2) \/ (r x2 x1)).

Module Type OrdExt.
Parameter Elt : Type.

(** LE (linear extension) extends a partial order to a total order *)

Parameter LE : relation Elt -> relation Elt.

(** A relation is included in its own linear extension and a linear extension
    is a strict linear order *)

Axiom OE : forall (s S:Ensemble Elt) (r:relation Elt),
  Included _ s S ->
  partial_order r s ->
  r ⊆ (LE r) /\
  linear_strict_order (LE r) S.

(** The extension of a strict linear order is itself *)

Axiom le_lso : forall (s:Ensemble Elt) (r:relation Elt),
  linear_strict_order r s -> LE r = r.

End OrdExt.

Lemma refl_trans_equiv {A:Type} (r: relation A):
  r ** = r ? ⁺.
Proof.
  apply ext_rel. split; intros x y H.
  - induction H.
    + left; left; auto.
    + left; right; auto.
    + right with (y := y); auto.
  - induction H.
    + induction H.
      * apply rt_step. auto.
      * apply rt_refl.
    + apply rt_trans with (y := y); auto.
Qed.

(** There is an immediate edge between two elements [a] and [b] of a strict partial 
order if :

- there is no event before [b] but not before [a] in the relation
- there is no event after [a] but not after [b] in the relation
 *)

Definition imm {A: Type} (r: relation A) : relation A :=
  fun a => fun b =>
    r a b /\
    forall c, r c b -> (r ?) c a /\
    forall c, r a c -> (r ?) b c.

Definition acyclic {A:Type} (r: relation A) : Prop :=
  forall x, ~(r⁺ x x).

(** [res_eset e r] restricts a relation [r] to the subset of [r] relating
events of [e] *)

Definition res_eset {A:Type} (e: Ensemble A) (r: relation A) :=
  fun x => fun y => (In _ e x) /\
                    (In _ e y) /\
                    r x y.

(** The restriction of a relation is included in the relation *)

Lemma res_eset_incl {A} (e : Ensemble A) (r : relation A):
  (res_eset e r) ⊆ r.
Proof.
  intros x y [_ [_ H]]. auto.
Qed.

Lemma tc_incl : forall  {E : Type}  (r1 r2 : relation E),
  r1 ⊆ r2 -> r1⁺ ⊆  r2⁺.
Proof.
intros A r r' Hinc x y H. induction H.
  - left. apply (Hinc x y). auto.
  - right with (y := y); auto.
Qed.

Lemma ac_incl {A : Set}  {r1 r2 : relation A} :
  acyclic r2 ->  r1 ⊆ r2 -> acyclic r1.
Proof.
intros Hac Hinc x Hnot. apply (Hac x).
apply tc_incl in Hinc. apply Hinc in Hnot. auto.
Qed.

(** A relation is included in its transitive closure *)

Lemma tc_incl_itself: forall (E:Type) (r: relation E),
  r ⊆  r⁺.
Proof.
intros E r.
intros x y H.
left. auto.
Qed.




