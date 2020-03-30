(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)


(* Require Import Relations. *)
Require Import Ensembles.
Require Import Classical_Prop.
Require Import Relations.
Require Import Lia.
From RelationAlgebra Require Import rel prop monoid kat relalg kat_tac.
From AAC_tactics Require Import AAC.
From RC11 Require Import proprel_classic.

(** * Utilities *)

(** Notations, lemmas and tactics, mostly about relations that are useful in the
rest of this development. *)

(** ** Tactics *)

(** A tactic to reason #<i>ad absurdum</i>#. *)

Ltac byabsurd :=
  match goal with
  |  |- ?Hgoal => destruct (classic Hgoal) as [|Hcontr]; [auto|]
  end.

(** A tactic to destruct the disjunction of n propositions, to n cases in the
proof *)

Ltac destruct_disjunction H :=
  destruct H as [H|H];
  try (destruct_disjunction H).

Ltac splitall := (split;(try splitall)).

(** ** Natural numbers *)

Lemma max_rewrite (k1 k2: nat):
  k1 < k2 -> max k2 k1 = k2.
Proof.
  lia.
Qed.

Lemma max_rewrite' (k1 k2: nat):
  k1 < k2 -> max k1 k2 = k2.
Proof.
  lia.
Qed.

(** ** Sets *)

Create HintDb set_db.

Hint Unfold In : set_db.

Ltac unfold_in := autounfold with set_db in *.

Definition I {A:Type} (s: Ensemble A) : prop_set A := In A s.

(** Axiom of extensionality for relations. If two relations relate the same 
elements, they are equal *)

Axiom ext_set : forall (A:Type) (s1 s2: Ensemble A),
    (forall x, s1 x <-> s2 x) -> s1 = s2.

(** The intersection of a set with another set is included in itself. *)

Lemma intersection_included_itself {A:Type} (s1 s2 : Ensemble A):
  Included _ (Intersection _ s1 s2) s1.
Proof.
  intros x [H1 H2]; auto.
Qed.

Lemma in_intersection {A:Type} (s1 s2 : Ensemble A) (e: A):
  In _ (Intersection _ s1 s2) e -> In _ s1 e /\ In _ s2 e.
Proof.
  intros [H1 H2]. split; auto.
Qed.

Lemma tautology_makes_fullset {A:Type} (P: A -> Prop):
  (forall x, P x) ->
  P = (Full_set _).
Proof.
  intros Hp. apply ext_set; intros y; split; intros H.
  + apply Full_intro.
  + apply Hp.
Qed.

Lemma inter_fullset {A:Type} (e: Ensemble A):
  Intersection _ e (Full_set _) = e.
Proof.
  apply ext_set. intros x; split; intros H.
  - inversion H. auto.
  - apply Intersection_intro. auto.
    apply Full_intro.
Qed.

Lemma inter_fullset' {A:Type} (e: Ensemble A):
  Intersection _ (Full_set _) e = e.
Proof.
  apply ext_set. intros x; split; intros H.
  - inversion H. auto.
  - apply Intersection_intro.
    + apply Full_intro.
    + auto.
Qed.

Lemma inter_incl {A:Type} (s1 s2 s3: Ensemble A):
  Included _ s3 s2 -> Included _ (Intersection _ s1 s3) (Intersection _ s1 s2).
Proof.
  intros Hincl x [Hin1 Hin2].
  split; auto.
Qed.



(** ** Notations *)

Definition rlt T := prop_hrel T T.

Definition id {T} : rlt T := (one T).
Definition empty {T} : rlt T := bot.

Declare Scope rel_notations.

(* Definition btest A : dset A -> rlt A := fun X => [X]. *)

Notation "R ?" := (R ⊔ 1) (at level 15) : rel_notations.

(* Notation " [ x ] " := (btest _ x) : rel_notations. *)

(*
(** Useful for rewriting *)
  Section defs.
    Variable T : Type. 
    Variables R S: rlt T.

    Locate "_ ≡ _".
    Check @RelationAlgebra.lattice.weq.
    Definition eq_rel : Prop := RelationAlgebra.lattice.weq R S.
    (* Definition incl_rel : rlt T -> rlt T -> Prop := leq. *)
    
    Definition union : rlt T := R ⊔ S.
    Definition inter : rlt T := R ⊓ S.

    Definition compo : rlt T := R ⋅ S.
    Definition negr : rlt T := !R.
    Definition conv : rlt T := R°.
    
    Definition rtc : rlt T := R^*.
    Definition tc : rlt T := R^+.

    Definition bot : rlt T := bot.
    Definition top : rlt T := top.

  End defs.
  
  Infix "≡" := (eq_rel _) : rel_notations.
  (*
  Infix "≦" := (incl_rel _) : rel_notations.
  *)
  
  Infix "⊔" := (union _) : rel_notations.
  Infix "⊓" := (inter _) : rel_notations.
  Infix "⋅" := (compo _) : rel_notations.
  Notation "!R" := (negr _) : rel_notations.
  Notation "R °" := (conv _ R) : rel_notations.
  Notation "R ^*" := (rtc _ R) : rel_notations.
  Notation "R ^+" := (tc _ R) : rel_notations.

  Instance eq_weq T : Equivalence (weq : rlt T -> rlt T -> Prop).
  Proof with auto.
    split.
    - unfold Reflexive; intros...
    - unfold Symmetric; intros x y H; rewrite H...
    - unfold Transitive; intros x y z H H'; rewrite H, H'...
  Qed.

  Instance pre_leq T : PreOrder (leq : rlt T -> rlt T -> Prop).
  Proof. constructor; intuition; compute; firstorder. Qed.

  (* Neutral elements *)
  Instance weq_cup_zero T : Unit weq (union T) 0.
  Proof. compute. firstorder. Qed.
  
  (*
  Instance leq_cup_zero T : Unit leq (union T) 0.
  Proof. compute. firstorder. Qed.
  *)
  
  Instance weq_compo_one T : Unit weq (compo T) 1.
  Proof. compute; firstorder; [rewrite H | rewrite <- H0]; auto. Qed.
  
  (*
  Instance leq_compo_one T : Unit leq (compo T) 1.
  Proof. compute; firstorder; [rewrite H | rewrite <- H0]; auto. Qed.
  *)
  
  (* Composition associativity *)
  Instance weq_compo_Proper T : Proper (weq ==> weq ==> weq) (compo T).
  Proof with auto.
    compute; intuition; destruct H1; exists x1.
    - destruct (H a x1)...
    - destruct (H0 x1 a0)...
    - destruct (H a x1)...
    - destruct (H0 x1 a0)...
  Qed.

  Instance weq_compo_Assoc T : Associative weq (compo T).
  Proof. compute. firstorder. Qed.

  (* Union commutativity and associatitivity *)
  Instance weq_cup_Proper T : Proper (weq ==> weq ==> weq) (union T).
  Proof. compute. firstorder. Qed.

  Instance weq_cup_Commutative T : Commutative weq (union T).
  Proof. compute. intuition auto. Qed.

  Instance weq_cup_Associative T : Associative weq (union T).
  Proof. compute. intuition auto. Qed.
  
  (* Conv is proper *)
  Instance weq_conv_Proper T : Proper (weq ==> weq) (conv T).
  Proof. firstorder. Qed.

  Program Instance lift_leq_weq T : AAC_lift (leq : rlt T -> rlt T -> Prop) weq.

*)
    
Open Scope rel_notations.

(** ** Definitions *)

(** Axiom of extensionality for relations. If two relations relate the same 
elements, they are equal *)

Axiom ext_rel : forall (A:Type) (r1 r2 : rlt A),
  (r1 ≡ r2) -> r1 = r2.

(** The domain of a relation is the set of elements that are related to one or
more elements by the relation *)

Definition dom {A:Type} (r:rlt A) : Ensemble A :=
  fun x => exists y, r x y.

(** The range (or codomain) of a relation is a set of elements such that one or
more elements are related to it by the relation *)

Definition ran {A:Type} (r:rlt A) : Ensemble A :=
  fun y => exists x, r x y.

(** [udr r] is the union of the domain and range of the relation [r] *)

Definition udr {A:Type} (r: rlt A) : Ensemble A :=
  Union _ (dom r) (ran r).

(** There is an immediate edge between two elements [a] and [b] of a strict partial 
order if :

- there is no event before [b] but not before [a] in the relation
- there is no event after [a] but not after [b] in the relation
 *)

Definition imm {A: Type} (r: rlt A) : rlt A :=
  fun a => fun b =>
    r a b /\
    forall c, r c b -> (r ?) c a /\
    forall c, r a c -> (r ?) b c.

(** A relation is cyclic if its transitive closure is irreflexive *)

Definition acyclic {A:Type} (r: rlt A) : Prop :=
  forall x, ~(r^+ x x).

(** A relation is cyclic if its transitive closure is not irreflexive *)

Definition cyclic {A:Type} (r: rlt A) : Prop :=
  exists x, r^+ x x.

(** [res_eset e r] restricts a relation [r] to the subset of [r] relating
events of [e] *)

Definition res_eset {A:Type} (e: Ensemble A) (r: rlt A) : rlt A :=
  fun x => fun y => (In _ e x) /\
                    (In _ e y) /\
                    r x y.

(** A relation forms a partial order on a set of elements if:

- All the elements related by the relation belong to the set of elements
- The relation is transitive
- The relation is irreflexive *)

Definition partial_order {A:Type} (r:rlt A) (xs: Ensemble A) : Prop :=
  r = [I xs] ⋅ r ⋅ [I xs] /\
  (r ⋅ r ≦ r)/\ (* Transitivity *)
  (forall x, ~(r x x)).     (* Irreflexivity *)

(** A relation is total on a set of elements if all the elements of the set are
related by the relation in a direction or in the other *)

Definition total_rel {A:Type} (r:rlt A) (xs: Ensemble A) : Prop :=
  forall x y, (x <> y) ->
              (In _ xs x) ->
              (In _ xs y) ->
              (r x y) \/ (r y x).

(** A relation forms a linear strict order on a set of elements if:

- It is a partial order
- It is linear, which means that every pair of elements of the set must be
related by the relation in any direction *)

Definition linear_strict_order {A:Type} (r:rlt A) (xs:Ensemble A) : Prop :=
  (partial_order r xs) /\
  (total_rel r xs).

Definition irreflexive {A:Type} (r: rlt A) := r ⊓ 1 ≦ 0.

Lemma irreflexive_is_irreflexive {A:Type} (r: rlt A):
  (forall x, ~(r x x)) <-> irreflexive r.
Proof.
  split; intros H.
  - intros x y [Hr Href].
    destruct Href.
    destruct (H _ Hr).
  - intros x Hnot.
    destruct (H x x).
    split; simpl; auto.
Qed.

Definition bidir {A:Type} (r: rlt A) :=
  r ⊔ r°.

Ltac kat_eq := apply ext_rel; kat.

(** *** Linear extension *)

Module Type OrdExt.
Parameter Elt : Type.

(** LE (linear extension) extends a partial order to a total order *)

Parameter LE : relation Elt -> relation Elt.

(** A relation is included in its own linear extension and a linear extension
    is a strict linear order *)

Axiom OE : forall (s S:Ensemble Elt) (r:relation Elt),
  Included _ s S ->
  partial_order r s ->
  r ≦ (LE r) /\
  linear_strict_order (LE r) S.

(** The extension of a strict linear order is itself *)

Axiom le_lso : forall (s:Ensemble Elt) (r:relation Elt),
  linear_strict_order r s -> LE r = r.

End OrdExt.

(** ** Tactics *)

Ltac simp_cnv H := simpl in H; unfold hrel_cnv in H.

Lemma inclusion_as_eq {A:Type} (R S : rlt A) : R ≦ S <-> R ⊔ S ≡ S.
Proof.
  compute; intuition eauto. firstorder.
Qed.

Lemma eq_as_inclusion {A:Type} (R S :rlt A) :
  (R ≦ S /\ S ≦ R) <-> S ≡ R.
Proof. compute. firstorder. Qed.


(** ** Basic Lemmas *)

Lemma fullset_one {A:Type}:
  [Full_set A : prop_set A] = 1.
Proof.
  apply ext_rel, antisym.
  - intros x y [Heq Hr]. auto.
  - intros x y Heq. split.
    auto. apply Full_intro.
Qed.

(** Sequencing with [1] has no effect *)

Lemma dot_one {A:Type} (r: rlt A):
  r⋅1 = r.
Proof.
  apply ext_rel. rewrite dotx1. auto.
Qed.

(** Relation intersection is distributive over relation union *)

Lemma union_inter {A:Type} (r1 r2 r3: rlt A):
  (r1 ⊔ r2) ⊓ r3 = (r1 ⊓ r3) ⊔ (r2 ⊓ r3).
Proof.
  apply ext_rel.
  apply antisym; intros x y.
  - intros [[H1|H2] H3].
    + left; split; auto.
    + right; split; auto.
  - intros [[H1 H3] | [H2 H3]]; split.
    + left; auto.
    + auto.
    + right; auto.
    + auto.
Qed.

(** The sequence of two reflexive relations restricted to their reflexive 
subrelation is the relation restricted to its reflexive subrelation *)

Lemma refl_double {A:Type} (r: rlt A):
  (r ⊓ 1) = (r ⊓ 1) ⋅ (r ⊓ 1).
Proof.
  apply ext_rel.
  apply antisym; intros x y.
  - intros [Hr Href].
    destruct Href.
    exists x; split; simpl; auto.
  - intros [z [Hr1 Hrefl1] [Hr2 Hrefl2]].
    destruct Hrefl1, Hrefl2; split; simpl; auto.
Qed.

(** The restriction of a relation to its reflexive subrelation is included in
the relation itself *)

Lemma capone {A:Type} (r: rlt A):
  r ⊓ 1 ≦ r.
Proof.
  intros x y [Hr _]. auto.
Qed.

(** The sequence of two relations restricted to their respective reflexive
subrelations is the sequence of the two relations restricted to its reflexive
subrelation *)

Lemma seq_refl {A:Type} (r r': rlt A):
  (r ⊓ 1) ⋅ (r' ⊓ 1) ≦ (r ⋅ r') ⊓ 1.
Proof.
  intros x y [z [Hr Href] [Hr' Href']].
  destruct Href; destruct Href'.
  split; try (exists x); simpl; auto.
Qed.

(** If a relation [r1] is included in a relation [r3], and if the sequence of [r3]
and of another relation is irreflexive, then the sequence of [r1] and of the other
relation is also irreflexive *)

Lemma seq_refl_incl_left {A:Type} (r1 r2 r3: rlt A):
  r1 ≦ r3 -> irreflexive (r3 ⋅ r2) -> irreflexive (r1 ⋅ r2).
Proof.
  intros Hinc Hirr.
  unfold irreflexive in *.
  rewrite Hinc. auto.
Qed.

(** If the sequence of two relations is restricted to its reflexive subrelation,
the sequence is commutative *)

Lemma refl_shift {A:Type} (r r': rlt A):
  (r ⋅ r') ⊓ 1 ≦ 0 ->
  (r' ⋅ r) ⊓ 1 ≦ 0.
Proof.
  intros H x y [[z Hr Hr'] Hrefl].
  destruct Hrefl.
  apply (H z z). split.
  - exists x; auto.
  - simpl; auto.
Qed.

(** A sequence of two relations is included in the sequence of two relations in
which the first two relations are respectively included *)

Lemma incl_dot {A:Type} (r1 r2 r3 r4: rlt A):
  r1 ≦ r3 -> r2 ≦ r4 -> r1 ⋅ r2 ≦ r3 ⋅ r4.
Proof.
  intros Hincl1 Hincl2.
  rewrite Hincl1, Hincl2.
  auto.
Qed.

(** The union of two relations is included in the union of two relations in
which the first two relations are respectively included *)

Lemma incl_cup {A:Type} (r1 r2 r3 r4: rlt A):
  r1 ≦ r3 -> r2 ≦ r4 -> r1 ⊔ r2 ≦ r3 ⊔ r4.
Proof.
  intros Hincl1 Hincl2.
  rewrite Hincl1, Hincl2.
  auto.
Qed.

(** If a first relation is included in a second one, the reflexive closure of
the first relation is included in the reflexive closure of the second one *)

Lemma refl_incl {A:Type} (r1 r2: rlt A):
  r1 ≦ r2 -> r1? ≦ r2?.
Proof. intros H. rewrite H. auto. Qed.

(** The identity relation is included in the reflexive closure of any 
relation *)

Lemma one_incl_refl {A:Type} (r: rlt A):
  1 ≦ r?.
Proof. kat. Qed.

(** The identity relation is included in the reflexive transitive closure of any
relation *)

Lemma one_incl_rtc {A:Type} (r: rlt A):
  1 ≦ r^*.
Proof. kat. Qed.

(** If a first relation is included in a second relation, the reflexive
transitive closure of the first relation is included in the reflexive
transitive closure of the second one *)

Lemma rtc_incl {A:Type} (r1 r2: rlt A):
  r1 ≦ r2 -> r1^* ≦ r2^*.
Proof. intros H. rewrite  H. auto. Qed.

(** The sequence of two relations is included in any relation that consists in
extending any of the two relations that are in sequence *)

Lemma union_seq_left {A:Type} (r1 r2 r3: rlt A):
  r1 ⋅ r3 ≦ (r1 ⊔ r2) ⋅ r3.
Proof. kat. Qed.

Lemma union_seq_right {A:Type} (r1 r2 r3: rlt A):
  r2 ⋅ r3 ≦ (r1 ⊔ r2) ⋅ r3.
Proof. kat. Qed.

Lemma seq_union_left {A:Type} (r1 r2 r3: rlt A):
  r1 ⋅ r2 ≦ r1 ⋅ (r2 ⊔ r3).
Proof. kat. Qed.

Lemma seq_union_right {A:Type} (r1 r2 r3: rlt A):
  r1 ⋅ r3 ≦ r1 ⋅ (r2 ⊔ r3).
Proof. kat. Qed.

(** The union of relations is commutative *)

Lemma union_comm {A:Type} (r1 r2 : rlt A):
  (r1 ⊔ r2) = (r2 ⊔ r1).
Proof.
  apply ext_rel. kat.
Qed.

(** The union of relations is commutative *)

Lemma union_assoc {A:Type} (r1 r2 r3 : rlt A):
  (r1 ⊔ (r2 ⊔ r3)) = ((r1 ⊔ r2) ⊔ r3).
Proof.
  apply ext_rel. kat.
Qed.

(** If two relations are included in a third relation, their union is included
in the third relation *)

Lemma union_incl {A:Type} (r1 r2 r3: rlt A):
  r1 ≦ r3 ->
  r2 ≦ r3 ->
  r1 ⊔ r2 ≦ r3.
Proof.
  intros H1 H2 x y [H|H].
  - apply (H1 _ _ H).
  - apply (H2 _ _ H).
Qed.

(** If a first relation is included in a second relation, it is included in the
union of the second relation with any other relation *)

Lemma incl_union_left {A:Type} (r1 r2 r3: rlt A):
  r1 ≦ r2 ->
  r1 ≦ r2 ⊔ r3.
Proof.
  intros H x y Hnot. left. apply (H _ _  Hnot).
Qed.

Lemma incl_union_right {A:Type} (r1 r2 r3: rlt A):
  r1 ≦ r3 ->
  r1 ≦ r2 ⊔ r3.
Proof.
  intros H x y Hnot. right. apply (H _ _  Hnot).
Qed.

(** This tactic transforms a goal of the form [r ≦ r1 ⊔ ... ⊔ rn] in a goal
of the form [r ≦ r2 ⊔ ... ⊔ rn] *)

Ltac incl_union_l :=
  repeat (rewrite <- union_assoc);
  apply incl_union_right.

(** This tactic transforms a goal of the form [r ≦ r1 ⊔ ... ⊔ rn] in a goal
of the form [r ≦ r1 ⊔ ... ⊔ r(n-1)] *)

Ltac incl_union_r :=
  repeat (rewrite -> union_assoc);
  apply incl_union_left;
  repeat (rewrite <- union_assoc).

(** The sequence of relations is associative *)

Lemma seq_assoc {A:Type} (r1 r2 r3 : rlt A):
  (r1 ⋅ r2 ) ⋅ r3 = r1 ⋅ (r2 ⋅ r3).
Proof.
  apply ext_rel. kat.
Qed.

(** The inclusion of relations is transitive *)

Lemma incl_trans {A:Type} (r1 r2 r3 : rlt A):
  r1 ≦ r2 -> r2 ≦ r3 -> r1 ≦ r3.
Proof.
  intros H1 H2 x y H.
  apply (H2 _ _ (H1 _ _ H)).
Qed.

Lemma incl_trans2 {A:Type} (r1 r2 r3 : rlt A):
  r2 ≦ r3 -> r1 ≦ r2 -> r1 ≦ r3.
Proof.
  intros H1 H2 x y H.
  apply (H1 _ _ (H2 _ _ H)).
Qed.

(** The union of the transitive closures of two relations is included in the
transitive closure of the union of these two relations *)
  
Lemma incl_tc_union {A:Type} (r1 r2: rlt A):
  r1^+ ⊔ r2^+ ≦ (r1 ⊔ r2)^+.
Proof. kat. Qed.

(** The union of the transitive closure of a relation and of a second relation
is included in the union of the transitive closure of the two relations *)

Lemma incl_union_of_tc_right {A:Type} (r1 r2 : rlt A):
  r1^+ ⊔ r2 ≦ r1^+ ⊔ r2^+.
Proof. kat. Qed.

(** The union of a relation and of the transitive closure of a second relation
is included in the union of the transitive closure of the two relations *)

Lemma incl_union_of_tc_left {A:Type} (r1 r2 : rlt A):
  r1 ⊔ r2^+ ≦ r1^+ ⊔ r2^+.
Proof. kat. Qed.

(** A relation is included in its transitive closure *)

Lemma tc_incl_itself {A:Type} (R: rlt A):
  R ≦  R^+.
Proof. kat. Qed.

(** The transitive closure of a relation is transitive *)

Lemma tc_trans {A:Type} (r1: rlt A) (x y z : A):
  r1^+ x y ->
  r1^+ y z ->
  r1^+ x z.
Proof.
  intros H1 H2.
  apply (itr_trans r1 x z).
  exists y; auto.
Qed.

(** A relation is included in its reflexive transitive closure *)

Lemma rtc_incl_itself {A:Type} (r: rlt A):
  r ≦ r^*.
Proof. kat. Qed.

(** The reflexive transitive closure of a relation is transitive *)

Lemma rtc_trans {A:Type} (r: rlt A):
  r^*⋅r^* ≦ r^*.
Proof. kat. Qed.


(** The transitive closure of a relation is equal to the sequence of the 
reflexive transitive closure and of the relation *)

Lemma tc_inv_dcmp {A:Type} (r1: rlt A):
  r1^+ = r1^* ⋅ r1.
Proof. apply ext_rel; kat. Qed.

Lemma tc_inv_dcmp2 {A:Type} (r1: rlt A):
  r1^+ = r1 ⋅ r1^*.
Proof. apply ext_rel; kat. Qed.

(** The transitive closure of the reflexive closure of a relation is the
transitive reflexive closure of this relation *)
  
Lemma refl_trans_equiv {A:Type} (r1 : rlt A):
  r1 ? ^+ = r1^*.
Proof. apply ext_rel; kat. Qed.

(** The transtive reflexive closure of the reflexive closure of a relation is
the transitive reflexive closure of this relation *)

Lemma refl_refl_trans {A:Type} (r1 : rlt A):
  r1 ? ^* = r1 ^*.
Proof. apply ext_rel. kat. Qed.


(** The restriction of a relation is included in the relation *)

Lemma res_eset_incl {A:Type} (e : Ensemble A) (r : rlt A):
  (res_eset e r) ≦ r.
Proof.
  intros x y [_ [_ H]]. auto.
Qed.

Lemma res_eset_prop_incl {A:Type} (e: Ensemble A) (r r': rlt A):
  r ≦ r' ->
  res_eset e r ≦ res_eset e r'.
Proof.
  intros H x y [Hin1 [Hin2 Hr]].
  split;[|split]; auto. apply H. auto.
Qed.

(** If the union of the domain and of the range of a relation are included in a
set, restricting the relation to this set is equal to the relation *)

Lemma res_eset_udr {A:Type} (e: Ensemble A) (r: rlt A):
  Included _ (udr r) e -> r = res_eset e r.
Proof.
  intros Hudr. apply ext_rel, antisym; intros x y H.
  - split;[|split].
    + apply Hudr. left. exists y. auto.
    + apply Hudr. right. exists x. auto.
    + auto.
  - destruct H as [_ [_ H]]. auto.
Qed.

(** The converse of the restriction of a relation is the restriction of the
converse *)

Lemma res_eset_cnv {A:Type} (e: Ensemble A) (r: rlt A):
  (res_eset e r)° = res_eset e r°.
Proof.
  apply ext_rel, antisym; intros x y H;
  (destruct H as [? [? ?]]; split;[|split]; auto).
Qed.

(** If we restrict a relation to a set, the union of its domain and range is
included in the set *)

Lemma res_eset_udr_incl {A:Type} (e: Ensemble A) (r: rlt A):
  Included _ (udr (res_eset e r)) e.
Proof.
  intros ? [? [? [? [? ?]]] | ? [? [? [? ?]]]]; auto.
Qed.

(** If elements are related by a relation restricted to a set, they belong to
the set *)

Lemma res_eset_elt_left {A:Type} (e: Ensemble A) (r: rlt A) (x y: A):
  (res_eset e r) x y ->
  In _ e x.
Proof.
  intros [? [? ?]]. auto.
Qed.

Lemma res_eset_elt_right {A:Type} (e: Ensemble A) (r: rlt A) (x y: A):
  (res_eset e r) x y ->
  In _ e y.
Proof.
  intros [? [? ?]]. auto.
Qed.

Lemma res_eset_dot {A:Type} (e: Ensemble A) (r r': rlt A):
  (res_eset e r) ⋅ (res_eset e r') ≦ res_eset e (r ⋅ r').
Proof.
  intros x y [z [Hin1 [Hin2 Hr]] [Hin3 [Hin4 Hr']]].
  splitall; auto.
  exists z; auto.
Qed.

Lemma res_eset_double {A:Type} (e e': Ensemble A) (r: rlt A):
  Included _ e' e ->
  res_eset e (res_eset e' r) = res_eset e' r.
Proof.
  intros Hincl.
  apply ext_rel. split.
  - intros [Hin1 [Hin2 [Hin3 [Hin4 Hr]]]].
    repeat (apply conj); auto.
  - intros [Hin1 [Hin2 Hr]].
    repeat (apply conj); auto.
Qed.

Lemma res_eset_double' {A:Type} (e e': Ensemble A) (r: rlt A):
  Included _ e' e ->
  res_eset e' (res_eset e r) = res_eset e' r.
Proof.
  intros Hincl.
  apply ext_rel. split.
  - intros [Hin1 [Hin2 [Hin3 [Hin4 Hr]]]].
    repeat (apply conj); auto.
  - intros [Hin1 [Hin2 Hr]].
    repeat (apply conj); auto.
Qed.

Lemma incl_irr {A:Type} (r r': rlt A):
  (forall x, ~r x x) ->
  r' ≦ r ->
  forall x, ~r' x x.
Proof.
  intros Hirr Hinc x H. eapply Hirr, Hinc. eauto.
Qed.

   
(** If a first relation is included in a second relation, the transitive closure
of the first relation is included in the transitive closure of the second
relation *)

Lemma tc_incl {A : Type}  (r1 r2 : rlt A):
  r1 ≦ r2 -> r1^+ ≦  r2^+.
Proof.
intros H.
rewrite -> inclusion_as_eq in *.
apply ext_rel in H. rewrite <- H.
kat.
Qed.

(** The transitive closure of the transitive closure of a relation is the
transitive closure of this relation *)

Lemma tc_of_tc_is_tc {A:Type} (r1: rlt A):
  (r1^+)^+ = r1^+.
Proof. apply ext_rel. kat. Qed.

(** If the sequence of two relations related a pair of elements, the first
relation relates two elements *)

Lemma shorten_path_on_right {A : Type} (r1 r2 : rlt A):
  (exists x y, (r1 ⋅ r2) x y) ->
  (exists x y, r1 x y).
Proof.
  intros [x [y [z H1 H2]]].
  exists x, z; auto.
Qed.

(** If the sequence of two relations related a pair of elements, the second
relation relates two elements *)

Lemma shorten_path_on_left {A : Type} (r1 r2 : rlt A):
  (exists x y, (r1 ⋅ r2) x y) ->
  (exists x y, r2 x y).
Proof.
  intros [x [y [z H1 H2]]].
  exists z, y; auto.
Qed.

(** If two elements are related by a first relation and if the first relation is
included in a second relation, the second relation also relates the two 
elements *)

Lemma incl_rel_thm {A:Type} {r r' : rlt A} {x y: A}:
  r x y ->
  r ≦ r' ->
  r' x y.
Proof.
  intros H1 H2.
  apply H2 in H1; auto.
Qed.

(** If an element is in the domain or in the range of a relation, it is in the
domain or range of any relation in which the relation is included *)

Lemma elt_dom_incl {A:Type} (r r': rlt A) (x: A):
  r ≦ r' ->
  In _ (dom r) x ->
  In _ (dom r') x.
Proof.
  intros Hinc [y Hr].
  exists y. apply Hinc. auto.
Qed.

Lemma elt_ran_incl {A:Type} (r r': rlt A) (x: A):
  r ≦ r' ->
  In _ (ran r) x ->
  In _ (ran r') x.
Proof.
  intros Hinc [y Hr].
  exists y. apply Hinc. auto.
Qed.

(** ** Acyclicity and Cyclicity Lemmas *)

(** A relation that is not acyclic is cyclic *)

Lemma not_acyclic_is_cyclic {A:Type} (r: rlt A):
  ~(acyclic r) ->
  (cyclic r).
Proof.
  intros H.
  unfold acyclic in H; unfold acyclic.
  byabsurd. destruct H. intros x H.
  apply Hcontr. exists x. auto.
Qed.

(** If a relation is included in an acyclic relation, it is also acyclic *)

Lemma ac_incl {A : Set}  (r1 r2 : rlt A) :
  acyclic r2 -> r1 ≦ r2 -> acyclic r1.
Proof.
intros Hac Hinc x Hnot. apply (Hac x).
apply tc_incl in Hinc. apply Hinc in Hnot. auto.
Qed.

(** If there is a cycle in the union of two relations, there is either a cycle
in the first relation or a cycle in the second relation *)

Lemma cyclic_union {A:Type} (r1 r2 : rlt A):
  (exists x, (r1 ⊔ r2) x x) ->
  ((exists x, r1 x x) \/
   (exists x, r2 x x)).
Proof.
  intros [x [Hr1 | Hr2]]; [left|right];
  exists x; auto.
Qed.

(** This tactic splits an hypothesis stating that the union of n relations is 
cyclic to n cases by repeatedly applying the [cycle_union] lemma *)

Ltac split_cyclic_union H :=
  apply cyclic_union in H;
  destruct H as [H|H];
  try (split_cyclic_union H).

(** If there is a cycle in [r], there exists two elements related by [r] *)

Lemma cyclic_implies_path {A:Type} (r: rlt A):
  (exists x, r x x) ->
  (exists x y, r x y).
Proof.
  intros [x H]; exists x,x; auto.
Qed.

(** If there is a cycle in a relation, there is the same  cycle in the sequence 
of the relation with itself *)

Lemma double_cycle {A:Type} (r: rlt A) (x: A):
  r x x ->
  (r ⋅ r) x x.
Proof.
  intros H. exists x; auto.
Qed.

(** If there is a path in the sequence of :

- A first relation
- The transitive closure of a second relation
- The transitive closure of the second relation
- The first relation

Then there is a path in the sequence of :

- The first relation
- The transitive closure of the second relation
- The first relation
*)

Lemma double_tc_in_path {A:Type} (r1 r2 : rlt A):
  (exists x y, (r1 ⋅ r2^+ ⋅ r2^+ ⋅ r1) x y) ->
  (exists x y, (r1 ⋅ r2^+ ⋅ r1) x y).
Proof.
  intros [w1 [w2 [z1 [z2 [z3 H1 H2] H3] H4]]].
  exists w1, w2, z1; auto.
  exists z3; auto.
  apply (itr_trans r2 _).
  exists z2; auto.
Qed.

(** We decompose the transitive closure of the union of two relations in the
union of several relations to analyze different cases in the proof of [ac_union]
*)

Lemma tc_union_decomposition {A:Type} (r1 r2 : rlt A):
  (r1 ⊔ r2)^+
  =
  r1^+ ⊔ r2^+ ⊔
  (r1 ⊔ r2)^* ⋅ r1 ⋅ r2^+ ⋅ r1 ⋅ (r1 ⊔ r2)^* ⊔ 
  r1 ⋅ r2^+ ⊔
  r2^+ ⋅ r1 ⋅ r2^+ ⊔
  r2^+ ⋅ r1 ⊔
  r1 ⋅ (r1 ⊔ r2)^* ⋅ r1 ⋅ r2^+ ⊔
  r2^+ ⋅ r1 ⋅ (r1 ⊔ r2)^* ⋅ r1 ⋅ r2^+ ⊔
  r2^+ ⋅ r1 ⋅ (r1 ⊔ r2)^* ⋅ r1.
Proof. apply ext_rel. kat. Qed.

(** If two relations are acyclic, but their union is cyclic, then there exists
two elements belonging to the cycle that are related by the sequence of:

- The first relation
- The transitive closure of the second relation
- The first relation
*)

Lemma ac_union {A:Type} (x:A) (r1 r2 : rlt A) :
  acyclic r1 ->
  acyclic r2 ->
  (r1 ⊔ r2)^+ x x ->
  exists y z, (r1 ⊔ r2)^* x y /\
              (r1 ⋅ r2^+ ⋅ r1) y z /\
              (r1 ⊔ r2)^* z x.
Proof.
  intros Hac1 Hac2 Hcyc. unfold cyclic in Hcyc.
  rewrite tc_union_decomposition in Hcyc.
  destruct_disjunction Hcyc.
  - destruct (Hac1 x Hcyc).
  - destruct (Hac2 x Hcyc).
  - destruct Hcyc as [z1 Hcyc Hbegin].
    repeat (rewrite seq_assoc in Hcyc).
    destruct Hcyc as [z2 Hend Hmid];
    repeat (rewrite <- seq_assoc in Hmid).
    exists z2,z1. auto.
  - apply double_cycle in Hcyc.
    apply double_cycle in Hcyc.
    repeat (rewrite -> seq_assoc in Hcyc).
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z1 Hbegin Hcyc].
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z2 Hmid Hend].
    exists z1, z2. repeat (try split).
    + apply (incl_rel_thm Hbegin). kat.
    + apply (incl_rel_thm Hmid). kat.
    + apply (incl_rel_thm Hend). kat.
  - apply double_cycle in Hcyc.
    repeat (rewrite -> seq_assoc in Hcyc).
    destruct Hcyc as [z1 Hbegin Hcyc].
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z2 Hmid Hend].
    exists z1, z2. repeat (try split).
    + apply (incl_rel_thm Hbegin). kat.
    + apply (incl_rel_thm Hmid). kat.
    + apply (incl_rel_thm Hend). kat.
  - apply double_cycle in Hcyc.
    apply double_cycle in Hcyc.
    repeat (rewrite -> seq_assoc in Hcyc).
    destruct Hcyc as [z1 Hbegin Hcyc].
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z2 Hmid Hend].
    exists z1, z2. repeat (try split).
    + apply (incl_rel_thm Hbegin). kat.
    + apply (incl_rel_thm Hmid). kat.
    + apply (incl_rel_thm Hend). kat.
  - apply double_cycle in Hcyc.
    repeat (rewrite -> seq_assoc in Hcyc).
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z1 Hbegin Hcyc].
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z2 Hmid Hend].
    exists z1, z2. repeat (try split).
    + apply (incl_rel_thm Hbegin). kat.
    + apply (incl_rel_thm Hmid). kat.
    + apply (incl_rel_thm Hend). kat.
  - apply double_cycle in Hcyc.
    repeat (rewrite -> seq_assoc in Hcyc).
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z1 Hbegin Hcyc].
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z2 Hmid Hend].
    exists z1, z2. repeat (try split).
    + apply (incl_rel_thm Hbegin). kat.
    + apply (incl_rel_thm Hmid). kat.
    + apply (incl_rel_thm Hend). kat.
  - apply double_cycle in Hcyc.
    repeat (rewrite -> seq_assoc in Hcyc).
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z1 Hbegin Hcyc].
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z2 Hmid Hend].
    exists z1, z2. repeat (try split).
    + apply (incl_rel_thm Hbegin). kat.
    + apply (incl_rel_thm Hmid). kat.
    + apply (incl_rel_thm Hend). kat.
Qed.


(** The transitive closure of a strict linear order is itself *)

Lemma lso_is_tc {A:Type} (so:rlt A) (s: Ensemble A):
  linear_strict_order so s -> so^+ = so.
Proof.
  intros [[H1 [H2 H6]] H3]; apply ext_rel.
  apply eq_as_inclusion. split.
  - kat.
  - apply itr_ind_l1; auto.
Qed.

(** A strict linear order is acyclic *)

Lemma lin_strict_ac {A:Type} (s:Ensemble A) (r : rlt A):
  linear_strict_order r s ->
  acyclic r.
Proof.
intros Hlin.
generalize (lso_is_tc _ _ Hlin); intro Heq.
unfold acyclic; rewrite Heq.
destruct Hlin as [[Hdr [Htrans Hac]] Htot];
apply Hac.
Qed.

(** The transitive closure of a transitive relation is itself *)

(*
Lemma transitive_tc {A:Type} (r: rlt A):
  (forall x1 x2 x3, (r x1 x2) /\ (r x2 x3) -> (r x1 x3)) ->
  r^+ = r.
Proof.
  intros Htrans.
  apply ext_rel. apply eq_as_inclusion; split; intros x y H.
  - exists y. auto. exists O. cbv. auto.
  - apply itr_ind_l1 in H.
  - destruct H as [z H H'].
    induction H' as [w z H2 | w | v w z H1 IH1 H2 IH2].
    + apply (Htrans x w z); split; auto.
    + auto.
    + apply IH2. apply IH1. auto.
  - exists y; split; auto. apply rt_refl; auto.
Qed.
*)

(** If a relation is acyclic, its transitive closure is acyclic *)

Lemma tc_ac_is_ac {A:Type} (r: rlt A):
  acyclic r ->
  acyclic (r^+).
Proof.
  unfold acyclic. rewrite tc_of_tc_is_tc.
  auto.
Qed.

(** ** Facts and tactics about the tests of KATs *)

Ltac simpl_trt :=
  match goal with
  | |- ([?t1] ⋅ ?r ⋅ [?t2]) ?x ?y => exists y; try (exists x); 
                                 [apply conj; auto | | apply conj; auto]
  end.

Lemma simpl_trt_hyp {A:Type} (t1 t2: prop_set A) (r: rlt A) (x y: A):
  ([t1] ⋅ r ⋅ [t2]) x y ->
  t1 x /\ r x y /\ t2 y.
Proof.
  intros [z [z' [Heqx Htx]] [Heqy Hty]].
  rewrite <- Heqx, Heqy in *.
  repeat (apply conj); auto.
Qed.
  
Lemma dom_trt {A:Type} (t1 t2: prop_set A) (r: rlt A) (x: A):
  In _ (dom ([t1] ⋅ r ⋅ [t2])) x ->
  t1 x /\ (exists y, t2 y /\ r x y).
Proof.
  intros [z [y [z' [Heqz Htz] Hr] [Heqy Hty]]].
  rewrite <- Heqz in Hr.
  split; auto. exists y; intuition auto.
Qed.

Lemma ran_trt {A:Type} (t1 t2: prop_set A) (r: rlt A) (x: A):
  In _ (ran ([t1] ⋅ r ⋅ [t2])) x ->
  t2 x /\ (exists y, t1 y /\ r y x).
Proof.
  intros [z [z' [y [Heqy Hty] Hr] [Heqx Htx]]].
  rewrite Heqy in Hty; rewrite Heqx in Htx; rewrite Heqx in Hr.
  split; auto. exists y; intuition auto.
Qed.

Section KatTests.

Variable A : Type.
Variable t t' : prop_set A.

(** The converse of a test is equivalent to the test *)

Lemma injcnv: [t]° = [t].
Proof.
  apply ext_rel.
  compute; firstorder; rewrite <- H; auto.
Qed.

(** The sequence of two identical tests is equivalent to the test *)

Lemma dtest: [t] ⋅ [t] = [t]. 
Proof. apply ext_rel. kat. Qed.

(** The sequence is commutative on tests *)

Lemma test_dot_comm: [t] ⋅ [t'] ≡ [t'] ⋅ [t]. 
Proof. kat. Qed.

(** A test is included in the identity relation *)

Lemma test_in_one: [t] ≦ 1. 
Proof. kat. Qed.

(** Adding a test on the domain of a relation can only restrict the union of its
domain and range *)

Lemma test_left_udr (r: rlt A) : Included _ (udr ([t] ⋅ r)) (udr r).
Proof.
  intros x [y H|y H]; [left|right].
  - destruct H as [z [z' [Heq _] Hr]].
    rewrite <- Heq in Hr. exists z. auto.
  - destruct H as [z [z' _ Hr]].
    exists z'. auto.
Qed.

(** Adding a test on the range of a relation can only restrict the union of its
domain and range *)

Lemma test_right_udr (r: rlt A) : Included _ (udr (r ⋅ [t])) (udr r).
Proof.
  intros x [y H|y H]; [left|right].
  - destruct H as [z [z' Hr _]].
    exists z'. auto.
  - destruct H as [z [z' Hr [Heq _]]].
    rewrite Heq in Hr. exists z. auto.
Qed.

(** Adding tests on both side of a relation restricted to a set is the same
as restricting the relation with both test onj its sides to the set *)

Lemma test_res_eset_swap (e: Ensemble A) (r: rlt A):
  [t]⋅(res_eset e r)⋅[t'] = res_eset e ([t]⋅r⋅[t']).
Proof.
  apply ext_rel, antisym; intros x y.
  - intros [z [w [Heq1 Ht1] [Hin1 [Hin2 Hr]]] [Heq2 Ht2]].
    splitall.
    + rewrite Heq1; auto.
    + rewrite <- Heq2; auto.
    + exists y. exists x.
      * split; auto.
      * rewrite Heq1, <- Heq2. auto.
      * split. auto. rewrite <- Heq2. auto.
  - intros [Hin1 [Hin2 [z [w [Heq1 Ht1] Hr] [Heq2 Ht2]]]].
    exists y. exists x.
    + split; auto.
    + splitall; auto. rewrite Heq1, <- Heq2. auto.
    + split; auto. rewrite <- Heq2. auto.
Qed.

End KatTests.

(** If a test implies another test, and if a first relation whose domain is
restricted to the elements satisfying the first test is included in a second
relation, then the first relation whose domain is restricted to the elements 
satisfying the first test is included in the second relation whose domain is
restricted to the elements satisfying the second test. *)

Lemma incl_dot_test_left {A:Type} (r1 r2: rlt A) (t1 t2: prop_set A):
  [t1] ≦ [t2] -> [t1] ⋅ r1 ≦ r2 -> [t1] ⋅ r1 ≦ [t2] ⋅ r2.
Proof.
  intros Hincl1 Hincl2.
  rewrite <- dtest.
  mrewrite Hincl2.
  rewrite Hincl1.
  auto.
Qed.

(** If a test implies another test, and if a first relation whose range is
restricted to the elements satisfying the first test is included in a second
relation, then the first relation whose range is restricted to the elements 
satisfying the first test is included in the second relation whose range is
restricted to the elements satisfying the second test. *)

Lemma incl_dot_test_right {A:Type} (r1 r2: rlt A) (t1 t2: prop_set A):
  [t1] ≦ [t2] -> r1 ⋅ [t1] ≦ r2 -> r1 ⋅ [t1] ≦ r2 ⋅ [t2].
Proof.
  intros Hincl1 Hincl2.
  rewrite <- dtest.
  rewrite dotA.
  mrewrite Hincl2.
  rewrite Hincl1.
  auto.
Qed.

(** The reflexive transitive closure defined as a positive or null number of 
sequence of a relation with itself is equivalent to its inductive definition,
i.e. the reflexive transitive closure of a relation is either the relation 
itself, the identity relation, or the sequence of the reflexive transitive
closure of the relation with the transitive reflexive closure of the relation

This means that the definitions of reflexive transitive closure of Relation
Algebra and of the standard library of coq are equivalent *)

Lemma rtc_clos_refl_trans {A:Type} (r: rlt A):
  r^* = (clos_refl_trans _ r).
Proof.
  apply ext_rel. split.
  - intros H. simpl in H.
    destruct H as [u Hrtc].
    generalize Hrtc; clear Hrtc.
    generalize a a0.
    induction u as [|u IH].
    + intros x y Hrtc. simpl in Hrtc. rewrite Hrtc.
      apply rt_refl.
    + intros x y Hrtc. simpl in Hrtc.
      destruct Hrtc as [z Hstep Hrtc].
      apply IH in Hrtc.
      apply rt_trans with (y:=z).
      * apply rt_step. auto.
      * auto.
  - intros H. induction H as [ | | x y z H IH H' IH'].
    * apply rtc_incl_itself in H. auto.
    * exists O. intuition.
    * apply rtc_trans. exists y; auto.
Qed.

Lemma tc_clos_trans {A:Type} (r: rlt A):
  r^+ = (clos_trans _ r).
Proof.
  apply ext_rel. split.
  - intros H. rewrite tc_inv_dcmp in H.
    destruct H as [z H1 H2]. apply clos_rt_t with z.
    + rewrite rtc_clos_refl_trans in H1. auto.
    + left. auto.
  - intros H. induction H as [ | x y z H IH H' IH' ].
    + exists y. auto. exists O. simpl. auto.
    + apply tc_trans with y; auto.
Qed.

(** We can do an induction on the reflexive transitive closure as defined in
RelationAlgebra the same way we would do on a reflexive transitive closure as
defined in the standard library of coq *)

Lemma rtc_ind:
  forall (A : Type) (R : rlt A) (P : A -> A -> Prop),
  (forall x y : A, R x y -> P x y) ->
  (forall x : A, P x x) ->
  (forall x y z : A, R^* x y -> P x y -> R^* y z -> P y z -> P x z) ->
  forall x a : A, R^* x a -> P x a.
Proof.
  intros A R.
  rewrite rtc_clos_refl_trans.
  apply clos_refl_trans_ind.
Qed.

Lemma tc_ind:
  forall (A : Type) (R : rlt A) (P : A -> A -> Prop),
  (forall x y : A, R x y -> P x y) ->
  (forall x y z : A, R^+ x y -> P x y -> R^+ y z -> P y z -> P x z) ->
  forall x a : A, R^+ x a -> P x a.
Proof.
  intros A R.
  rewrite tc_clos_trans.
  apply clos_trans_ind.
Qed.

Lemma trans_equiv_tc {A:Type} (r: rlt A):
  r⋅r ≦ r <-> r = r^+.
Proof.
  split.
  - intros Hinc.
    apply ext_rel, antisym.
    + kat.
    + simpl.
      apply tc_ind.
      * auto.
      * intros x y z H1 H2 H3 H4.
        eapply (Hinc _ z).
        exists y; auto.
  - intros Heqtc. rewrite Heqtc. kat.
Qed.
