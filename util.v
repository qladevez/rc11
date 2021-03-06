(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Ensembles.
Require Import Classical_Prop.
Require Import Relations.
Require Import Lia.
From RelationAlgebra Require Import rel prop monoid kat relalg kat_tac.
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

(** Apply the split tactic as much as possible *)

Ltac splitall := (split;(try splitall)).

(** ** Logic *)

Lemma diff_inv {A:Type} (x y: A):
  x <> y <-> y <> x.
Proof. intuition auto. Qed.

(** ** Natural numbers *)

(** The greater or equal to relation is transitive *)

Instance ge_trans : Transitive ge.
Proof. compute; lia. Qed.

(** If we know the ordering between two numbers, we can rewrite the max of these
numbers to the biggest number *)

Lemma max_rewrite (k1 k2: nat):
  k1 < k2 -> max k2 k1 = k2.
Proof. lia. Qed.

Lemma max_rewrite' (k1 k2: nat):
  k1 < k2 -> max k1 k2 = k2.
Proof. lia. Qed.

(** If a numbering is strictly greater than 0, the successor of the number minus
one is the number *)

Lemma S_min_one (k: nat):
  k > 0 -> S (k - 1) = k.
Proof.
  intros Hord.
  destruct k; lia.
Qed.

Lemma nminone_lt_n (k: nat):
  0 < k ->
  k - 1 < k.
Proof.
  intros H. lia.
Qed.

(** ** Sets *)

(** Tactic to unfold all occurences of [In] in the current goal and its
hypotheses *)

Create HintDb set_db.

Hint Unfold In : set_db.

Ltac unfold_in := autounfold with set_db in *.

(** KAT test that checks if an element belongs to a set *)

Definition I {A:Type} (s: Ensemble A) : prop_set A := In A s.

(** KAT test that checks if an element is different from another element *)

Definition D {A:Type} (y: A) : prop_set A := (fun x => x <> y).

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

(** If an element belongs to the intersection of two sets, it belongs to both 
sets *)

Lemma in_intersection {A:Type} (s1 s2 : Ensemble A) (e: A):
  In _ (Intersection _ s1 s2) e -> In _ s1 e /\ In _ s2 e.
Proof.
  intros [H1 H2]; intuition auto.
Qed.

(** If a element belongs to the union of two sets, it belongs to one of the 
sets *)

Lemma in_union {A:Type} (s1 s2 : Ensemble A) (e: A):
  In _ (Union _ s1 s2) e -> In _ s1 e \/ In _ s2 e.
Proof.
  intros [x H1|x H2]; intuition auto.
Qed.


Lemma in_union_l {A:Type} (s1 s2 : Ensemble A) (e: A):
  In _ s1 e -> In _ (Union _ s1 s2) e.
Proof.
  intros H. left. auto.
Qed.

Lemma in_union_r {A:Type} (s1 s2 : Ensemble A) (e: A):
  In _ s2 e -> In _ (Union _ s1 s2) e.
Proof.
  intros H. right. auto.
Qed.

(** If a predicate is always true, it is the full set *)

Lemma tautology_makes_fullset {A:Type} (P: A -> Prop):
  (forall x, P x) ->
  P = (Full_set _).
Proof.
  intros Hp. apply ext_set; intros y; split; intros H.
  + apply Full_intro.
  + apply Hp.
Qed.

(** The intersection of a set with the full set is itself *)

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

(** If set [A] is included in set [B], the intersection of [A] with a set is
included in the intersection of [B] with the same set *)

Lemma inter_incl {A:Type} (s1 s2 s3: Ensemble A):
  Included _ s3 s2 -> Included _ (Intersection _ s1 s3) (Intersection _ s1 s2).
Proof.
  intros Hincl x [Hin1 Hin2].
  split; auto.
Qed.

(** ** Notations *)

(** Alternative names for relations, identitity and empty relation *)

Definition rlt T := prop_hrel T T.
Definition id {T} : rlt T := (one T).
Definition empty {T} : rlt T := bot.

Declare Scope rel_notations.

(** The reflexive closure of a relation is its union with identity relation *)

Notation "R ?" := (R ⊔ 1) (at level 15) : rel_notations.
Notation "R \ S" := (R ⊓ !S) (at level 30) : rel_notations.

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
    (forall c, r c b -> (r ?) c a) /\
    (forall c, r a c -> (r ?) b c).

(** A relation is cyclic if its transitive closure is irreflexive *)

Definition acyclic {A:Type} (r: rlt A) : Prop :=
  forall x, ~(r^+ x x).

(** A relation is cyclic if its transitive closure is not irreflexive *)

Definition cyclic {A:Type} (r: rlt A) : Prop :=
  exists x, r^+ x x.

(** A relation forms a partial order on a set of elements if:

- All the elements related by the relation belong to the set of elements
- The relation is transitive
- The relation is irreflexive *)

Definition partial_order {A:Type} (r:rlt A) (xs: Ensemble A) : Prop :=
  r = [I xs] ⋅ r ⋅ [I xs] /\ (* Inclusion in the set *)
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

(** A relation is irreflexive if its intersection with the identity relation is
empty *)

Definition irreflexive {A:Type} (r: rlt A) := r ⊓ 1 ≦ 0.

(** The bidirectional of a relation is its union with its conserve *)

Definition bidir {A:Type} (r: rlt A) :=
  r ⊔ r°.

(** *** Linear extension *)

Section OrdExt.
Context {Elt:Type}.

(** LE (linear extension) extends a partial order to a total order *)

Parameter LE : rlt Elt -> rlt Elt.

(** A relation is included in its own linear extension and a linear extension
    is a strict linear order *)

Axiom OE : forall (e: Ensemble Elt) (r: rlt Elt),
  partial_order r e ->
  r ≦ (LE r) /\
  linear_strict_order (LE r) e.

(** The extension of a strict linear order is itself *)

Axiom le_lso : forall (s:Ensemble Elt) (r:rlt Elt),
  linear_strict_order r s -> LE r = r.

End OrdExt.

(** ** Tactics *)

(** Solve an equality goal using [kat] *)

Ltac kat_eq := apply ext_rel; kat.

(** Change an hypothesis of form [r° x y] to [r y x] *)

Ltac simp_cnv H := simpl in H; unfold hrel_cnv in H.

(** ** Basic Lemmas *)

Lemma in_id {A:Type} (x y: A):
  In _ (id x) y -> x = y.
Proof.
  unfold In, id. auto.
Qed.

(** Two elements of a set are related by a linear strict order in a direction *)

Lemma lso_rel {A:Type} (e: Ensemble A) (r: rlt A) (x y: A):
  linear_strict_order r e ->
  x <> y ->
  In _ e x ->
  In _ e y ->
  (r x y) \/ (r y x).
Proof.
  intros [_ Htot] Hdiff Hin1 Hin2.
  apply Htot; auto.
Qed.

(** If not all elements are not related by a relation, two elements exists such
that they are related by the relation *)

Lemma not_all_not_rel_ex_rel {A:Type} (r: rlt A):
  ~(forall x y, ~(r x y)) ->
  exists x y, r x y.
Proof.
  intros Hnotforall.
  byabsurd. exfalso.
  apply Hnotforall. intros x y Hr.
  apply Hcontr. exists x, y. auto.
Qed.

(** Testing if an element belongs to a set [A] and to a subset of [A] is
equivalent to testing if it belongs to the subset of [A] *)

Lemma I_simpl1 {A:Type} (s1 s2: Ensemble A):
  Included _ s1 s2 ->
  [I s1]⋅[I s2] = [I s1].
Proof.
  intros Hincl. apply ext_rel, antisym; intros x y H.
  - destruct H as [z [Heq1 H1] [Heq2 H2]].
    split; auto.
    rewrite Heq1, Heq2. auto.
  - destruct H as [Heq H]. exists x.
    + split; auto.
    + rewrite <-Heq. split; auto. apply Hincl. auto.
Qed.

Lemma I_simpl2 {A:Type} (s1 s2: Ensemble A):
  Included _ s1 s2 ->
  [I s2]⋅[I s1] = [I s1].
Proof.
  intros Hincl. apply ext_rel, antisym; intros x y H.
  - destruct H as [z [Heq1 H1] [Heq2 H2]].
    rewrite Heq1, <-Heq2. split; auto.
  - destruct H as [Heq H]. exists x.
    + split; auto. apply Hincl. auto. 
    + rewrite <-Heq. split; auto.
Qed.

(** Being in the union of two set, is like being in one set or in the other *)

Lemma I_union {A:Type} (s1 s2 : Ensemble A):
  [I (Union _ s1 s2)] = [(I s1) ⊔ (I s2)].
Proof.
  apply ext_rel, antisym; intros x y H.
  - destruct H as [Heq Ht]. rewrite <-Heq.
    unfold I in Ht. apply in_union in Ht.
    destruct Ht as [Ht|Ht]; split; auto;
    [left|right]; auto.
  - destruct H as [Heq Ht]. rewrite <-Heq.
    destruct Ht as [Ht|Ht]; split; auto;
    [left|right]; auto.
Qed.

(** A relation being included in another is equivalent to the union of the
smaller and bigger relation being equal to the bigger relation *)

Lemma inclusion_as_eq {A:Type} (R S : rlt A) : R ≦ S <-> R ⊔ S ≡ S.
Proof.
  compute; intuition eauto. firstorder.
Qed.

(** A relation is irreflexive if it doesn't relate any element to itself *)

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

(** If two relations are irreflexive, their union is irreflexive *)

Lemma irreflexive_union {A:Type} (r1 r2: rlt A):
  irreflexive r1 ->
  irreflexive r2 ->
  irreflexive (r1 ⊔ r2).
Proof.
  intros Hirr1 Hirr2.
  unfold irreflexive in *.
  rewrite capcup'. rewrite Hirr1, Hirr2. kat.
Qed.

(** The full-set considered as a KAT test is equal to the identity relation *)

Lemma fullset_one {A:Type}:
  [Full_set A : prop_set A] = 1.
Proof.
  apply ext_rel, antisym.
  - intros x y [Heq Hr]. auto.
  - intros x y Heq. split.
    auto. apply Full_intro.
Qed.

(** Testing if an element belongs to the intersection of two sets is equivalent
to testing if it belongs to the first set, and then testing if it belongs to
the second test *)

Lemma I_inter {A:Type} (e1 e2: Ensemble A):
  [I (Intersection _ e1 e2)] = [I e1]⋅[I e2].
Proof.
  apply ext_rel, antisym; intros x y H.
  - destruct H as [Heq Ht]. unfold I in Ht.
    apply in_intersection in Ht as [Ht1 Ht2].
    rewrite <-Heq. exists x; split; unfold I; auto.
  - destruct H as [z [Heq1 Ht1] [Heq2 Ht2]].
    rewrite Heq1 in Ht1. rewrite Heq1, <-Heq2.
    split; auto. split; auto.
Qed.

(** Sequencing with [1] has no effect *)

Lemma dot_one {A:Type} (r: rlt A):
  r⋅1 = r.
Proof.
  apply ext_rel. rewrite dotx1. auto.
Qed.

(** The converse of the sequence of two relations, is the sequence of the
converse of the second relation and of the converse of the first relation *)

Lemma dot_cnv {A:Type} (r1 r2: rlt A):
  (r1⋅r2)° = r2°⋅r1°.
Proof.
  apply ext_rel.
  rewrite cnvdot.
  auto.
Qed.

(** A relation relating [x] to [y], is equal to the converse of the relation 
relating [y] to [x] *)

Lemma cnv_rev {A:Type} (r: rlt A) (x y: A):
  r x y <-> r° y x.
Proof.
  simpl. unfold prop_hrel_cnv. intuition auto.
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

(** The intersection of the subsets of two sets is included in the intersection
of these two sets *)

Lemma capincl {A:Type} (r1 r2 r3 r4: rlt A):
  r1 ≦ r2 ->
  r3 ≦ r4 ->
  r1 ⊓ r3 ≦ r2 ⊓ r4.
Proof.
  intros H1 H2. rewrite H1, H2. auto.
Qed.

(** The union of a set and of one of its subsets is equal to the set *)

Lemma incl_as_eq {A:Type} (r s: rlt A):
  r ≦ s -> r ⊔ s = s.
Proof.
  intros Hincl. apply ext_rel, antisym. 
  - rewrite Hincl. kat.
  - kat.
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

(** Lemma to rebuild a sequence from hypothesis *)

Lemma cmp_seq {A:Type} {x y z: A} {r1 r2: rlt A}:
  r1 x y ->
  r2 y z ->
  (r1⋅r2) x z.
Proof.
  intuition (exists y; auto).
Qed.

Lemma cmp_minus {A:Type} {x y: A} {r1 r2: rlt A}:
  r1 x y ->
  !r2 x y ->
  (r1 \ r2) x y.
Proof.
  intuition (split; auto).
Qed.

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

(** The union of relations is commutative and associative *)

Lemma union_comm {A:Type} (r1 r2 : rlt A):
  (r1 ⊔ r2) = (r2 ⊔ r1).
Proof.
  apply ext_rel. kat.
Qed.

Lemma union_assoc {A:Type} (r1 r2 r3 : rlt A):
  (r1 ⊔ (r2 ⊔ r3)) = ((r1 ⊔ r2) ⊔ r3).
Proof.
  apply ext_rel. kat.
Qed.

Lemma union_comm_assoc {A:Type} (r1 r2 r3: rlt A):
  (r1 ⊔ r2 ⊔ r3) = (r1 ⊔ r3 ⊔ r2).
Proof. kat_eq. Qed.

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
reflexive transitive closure of the relation and of the relation *)

Lemma tc_inv_dcmp {A:Type} (r: rlt A):
  r^+ = r^* ⋅ r.
Proof. apply ext_rel; kat. Qed.

(** The transitive closure of a relation is equal to the sequence of the 
relation and of the reflexive transitive closure of the relation *)

Lemma tc_inv_dcmp2 {A:Type} (r: rlt A):
  r^+ = r ⋅ r^*.
Proof. apply ext_rel; kat. Qed.

(** The transitive closure of a relation is either itself or the sequence of
itself with its transitive closure *)

Lemma tc_inv_dcmp3 {A:Type} (r: rlt A):
  r^+ = r ⊔ (r ⋅ r^+).
Proof. kat_eq. Qed.

(** The transitive closure of a relation is either itself or the sequence of
its transitive closure with itself *)

Lemma tc_inv_dcmp4 {A:Type} (r: rlt A):
  r^+ = r ⊔ (r^+ ⋅ r).
Proof. kat_eq. Qed.

(** The transitive closure of a relation is either itself or the sequence of
its reflexive transitive closure with itself *)

Lemma tc_inv_dcmp5 {A:Type} (r: rlt A):
  r^+ = r ⊔ (r^* ⋅ r).
Proof. kat_eq. Qed.

Lemma tc_inv_dcmp6 {A:Type} (r: rlt A):
  r⋅r^+ ≦ r^+.
Proof. kat. Qed.

Lemma tc_inv_dcmp7 {A:Type} (r: rlt A):
  r^+⋅r ≦ r^+.
Proof. kat. Qed.

Lemma tc_inv_dcmp8 {A:Type} (r: rlt A):
  r^+⋅r^+ ≦ r^+.
Proof. kat. Qed.

(** The sequence of the reflexive transitive closure of a relation with the
reflexie transitive closure of the same relation is included in the reflexive
transitive closure of this relation *)

Lemma rtc_inv_dcmp {A:Type} (r: rlt A):
  r^* ⋅ r^* ≦ r^*.
Proof. kat. Qed.

(** The sequence of relation with its reflexive transitive closure is included
in the reflexive transitive closure of this relation *)

Lemma rtc_inv_dcmp2 {A:Type} (r: rlt A):
  r ⋅ r^* ≦ r^*.
Proof. kat. Qed.

(** The sequence of the reflexive transitive closure of a relation with itself
is included in the reflexive transitive closure of this relation *)

Lemma rtc_inv_dcmp3 {A:Type} (r: rlt A):
  r^* ⋅ r ≦ r^*.
Proof. kat. Qed.

(** The sequence of the reflexive transitive closure of a relation and of the
transitive closure of the same relation is included in the reflexive
transitive closure of this relation *)

Lemma rtc_inv_dcmp4 {A:Type} (r: rlt A):
  r^* ⋅ r^+ ≦ r^*.
Proof. kat. Qed.

(** The sequence of the transitive closure of a relation and of the reflexive
transitive closure of the same relation is included in the reflexive
transitive closure of this relation *)

Lemma rtc_inv_dcmp5 {A:Type} (r: rlt A):
  r^+ ⋅ r^* ≦ r^*.
Proof. kat. Qed.

(** The reflexive transitive closure is equal to the union of the identity
relation with the transitive closure of this relation *)

Lemma rtc_inv_dcmp6 {A:Type} (r: rlt A):
  r^* = 1 ⊔ r^+.
Proof. kat_eq. Qed.

Lemma rtc_inv_dcmp7 {A:Type} (r: rlt A):
  r^+ = r⋅r^*.
Proof. kat_eq. Qed.

Lemma rtc_inv_dcmp8 {A:Type} (r: rlt A):
  r^+ = r^*⋅r.
Proof. kat_eq. Qed.

(** The transitive closure of a relation is included in the reflexive transitive
closure of this relation *)

Lemma tc_incl_rtc {A:Type} (r: rlt A):
  r^+ ≦ r^*.
Proof. kat. Qed.

(** The transitive closure of a relation is included in the transitive closure
of this relation with another relation *)

Lemma tc_union_left {A:Type} (r1 r2: rlt A):
  r1^+ ≦ (r1 ⊔ r2)^+.
Proof. kat. Qed.

Lemma tc_union_right {A:Type} (r1 r2: rlt A):
  r2^+ ≦ (r1 ⊔ r2)^+.
Proof. kat. Qed.

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

(** The reflexive transitive closure is the union of the reflexive closure and
of the transitive closure *)

Lemma refl_trans_refl_union_trans {A:Type} (r: rlt A):
  r^* = 1 ⊔ r^+.
Proof. kat_eq. Qed.

(** A relation included in an irreflexive relation is irreflexive *)

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
intros H. rewrite H. auto.
Qed.

Lemma tc_incl_2 {A:Type} (r1 r2: rlt A):
  r1 ≦ r2^+ -> r1^+ ≦ r2^+.
Proof.
  intros H. rewrite H. kat.
Qed.

Lemma incl_unionincl_rtc {A:Type} (r1 r2: rlt A):
  r1 ≦ r2 ->
  (r1 ⊔ r2)^* ≦ r2^*.
Proof.
  intros Hincl. eapply rtc_incl. 
  rewrite Hincl. kat.
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
  apply H2, H1.
Qed.

Lemma incl_not_rel_thm {A:Type} {r r': rlt A} {x y: A}:
  ~(r' x y) ->
  r ≦ r' ->
  ~(r x y).
Proof.
  intros H Hincl Hnot.
  apply H, Hincl, Hnot.
Qed.

Lemma not_rel_tc {A:Type} {r: rlt A} {x y: A}:
  (forall s, ~(r x s)) ->
  ~(r^+ x y).
Proof.
  intros H Hnot. rewrite tc_inv_dcmp2 in Hnot.
  destruct Hnot as [z Hnot _].
  eapply H. eauto.
Qed.

Ltac incl_rel_kat H := apply (incl_rel_thm H); kat.

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
  ~(acyclic r) <->
  (cyclic r).
Proof.
  split.
  - intros H.
    unfold acyclic in H; unfold acyclic.
    byabsurd. destruct H. intros x H.
    apply Hcontr. exists x. auto.
  - intros Hcyc Hnot.
    destruct Hcyc as [x Hcyc].
    destruct (Hnot x).
    auto.
Qed.

(** A relation that is not cyclic is acyclic *)

Lemma not_cyclic_is_acyclic {A:Type} (r: rlt A):
  ~(cyclic r) <->
  (acyclic r).
Proof.
  split.
  - intros Hnot x Hrel.
    apply Hnot. exists x; auto.
  - intros Hac Hcyc. destruct Hcyc as [z Hcyc].
    destruct (Hac z). auto.
Qed.

(** If a relation is included in an acyclic relation, it is also acyclic *)

Lemma ac_incl {A : Type}  (r1 r2 : rlt A) :
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

(** If there is a cycle in a relation, we can extend this relation and keep the
cycle *)

Lemma cycle_ext {A:Type} (r1 r2: rlt A) (x: A):
  r1^+ x x ->
  (r1 ⊔ r2)^+ x x.
Proof.
  intros Hrel. incl_rel_kat Hrel.
Qed.
(* (*
(** If there is a path in the sequence of : *) *)

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
  intros Hac1 Hac2 Hcyc.
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

(** If a relation is acyclic, but there is a cycle in the union of this relation
with a second relation, there is an element in this cycle that is in the domain
or the range of the second relation *)

Lemma added_cycle_pass_through_addition1 {A:Type} (x:A) (r1 r2 : rlt A) :
  acyclic r1 ->
  (r1 ⊔ r2)^+ x x ->
  exists y, ( r2^+ ⋅ (r1 ⊔ r2)^* ) y y.
Proof.
  intros Hac1 Hcyc.
  rewrite tc_union_decomposition in Hcyc.
  destruct_disjunction Hcyc.
  - destruct (Hac1 x Hcyc).
  - exists x, x. auto.
    apply one_incl_rtc. split; auto.
  - destruct Hcyc as [z1 [z2 [z3 [z4 ? ?] ?] ?] ?].
    exists z3, z2. { auto. }
    apply rtc_inv_dcmp2. exists z1. { left. auto. }
    apply rtc_inv_dcmp. exists x. { auto. }
    apply rtc_inv_dcmp3. exists z4. { auto. }
    left. auto.
  - destruct Hcyc as [z ? ?].
    exists z, x. auto. apply rtc_incl_itself. left. auto.
  - destruct Hcyc as [z1 [z2 ? ?] ?].
    exists z1, x. { auto. }
    apply rtc_inv_dcmp3. exists z2.
    { apply tc_incl_rtc, tc_union_right. auto. }
    left. auto.
  - destruct Hcyc as [z ? ?].
    exists x, z. auto. apply rtc_incl_itself. left. auto.
  - destruct Hcyc as [z Hbeg Hend].
    exists z, x. { auto. }
    apply (incl_rel_thm Hbeg). kat.
  - destruct Hcyc as [z Hbeg Hend].
    exists z, x. { auto. }
    apply (incl_rel_thm Hbeg). kat.
  - rewrite 2seq_assoc in Hcyc.
    destruct Hcyc as [z Hbeg Hend].
    exists x, z. { auto. }
    apply (incl_rel_thm Hend). kat.
Qed.

Lemma add_cycle_pass_through_addition2 {A:Type} (x:A) (r1 r2: rlt A):
  r2^+ ⋅ (r1 ⊔ r2)^* ≦ (r1 ⊔ r2)^+.
Proof. kat. Qed.

Lemma add_cycle_pass_through_addition {A:Type} (x: A) (r1 r2: rlt A):
  acyclic r1 ->
  (r1 ⊔ r2)^+ x x ->
  exists y, (In _ (udr r2) y) /\ (r1 ⊔ r2)^+ y y.
Proof.
  intros Hac Hcyc.
  destruct (added_cycle_pass_through_addition1 _ _ _ Hac Hcyc) as [z H].
  exists z; split.
  - left. destruct H as [z' H _]. rewrite tc_inv_dcmp2 in H.
    destruct H as [z'' H _]. exists z''. auto.
  - apply add_cycle_pass_through_addition2; auto.
Qed.

(** If there a relation relates two elements with an immediate link, it relates
them *)

Lemma imm_rel_implies_rel {A:Type} (r:rlt A) (x y: A):
  (imm r) x y ->
  r x y.
Proof.
  intros [Hr _]. auto.
Qed.

Lemma imm_rel_incl_rel {A:Type} (r:rlt A):
  (imm r) ≦ r.
Proof.
  intros x y H. apply imm_rel_implies_rel. auto.
Qed.

(** The transitive closure of a transitive relation is equal to itself *)

Lemma tc_trans_itself {A:Type} (r: rlt A):
  (r⋅r) ≦ r ->
  r^+ = r.
Proof.
  intros Htrans. apply ext_rel, antisym; [|kat].
  apply itr_ind_l1; auto.
Qed.

(** A partial order is acyclic *)

Lemma part_order_ac {A:Type} (s:Ensemble A) (r : rlt A):
  partial_order r s ->
  acyclic r.
Proof.
  intros [_ [Htrans Hirr]] x Hcyc.
  rewrite (tc_trans_itself _ Htrans) in Hcyc.
  intuition eauto.
Qed.

(** A strict linear order is acyclic *)

Lemma lin_strict_ac {A:Type} (s:Ensemble A) (r : rlt A):
  linear_strict_order r s ->
  acyclic r.
Proof.
  intros [Hpo _]. eapply part_order_ac; eauto.
Qed.

(** If a relation is acyclic, its transitive closure is acyclic *)

Lemma tc_ac_is_ac {A:Type} (r: rlt A):
  acyclic r ->
  acyclic (r^+).
Proof.
  unfold acyclic. rewrite tc_of_tc_is_tc.
  auto.
Qed.

(** ** Facts and tactics about the tests of KATs *)

(** The following tactic and lemmas decompose goals or hypotheses consisting
of the composition of relations and tests relating two elements *)

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

Lemma simpl_trt_tleft {A:Type} (t1 t2: prop_set A) (r: rlt A) (x y: A):
  ([t1] ⋅ r ⋅ [t2]) x y -> t1 x.
Proof.
  intros H. apply simpl_trt_hyp in H as [H _]. auto.
Qed.

Lemma simpl_trt_rel {A:Type} (t1 t2: prop_set A) (r: rlt A) (x y: A):
  ([t1] ⋅ r ⋅ [t2]) x y -> r x y.
Proof.
  intros H. apply simpl_trt_hyp in H as [_ [H _]]. auto.
Qed.

Lemma simpl_trt_tright {A:Type} (t1 t2: prop_set A) (r: rlt A) (x y: A):
  ([t1] ⋅ r ⋅ [t2]) x y -> t2 y.
Proof.
  intros H. apply simpl_trt_hyp in H as [_ [_ H]]. auto.
Qed.

Lemma simpl_tr_rel_aux {A:Type} (t: prop_set A) (r: rlt A):
  [t]⋅r ≦ r.
Proof.
  intros x y H.
  destruct H as [w [Heq _] H]. rewrite <-Heq in H. auto.
Qed.

Ltac simpl_tr_rel H :=
  repeat (rewrite seq_assoc in H);
  apply simpl_tr_rel_aux in H;
  repeat (rewrite <-seq_assoc in H).

Lemma simpl_rt_rel_aux {A:Type} (t: prop_set A) (r: rlt A):
  r⋅[t] ≦ r.
Proof.
  intros x y H.
  destruct H as [w H [Heq _]]. rewrite Heq in H. auto.
Qed.

Ltac simpl_rt_rel H := apply simpl_rt_rel_aux in H.

Lemma simpl_rt_hyp {A:Type} (t: prop_set A) (r: rlt A) (x y: A):
  (r ⋅ [t]) x y ->
  r x y /\ t y.
Proof. intros [z Hr [Heq Ht]]. rewrite Heq in Ht, Hr. intuition. Qed.

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

Lemma add_test_left {A:Type} (t: prop_set A) (r: rlt A) (x y: A):
  r x y ->
  t x ->
  ([t] ⋅ r) x y.
Proof.
  intros Hr Ht.
  exists x; auto. split; auto.
Qed.

Lemma add_test_right {A:Type} (t: prop_set A) (r: rlt A) (x y: A):
  r x y ->
  t y ->
  (r ⋅ [t]) x y.
Proof.
  intros Hr Ht.
  exists y. auto. split; auto.
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

End KatTests.

Lemma test_i_union {A:Type} (s1 s2: Ensemble A):
  [I (Union _ s1 s2)] = [I s1] ⊔ [I s2].
Proof.
  apply ext_rel, antisym.
  - intros x y [Heq H].
    apply in_union in H as [H|H];[left|right]; 
    split; auto.
  - intros x y [[H Heq]|[H Heq]]; 
    split; auto;
    [left|right]; auto.
Qed.

(** The transitive closure of a relation framed by two tests is included in the
framing of the transitive closure of the relation by the two tests *)

Lemma tc_test_restriction {A:Type} (t1 t2: prop_set A) (r: rlt A):
  ([t1]⋅r⋅[t2])^+ ≦ [t1]⋅r^+⋅[t2].
Proof. kat. Qed.

(** If the transitive closure of a relation doesn't relate any of the elements
that verifies a given test, the framing of the relation by the test is acyclic *)
Lemma ac_test_restriction {A:Type} (t: prop_set A) (r: rlt A):
  (forall x, t x -> ~(r^+ x x)) ->
  acyclic ([t]⋅r⋅[t]).
Proof.
  intros H x Hnot.
  apply tc_test_restriction in Hnot.
  apply simpl_trt_hyp in Hnot as [Ht [Hr _]].
  eapply H; eauto.
Qed.

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

(** A test is included in the sequence of two tests if it is included in both
tests *)

Lemma incl_dot_test {A:Type} (t t1 t2: prop_set A):
  [t] ≦ [t1] ->
  [t] ≦ [t2] ->
  [t] ≦ [t1]⋅[t2].
Proof.
  intros H1 H2. intros x y H. 
  apply H1 in H as H1'.
  apply H2 in H as H2'.
  exists x; auto.
  split; auto.
  destruct H1'. congruence.
Qed.


(** The reflexive transitive closure defined as a positive or null number of 
sequence of a relation with itself is equivalent to its inductive definition,
i.e. the reflexive transitive closure of a relation is either the relation 
itself, the identity relation, or the sequence of the reflexive transitive
closure of the relation with the transitive reflexive closure of the relation.

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

(** We can also use the alternative definitions of the coq standard library *)

Lemma clos_refl_trans_clos_refl_trans_1n {A:Type} (r: rlt A):
  (clos_refl_trans _ r) = (clos_refl_trans_1n _ r).
Proof.
  apply ext_rel, antisym;
  intros x y H;
  apply clos_rt_rt1n_iff in H; auto.
Qed.

Lemma rtc_clos_refl_trans_1n {A:Type} (r: rlt A):
  r^* = (clos_refl_trans_1n _ r).
Proof.
  rewrite rtc_clos_refl_trans, clos_refl_trans_clos_refl_trans_1n. auto.
Qed.

Lemma clos_refl_trans_clos_refl_trans_n1 {A:Type} (r: rlt A):
  (clos_refl_trans _ r) = (clos_refl_trans_n1 _ r).
Proof.
  apply ext_rel, antisym;
  intros x y H;
  apply clos_rt_rtn1_iff in H; auto.
Qed.

Lemma rtc_clos_refl_trans_n1 {A:Type} (r: rlt A):
  r^* = (clos_refl_trans_n1 _ r).
Proof.
  rewrite rtc_clos_refl_trans, clos_refl_trans_clos_refl_trans_n1. auto.
Qed.

(** The transitive closure defined as a positive and non-null number of 
sequence of a relation with itself is equivalent to its inductive definition,
i.e. the transitive closure of a relation is either the relation itself, or the
sequence of the transitive closure of the relation with the transitive closure 
of the relation.

This means that the definitions of transitive closure of Relation Algebra and of
the standard library of coq are equivalent *)

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

(** We can also use the alternative definitions of the coq standard library *)

Lemma clos_trans_clos_trans_1n {A:Type} (r: rlt A):
  (clos_trans _ r) = (clos_trans_1n _ r).
Proof.
  apply ext_rel, antisym; intros x y H;
  apply clos_trans_t1n_iff in H; auto.
Qed.

Lemma tc_clos_trans_1n {A:Type} (r: rlt A):
  r^+ = (clos_trans_1n _ r).
Proof.
  rewrite tc_clos_trans, clos_trans_clos_trans_1n. auto.
Qed.

Lemma clos_trans_clos_trans_n1 {A:Type} (r: rlt A):
  (clos_trans _ r) = (clos_trans_n1 _ r).
Proof.
  apply ext_rel, antisym; intros x y H;
  apply clos_trans_tn1_iff in H; auto.
Qed.

Lemma tc_clos_trans_n1 {A:Type} (r: rlt A):
  r^+ = (clos_trans_n1 _ r).
Proof.
  rewrite tc_clos_trans, clos_trans_clos_trans_n1. auto.
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

(** We can do an induction on the transitive closure as defined in
RelationAlgebra the same way we would do on a transitive closure as
defined in the standard library of coq *)

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

Lemma tc_ind_right_aux:
  forall (A: Type) (R: rlt A) (x: A) (P: A -> A -> Prop),
  (forall y: A, R x y -> P x y) ->
  (forall y z: A, R y z -> R^+ x y -> P x y -> P x z) ->
  forall a: A, R^+ x a -> P x a.
Proof.
  intros A R x P.
  rewrite tc_clos_trans_n1.
  apply clos_trans_n1_ind.
Qed.

Lemma tc_ind_right:
  forall (A: Type) (R: rlt A) (P: A -> A -> Prop),
  (forall x y: A, R x y -> P x y) ->
  (forall x y z: A, R y z -> R^+ x y -> P x y -> P x z) ->
  forall x a: A, R^+ x a -> P x a.
Proof.
  intros A R P Hbase Hind x a Hrel.
  apply (tc_ind_right_aux _ R); auto.
  intros y z Hyz Hxy Hpxy. eapply Hind; eauto.
Qed.

(** If there is not path between two elements in a relation, there is no third
element such that there is a path between the first and third elements, and a
path between the third and second element in the same relation *)

Lemma no_path_impl_no_step {A:Type} (r: rlt A) (x y: A):
  ~(r^+ x y) ->
  (forall z, ~(r^+ x z /\ r^+ z y)).
Proof.
  intros Hnot z [H1 H2].
  apply Hnot.
  apply tc_trans with z; auto.
Qed.

(** If there is no path between two elements in a first relation, but there is
a path between these two elements in the union of a first relation with a second
relation, this path must pass through two elements that are related by the
second relation and not by the first one *)

Lemma path_impl_pass_through_aux {A:Type} (r1 r2: rlt A):
  forall x y,
  (r1 ⊔ r2)^+ x y ->
  (fun w1 w2 => ~(r1^+ w1 w2) ->
                ((r1 ⊔ r2)^* ⋅ (r2 \ r1) ⋅ (r1 ⊔ r2)^* ) w1 w2 ) x y.
Proof.
  apply tc_ind.
  - intros x y [Hr1 | Hr2] Hnot.
    + destruct Hnot. apply tc_incl_itself. auto.
    + destruct (classic (r1 x y)).
      * destruct Hnot. apply tc_incl_itself. auto.
      * exists y. exists x.
        all: try (apply one_incl_rtc; intuition).
        split; auto.
  - intros x y z Hr1 IH1 Hr2 IH2 Hnot.
    pose proof ((no_path_impl_no_step _ _ _ Hnot) y) as H.
    apply not_and_or in H as [H|H].
    + apply IH1 in H. destruct H as [z1 H1 H2].
      exists z1. { auto. }
      apply rtc_inv_dcmp4.
      exists y; auto.
    + apply IH2 in H. rewrite seq_assoc in H.
      destruct H as [z1 H1 H2].
      rewrite seq_assoc. exists z1; auto.
      apply rtc_inv_dcmp5. exists y; auto.
Qed.

Lemma path_impl_pass_through {A:Type} (r1 r2: rlt A) (x y: A):
  ~(r1^+ x y) ->
  (r1 ⊔ r2)^+ x y ->
  ((r1 ⊔ r2)^* ⋅ (r2 \ r1) ⋅ (r1 ⊔ r2)^*) x y.
Proof.
  intros Hnot Hpath.
  apply path_impl_pass_through_aux; auto.
Qed.

(** If a first relation is acyclic and there is a cycle in the union of the
first relation with a second relation, the cycle must passe through two elements
that are related by the second relation and not by the first one *)

Lemma added_cycle_pass_through_addition {A:Type} (r1 r2: rlt A) (x: A):
  acyclic r1 ->
  (r1 ⊔ r2)^+ x x ->
  ((r1 ⊔ r2)^* ⋅ (r2 \ r1) ⋅ (r1 ⊔ r2)^*) x x.
Proof.
  intros Hac Hcyc.
  apply (path_impl_pass_through _ _ _ _ (Hac x) Hcyc).
Qed.
  
(** The union of two relations is equivalent to the union of the first relation
with the second relation minus the first one *)

Lemma union_dcmp {A:Type} (r1 r2: rlt A):
  (r1 ⊔ r2) = (r1 ⊔ (r2 \ r1)).
Proof.
  apply ext_rel, antisym; intros x y [H|H].
  - left; auto.
  - destruct (classic (r1 x y)).
    + left; auto.
    + right; split; auto.
  - left; auto.
  - destruct H as [H2 _].
    right; auto.
Qed.

(** A relation [A] minus another relation is included in [A] *)

Lemma minus_incl {A:Type} (r1 r2: rlt A):
  (r2 \ r1) ≦ r2.
Proof.
  intros x y [H _].
  auto.
Qed.

(** The transitive closure of the union of two relations is equal to the union
of the transitive closure of the first relation and of the sequence of:

- the reflexive transitive closure of the first relation
- the second relation minus the first one
- the reflexive transitive closure of the union of the two relations
*)

Lemma tc_union_dcmp {A:Type} (r1 r2: rlt A):
  (r1 ⊔ r2)^+ = r1^+ ⊔ (r1^* ⋅ (r2 \ r1) ⋅ (r1 ⊔ r2)^*).
Proof.
  apply ext_rel, antisym.
  - intros x y H.
    generalize dependent y.
    generalize dependent x.
    apply tc_ind.
    + intros x y H. rewrite union_dcmp in H.
      destruct H as [H|H].
      * left. apply tc_incl_itself. auto.
      * eapply (incl_rel_thm H). kat.
    + intros x y z H1 IH1 H2 IH2.
      destruct IH1 as [IH1|IH1];
      destruct IH2 as [IH2|IH2].
      * left. apply tc_trans with y; auto.
      * destruct IH2 as [w1 [w2 Hr1 Hr2] Hr3].
        right. exists w1;[|auto]. exists w2; auto.
        apply rtc_trans. exists y; auto.
        apply (incl_rel_thm IH1). kat.
      * destruct IH1 as [w1 [w2 Hr1 Hr2] Hr3].
        right. exists w1. exists w2; auto.
        apply rtc_trans. exists y; auto.
        apply (incl_rel_thm IH2). kat.
      * destruct IH1 as [w1 [w2 Hr1 Hr2] Hr3].
        right. exists w1. exists w2; auto.
        apply rtc_trans. exists y; auto.
        apply (incl_rel_thm H2). kat.
  - rewrite (minus_incl r1 r2). kat.
Qed.

Lemma shift_cyc_thm {A:Type} (r1 r2: rlt A):
  (exists x, (r1⋅r2) x x) ->
  exists x, (r2⋅r1) x x.
Proof.
  intros [x [y H1 H2]].
  exists y. exists x; auto.
Qed.

Ltac shift_cyc H :=
  apply shift_cyc_thm in H;
  repeat (rewrite <-seq_assoc in H).

Lemma exists_cyc {A:Type} (r: rlt A) (x: A):
  r x x ->
  exists x, r x x.
Proof. intros H. exists x. auto. Qed.

Lemma cycle_of_u_ac2 {A:Type} (r1 r2: rlt A): 
  cyclic (r1 ⊔ r2) ->
  cyclic r2 \/
  exists w, (r1⋅(r1 ⊔ r2)^+) w w.
Proof.
  intros Hcyc.
  unfold cyclic in Hcyc.
  rewrite tc_union_decomposition in Hcyc.
  destruct Hcyc as [w Hcyc].
  destruct_disjunction Hcyc.
  - right. rewrite tc_inv_dcmp2 in Hcyc.
    rewrite rtc_inv_dcmp6 in Hcyc.
    exists w. destruct Hcyc as [z Hbeg Hend].
    exists z. auto.
    destruct Hend as [Hend|Hend].
    + simpl in Hend. rewrite Hend in Hbeg.
      rewrite Hend. incl_rel_kat Hbeg.
    + incl_rel_kat Hend.
  - left. exists w. auto.
  - apply exists_cyc in Hcyc.
    do 2 (shift_cyc Hcyc).
    destruct Hcyc as [x Hcyc].
    right. exists x. incl_rel_kat Hcyc.
  - right. exists w. incl_rel_kat Hcyc.
  - apply exists_cyc in Hcyc.
    do 2 (shift_cyc Hcyc).
    destruct Hcyc as [x Hcyc].
    right. exists x. incl_rel_kat Hcyc.
  - apply exists_cyc in Hcyc.
    shift_cyc Hcyc.
    destruct Hcyc as [x Hcyc].
    right. exists x. incl_rel_kat Hcyc.
  - right. exists w. incl_rel_kat Hcyc.
  - apply exists_cyc in Hcyc.
    do 2 (shift_cyc Hcyc).
    destruct Hcyc as [x Hcyc].
    right. exists x. incl_rel_kat Hcyc.
  - apply exists_cyc in Hcyc.
    do 3 (shift_cyc Hcyc).
    destruct Hcyc as [x Hcyc].
    right. exists x. incl_rel_kat Hcyc.
Qed.

Lemma itr_cup {A} (r s : rlt A) :
  (r ⊔ s)^+ ≡ r^+ ⊔ s^+
         ⊔ s^+⋅r^+
         ⊔ (r^+⋅s^+)^+
         ⊔ s^+⋅(r^+⋅s^+)^+⋅r^+
         ⊔ (r^+⋅s^+)^+⋅r^+
         ⊔ s^+⋅(r^+⋅s^+)^+.
Proof.
  ka.
Qed.

Lemma tc_of_dot_dcmp {A:Type} (r1 r2: rlt A):
  (r1⋅r2)^+ = r1⋅(r2⋅r1)^*⋅r2.
Proof.
  kat_eq.
Qed.

Lemma add_dom {A:Type} (r: rlt A):
  r = [I (dom r)]⋅r.
Proof.
  apply ext_rel, antisym; try kat.
  intros x y H.
  exists x.
  - split; auto. exists y; auto.
  - auto.
Qed.

Lemma add_dom_tc {A:Type} (r: rlt A):
  r^+ = [I (dom r)]⋅r^+.
Proof.
  rewrite tc_inv_dcmp2. rewrite (add_dom r) at 1. kat_eq.
Qed.

Lemma add_ran {A:Type} (r: rlt A):
  r = r⋅[I (ran r)].
Proof.
  apply ext_rel, antisym; try kat.
  intros x y H.
  exists y.
  - auto.
  - split; auto. exists x; auto.
Qed.

Lemma add_ran_tc {A:Type} (r: rlt A):
  r^+ = r^+⋅[I (ran r)].
Proof.
  rewrite tc_inv_dcmp. rewrite (add_ran r) at 2. kat_eq.
Qed.

Lemma range_domain_cup {A} (r s : rlt A) :
  [I (ran r)] ⋅ (r ⊔ s)^+ ⋅ [I (dom r)] =
  [I (ran r)] ⋅ (r ⊔ [I (ran r)] ⋅ s^+ ⋅ [I (dom r)])^+ ⋅ [I (dom r)].
Proof.
  apply ext_rel.
  apply antisym; (try kat).
  intros x y [z1 [z2 Hran Hrel] Hdom].
  inversion Hran as [Heqr _].
  inversion Hdom as [Heqd _].
  rewrite <-Heqr in Hran, Hrel.
  rewrite Heqd in Hdom, Hrel. clear Heqr. clear Heqd.
  apply itr_cup in Hrel.
  destruct_disjunction Hrel.
  - exists y; auto.
    exists x; auto.
    incl_rel_kat Hrel.
  - exists y; auto.
    exists x; auto.
    assert (([I (ran r)]⋅s^+⋅[I (dom r)]) x y) as H'.
    { exists y; auto. exists x; auto. }
    incl_rel_kat H'.
  - exists y; auto.
    exists x; auto.
    destruct Hrel as [z H1 H2].
    apply tc_trans with z.
    + apply tc_incl_itself.
      assert (([I (ran r)]⋅s^+⋅[I (dom r)]) x z) as H'.
      { exists z. exists x; auto.
        rewrite tc_inv_dcmp2 in H2. destruct H2 as [z3 H2 _].
        split; auto. exists z3; auto. }
      incl_rel_kat H'.
    + incl_rel_kat H2.
  - exists y; auto.
    exists x; auto.
    assert (([I (ran r)]⋅(r^+⋅s^+)^+⋅[I (dom r)]) x y) as Hrel'.
    { exists y; auto. exists x; auto. }
    rewrite tc_of_dot_dcmp in Hrel'.
    rewrite (add_ran_tc r) in Hrel'.
    rewrite (add_dom_tc r) in Hrel'.
    incl_rel_kat Hrel'.
  - exists y; auto.
    exists x; auto.
    assert (([I (ran r)]⋅(s^+⋅(r^+⋅s^+)^+⋅r^+)⋅[I (dom r)]) x y) as Hrel'.
    { exists y; auto. exists x; auto. }
    rewrite tc_of_dot_dcmp in Hrel'.
    rewrite (add_ran_tc r) in Hrel'.
    rewrite (add_dom_tc r) in Hrel'.
    incl_rel_kat Hrel'.
  - exists y; auto.
    exists x; auto.
    assert (([I (ran r)]⋅((r^+⋅s^+)^+⋅r^+)⋅[I (dom r)]) x y) as Hrel'.
    { exists y; auto. exists x; auto. }
    rewrite tc_of_dot_dcmp in Hrel'.
    rewrite (add_ran_tc r) in Hrel'.
    rewrite (add_dom_tc r) in Hrel'.
    incl_rel_kat Hrel'.
  - exists y; auto.
    exists x; auto.
    assert (([I (ran r)]⋅(s^+⋅(r^+⋅s^+)^+)⋅[I (dom r)]) x y) as Hrel'.
    { exists y; auto. exists x; auto. }
    rewrite tc_of_dot_dcmp in Hrel'.
    rewrite (add_ran_tc r) in Hrel'.
    rewrite (add_dom_tc r) in Hrel'.
    incl_rel_kat Hrel'.
Qed.

Lemma cycle_of_u_ac3 {A:Type} (r1 r2: rlt A):
  (forall w1 w2 w3 w4,
      r1^+ w1 w2 ->
      r2 w2 w3 ->
      r1^+ w3 w4 ->
      r1^+ w2 w3) <-> [I (ran r1)] ⋅ r2 ⋅ [I (dom r1)] ≦ r1^+.
Proof.
  split.
  - intros H b c [c' [b' [<- [a ab]] bc] [-> [d cd]]].
    eapply H; eauto; apply tc_incl_itself; eauto.
  - intros H a b c d ab bc cd. apply H.
    exists c. exists b; auto.
    + rewrite (add_ran_tc r1) in ab.
      destruct ab as [z _ [Heq Hran]].
      rewrite Heq in Hran. split; auto.
    + rewrite (add_dom_tc r1) in cd.
      destruct cd as [z [Heq Hdom] _].
      split; auto.
Qed.

Lemma cycle_of_u_ac_aux {A:Type} (r1 r2: rlt A):
  (forall w1 w2 w3 w4, 
                       r1^+ w1 w2 ->
                       r2^+ w2 w3 ->
                       r1^+ w3 w4 ->
                       r1^+ w2 w3) ->
  (forall w1 w2 w3 w4, 
                       r1^+ w1 w2 ->
                       (r1 ⊔ r2)^+ w2 w3 ->
                       r1^+ w3 w4 ->
                       r1^+ w2 w3).
Proof.
  intros Hclo.
  apply cycle_of_u_ac3 in Hclo.
  apply cycle_of_u_ac3.
  rewrite range_domain_cup.
  rewrite Hclo. kat.
Qed.

Lemma cycle_of_u_ac {A:Type} (r1 r2: rlt A):
  (forall w1 w2 w3 w4, r1^+ w1 w2 ->
                       r2^+ w2 w3 ->
                       r1^+ w3 w4 ->
                       r1^+ w2 w3) ->
  acyclic r2 ->
  cyclic (r1 ⊔ r2) ->
  cyclic r1.
Proof.
  intros Htrans Hac H.
  specialize (cycle_of_u_ac_aux _ _ Htrans).
  clear Htrans. intros Htrans.
  apply cycle_of_u_ac2 in H as Hcyc.
  destruct Hcyc as [Hcyc|[w1 [w2 Hbeg Hend]]].
  { destruct Hcyc as [x Hcyc]. destruct (Hac x). auto. }
  assert (r1^+ w2 w1) as Hend2.
  { eapply Htrans.
    - incl_rel_kat Hbeg.
    - auto.
    - incl_rel_kat Hbeg.
  }
  exists w1. apply tc_trans with w2.
  - incl_rel_kat Hbeg.
  - auto.
Qed.

(** The transitive closure of a transitive relation is itself *)

Lemma tc_of_trans {A:Type} (r: rlt A):
  r⋅r ≦ r ->
  r^+ = r.
Proof.
  intros H. apply ext_rel, antisym.
  - intros x y Htrans.
    generalize x, y, Htrans.
    apply tc_ind.
    + intros w z Hrel. auto.
    + intros w z v _ H2 _ H4.
      apply H. exists z; auto.
  - kat.
Qed.
  


(** The transitive closure of the union of two relations is the same as the
transitive closure of the union of the first relation and of the transitive
closure of the second relation *)

Lemma tc_of_union_is_tc_of_union_tc_right {A:Type} (r1 r2: rlt A):
  (r1 ⊔ r2)^+ = (r1 ⊔ r2^+)^+.
Proof.
  apply ext_rel, antisym; kat.
Qed.

(** When a first relation is included in a second relation, a cycle in the union
of the two relations is a cycle in the second relation *)

Lemma cycle_incl_union {A:Type} (r1 r2: rlt A) (x:A):
  r1 ≦ r2^+ ->
  (r1 ⊔ r2)^+ x x ->
  r2^+ x x.
Proof.
  intros Hincl Hrel.
  apply (incl_rel_thm Hrel).
  rewrite Hincl. kat.
Qed.

Lemma cyc_u_of_ac_implies_cyc_seq {A:Type} (r1 r2: rlt A) (x: A):
  acyclic r1 ->
  (r1⋅r1 ≦ r1) ->
  acyclic r2 ->
  (r1 ⊔ r2)^+ x x ->
  (exists y, (r1⋅r2^+)^+ y y).
Proof.
  intros Hac1 Hac2 Htrans2 Hcyc.
Admitted.


Lemma added_cycle_pass_through_addition2 {A:Type} (r1 r2: rlt A) (x: A):
  acyclic r1 ->
  (r1 ⊔ r2)^+ x x ->
  exists y, ((r2 \ r1) ⋅ (r1 ⊔ r2)^*) y y.
Proof.
  intros Hac Hcyc.
  pose proof (added_cycle_pass_through_addition _ _ _ Hac Hcyc) as H.
  destruct H as [z [y H1 H2] H3].
  exists y. exists z; auto.
  incl_rel_kat (cmp_seq H3 H1).
Qed.

Lemma le_trans {Elt:Type} (r: rlt Elt) (s: Ensemble Elt) (x y z: Elt):
  partial_order r s ->
  (LE r) x y ->
  (LE r) y z ->
  (LE r) x z.
Proof.
  intros Hpo H1 H2.
  destruct (OE _ _ Hpo) as [_ [[_ [Htrans _]] _]].
  eapply Htrans.
  incl_rel_kat (cmp_seq H1 H2).
Qed.
