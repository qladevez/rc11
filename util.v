(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Relations.
Require Import Ensembles.
Require Import Classical_Prop.
From ATBR Require Import ATBR Model_StdRelations.
Import Load.

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

(** ** Sets *)

Lemma intersection_included_itself {A:Type} (s1 s2 : Ensemble A):
  Included _ (Intersection _ s1 s2) s1.
Proof.
  intros x [H1 H2]; auto.
Qed.

(** ** Notations *)

Module RelNotations.

Infix " <+> " := (union _) (at level 49, right associativity).
Definition inter {A:Type} (r1 r2 : relation A) :=
  fun x => fun y => (r1 x y) /\
                    (r2 x y).
Infix " <*> " := inter (at level 50, left associativity).
Infix " ;; " := comp (at level 41, right associativity).
Infix " == " := (same_relation _) (at level 70).
Infix " ⊆ " := (inclusion _) (at level 75).
Notation "R ?" := (clos_refl _ R) (at level 15).
Notation "R **" := (clos_refl_trans _ R) (at level 25).
Definition t_clos {A} (R : relation A) := R ;; R**.
Notation "R ⁺" := (t_clos R) (at level 20).
Notation "R ^-1" := (transp _ R) (at level 14).

Definition id {A} := (@one (@rel_Graph A) rel_Monoid_Ops tt).
Definition empty {A} := (@zero (@rel_Graph A) rel_SemiLattice_Ops tt).

End RelNotations.

Import RelNotations.

(** ** Definitions *)

(** Axiom of extensionality for relations. If two relations relate the same 
elements, they are equal *)

Axiom ext_rel : forall (A:Type) (r1 r2 : relation A),
  (r1 == r2) -> r1 = r2.

(** The domain of a relation is the set of elements that are related to one or
more elements by the relation *)

Definition dom {A:Type} (r:relation A) : Ensemble A :=
  fun x => exists y, r x y.

(** The range (or codomain) of a relation is a set of elements such that one or
more elements are related to it by the relation *)

Definition ran {A:Type} (r:relation A) : Ensemble A :=
  fun y => exists x, r x y.

(** [udr r] is the union of the domain and range of the relation [r] *)

Definition udr {A:Type} (r: relation A) : Ensemble A :=
  Union _ (dom r) (ran r).

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

(** A relation is cyclic if its transitive closure is irreflexive *)

Definition acyclic {A:Type} (r: relation A) : Prop :=
  forall x, ~(r⁺ x x).

(** A relation is cyclic if its transitive closure is not irreflexive *)
Definition cyclic {A:Type} (r: relation A) : Prop :=
  exists x, r⁺ x x.

(** [res_eset e r] restricts a relation [r] to the subset of [r] relating
events of [e] *)

Definition res_eset {A:Type} (e: Ensemble A) (r: relation A) :=
  fun x => fun y => (In _ e x) /\
                    (In _ e y) /\
                    r x y.

(** A relation forms a partial order on a set of elements if:

- All the elements related by the relation belong to the set of elements
- The relation is transitive
- The relation is irreflexive *)

Definition partial_order {A:Type} (r:relation A) (xs:Ensemble A) : Prop :=
  Included _ (udr r) xs /\
  (forall x1 x2 x3, (r x1 x2) /\ (r x2 x3) -> (r x1 x3)) /\ (** Transitivity *)
  (forall x, ~(r x x)). (** Irreflexivity *)

(** A relation forms a linear strict order on a set of elements if:

- It is a partial order
- It is linear, which means that every pair of elements of the set must be
related by the relation in any direction *)

Definition linear_strict_order {A:Type} (r:relation A) (xs:Ensemble A) : Prop :=
  (partial_order r xs) /\
  (forall x1 x2, (x1 <> x2) -> (In _ xs x1) -> (In _ xs x2) ->
    (r x1 x2) \/ (r x2 x1)). (** Linearity *)

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
  r ⊆ (LE r) /\
  linear_strict_order (LE r) S.

(** The extension of a strict linear order is itself *)

Axiom le_lso : forall (s:Ensemble Elt) (r:relation Elt),
  linear_strict_order r s -> LE r = r.

End OrdExt.

(** ** Kleene tactic *)

(** We can use the [kleene_reflexivity] tactic provided by the 
#<a href="https://github.com/coq-community/atbr">ATBR</a># library to solve 
equations about relations. *)

(** The tactic doesn't handle inequations, but this lemmas allows us to rewrite
them as equations *)

Lemma inclusion_as_eq A (R S : relation A) : inclusion A R S <-> R <+> S == S.
Proof.
  compute; intuition eauto.
Qed.

(** Reflexive closures are not a part of kleene algebras, but we can rewrite 
them as a simple union *)

Lemma refl_as_union {A:Type} (r1 : relation A):
  r1 ? = r1 <+> id.
Proof.
  apply ext_rel. split; intros x y H.
  - induction H; [left | right; compute]; auto.
  - destruct H as [H|H].
    + apply r_step; auto.
    + compute in H; rewrite H; apply r_refl.
Qed.

(** The [kleene] tactic that prepares the goal before applying 
[kleene_reflexivity] to it:

- Rewrite inclusions as equalities
- Rewrite reflexive closures as unions
- Unfold the definition of the transitive closure (see [t_clos])
- Unfold the definitions of the identity set and of the empty set (see [id] and
[empty]).
- Apply the [fold_relAlg] tactic of the ATBR library to lift the equation about
relations to an equation about kleene algebras *)

Ltac kleene X := try (rewrite -> inclusion_as_eq in *);
                 try (rewrite -> refl_as_union in *);
                 unfold "⁺" in *;
                 unfold id; unfold empty;
                 fold_relAlg X;
                 kleene_reflexivity.

(** ** Basic Lemmas *)

(** The union of relations is commutative *)

Lemma union_comm {A:Type} (r1 r2 : relation A):
  (r1 <+> r2) = (r2 <+> r1).
Proof.
  apply ext_rel. kleene A.
Qed.

(** The union of relations is commutative *)

Lemma union_assoc {A:Type} (r1 r2 r3 : relation A):
  (r1 <+> (r2 <+> r3)) = ((r1 <+> r2) <+> r3).
Proof.
  apply ext_rel. kleene A.
Qed.

(** If two relations are included in a third relation, their union is included
in the third relation *)

Lemma union_incl {A:Type} (r1 r2 r3: relation A):
  r1 ⊆ r3 ->
  r2 ⊆ r3 ->
  r1 <+> r2 ⊆ r3.
Proof.
  intros H1 H2 x y [H|H].
  - apply (H1 _ _ H).
  - apply (H2 _ _ H).
Qed.

(** If a first relation is included in a second relation, it is included in the
union of the second relation with any other relation *)

Lemma incl_union_left {A:Type} (r1 r2 r3: relation A):
  r1 ⊆ r2 ->
  r1 ⊆ r2 <+> r3.
Proof.
  intros H x y Hnot. left. apply (H _ _  Hnot).
Qed.

Lemma incl_union_right {A:Type} (r1 r2 r3: relation A):
  r1 ⊆ r3 ->
  r1 ⊆ r2 <+> r3.
Proof.
  intros H x y Hnot. right. apply (H _ _  Hnot).
Qed.

(** This tactic transforms a goal of the form [r ⊆ r1 <+> ... <+> rn] in a goal
of the form [r ⊆ r2 <+> ... <+> rn] *)

Ltac incl_union_l :=
  repeat (rewrite <- union_assoc);
  apply incl_union_right.

(** This tactic transforms a goal of the form [r ⊆ r1 <+> ... <+> rn] in a goal
of the form [r ⊆ r1 <+> ... <+> r(n-1)] *)

Ltac incl_union_r :=
  repeat (rewrite -> union_assoc);
  apply incl_union_left;
  repeat (rewrite <- union_assoc).

(** The sequence of relations is associative *)

Lemma seq_assoc {A:Type} (r1 r2 r3 : relation A):
  (r1 ;; r2 ) ;; r3 = r1 ;; (r2 ;; r3).
Proof.
  apply ext_rel. kleene A.
Qed.

(** The inclusion of relations is transitive *)

Lemma incl_trans {A:Type} (r1 r2 r3 : relation A):
  r1 ⊆ r2 -> r2 ⊆ r3 -> r1 ⊆ r3.
Proof.
  intros H1 H2 x y H.
  apply (H2 _ _ (H1 _ _ H)).
Qed.

Lemma incl_trans2 {A:Type} (r1 r2 r3 : relation A):
  r2 ⊆ r3 -> r1 ⊆ r2 -> r1 ⊆ r3.
Proof.
  intros H1 H2 x y H.
  apply (H1 _ _ (H2 _ _ H)).
Qed.

(** The union of the transitive closures of two relations is included in the
transitive closure of the union of these two relations *)

Lemma incl_tc_union {A:Type} (r1 r2: relation A):
  r1⁺ <+> r2⁺ ⊆ (r1 <+> r2)⁺.
Proof.
  kleene A.
Qed.

(** The union of the transitive closure of a relation and of a second relation
is included in the union of the transitive closure of the two relations *)

Lemma incl_union_of_tc_right {A:Type} (r1 r2 : relation A):
  r1⁺ <+> r2 ⊆ r1⁺ <+> r2⁺.
Proof.
  kleene A.
Qed.

(** The union of a relation and of the transitive closure of a second relation
is included in the union of the transitive closure of the two relations *)

Lemma incl_union_of_tc_left {A:Type} (r1 r2 : relation A):
  r1 <+> r2⁺ ⊆ r1⁺ <+> r2⁺.
Proof.
  kleene A.
Qed.

(** The transitive closure of a relation is transitive *)

Lemma tc_trans {A:Type} (r1 : relation A) (x y z : A):
  r1⁺ x y ->
  r1⁺ y z ->
  r1⁺ x z.
Proof.
  intros [w [H1 H2]] [w' [H3 H4]]. exists w; split; auto.
  apply rt_trans with (y:=y); auto.
  apply rt_trans with (y:=w'); auto.
  apply rt_step; auto.
Qed.

(** The transitive closure of a relation is equal to the sequence of the 
reflexive transitive closure and of the relation *)

Lemma tc_inv_dcmp {A:Type} (r1: relation A):
  r1⁺ = r1** ;; r1.
Proof.
  apply ext_rel.
  kleene A.
Qed.

(** The transitive closure of the reflexive closure of a relation is the
transitive reflexive closure of this relation *)
  
Lemma refl_trans_equiv {A:Type} (r1 : relation A):
  r1 ? ⁺ = r1 **.
Proof.
  apply ext_rel; kleene A.
Qed.

(** The transtive reflexive closure of the reflexive closure of a relation is
the transitive reflexive closure of this relation *)

Lemma refl_refl_trans {A:Type} (r1 : relation A):
  r1 ? ** = r1 **.
Proof.
  apply ext_rel. kleene A.
Qed.

(** A relation is included in its transitive closure *)

Lemma tc_incl_itself {A:Type} (R: relation A):
  R ⊆  R⁺.
Proof.
  kleene A.
Qed.

(** The restriction of a relation is included in the relation *)

Lemma res_eset_incl {A} (e : Ensemble A) (r : relation A):
  (res_eset e r) ⊆ r.
Proof.
  intros x y [_ [_ H]]. auto.
Qed.

(** If a first relation is included in a second relation, the transitive closure
of the first relation is included in the transitive closure of the second
relation *)

Lemma tc_incl {A : Type}  (r1 r2 : relation A):
  r1 ⊆ r2 -> r1⁺ ⊆  r2⁺.
Proof.
intros H.
rewrite -> inclusion_as_eq in *. unfold "⁺".
apply ext_rel in H. rewrite <- H.
kleene A.
Qed.

(** The transitive closure of the transitive closure of a relation is the
transitive closure of this relation *)

Lemma tc_of_tc_is_tc {A:Type} (r1: relation A):
  (r1⁺)⁺ = r1⁺.
Proof.
  apply ext_rel.
  kleene A.
Qed.

(** If the sequence of two relations related a pair of elements, the first
relation relates two elements *)

Lemma shorten_path_on_right {A : Type} (r1 r2 : relation A):
  (exists x y, (r1 ;; r2) x y) ->
  (exists x y, r1 x y).
Proof.
  intros [x [y [z [H1 H2]]]].
  exists x, z; auto.
Qed.

(** If the sequence of two relations related a pair of elements, the second
relation relates two elements *)

Lemma shorten_path_on_left {A : Type} (r1 r2 : relation A):
  (exists x y, (r1 ;; r2) x y) ->
  (exists x y, r2 x y).
Proof.
  intros [x [y [z [H1 H2]]]].
  exists z, y; auto.
Qed.

(** If two elements are related by a first relation and if the first relation is
included in a second relation, the second relation also relates the two 
elements *)

Lemma incl_rel_thm {A:Type} {r r' : relation A} {x y :A}:
  r x y ->
  r ⊆ r' ->
  r' x y.
Proof.
  intros H1 H2.
  apply H2 in H1; auto.
Qed.

(** ** Acyclicity and Cyclicity Lemmas *)

(** A relation that is not acyclic is cyclic *)

Lemma not_acyclic_is_cyclic {A:Type} (r: relation A):
  ~(acyclic r) ->
  (cyclic r).
Proof.
  intros H.
  unfold acyclic in H; unfold acyclic.
  byabsurd. destruct H. intros x H.
  apply Hcontr. exists x. auto.
Qed.

(** If a relation is included in an acyclic relation, it is also acyclic *)

Lemma ac_incl {A : Set}  (r1 r2 : relation A) :
  acyclic r2 -> r1 ⊆ r2 -> acyclic r1.
Proof.
intros Hac Hinc x Hnot. apply (Hac x).
apply tc_incl in Hinc. apply Hinc in Hnot. auto.
Qed.

(** If there is a cycle in the union of two relations, there is either a cycle
in the first relation or a cycle in the second relation *)

Lemma cyclic_union {A:Type} (r1 r2 : relation A):
  (exists x, (r1 <+> r2) x x) ->
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

Lemma cyclic_implies_path {A:Type} (r: relation A):
  (exists x, r x x) ->
  (exists x y, r x y).
Proof.
  intros [x H]; exists x,x; auto.
Qed.

(** If there is a cycle in a relation, there is the same  cycle in the sequence 
of the relation with itself *)

Lemma double_cycle {A:Type} (r: relation A) (x: A):
  r x x ->
  (r ;; r) x x.
Proof.
  intros H. exists x; split; auto.
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

Lemma double_tc_in_path {A:Type} (r1 r2 : relation A):
  (exists x y, (r1 ;; r2⁺ ;; r2⁺ ;; r1) x y) ->
  (exists x y, (r1 ;; r2⁺ ;; r1) x y).
Proof.
  intros [w1 [w2 [z1 [H1 [z2 [H2 [z3 [H3 H4]]]]]]]].
  exists w1, w2, z1; split; auto.
  exists z3; split; auto.
  apply tc_trans with (y:=z2); auto.
Qed.

(** We decompose the transitive closure of the union of two relations in the
union of several relations to analyze different cases in the proof of [ac_union]
*)

Lemma tc_union_decomposition {A:Type} (r1 r2 : relation A):
  (r1 <+> r2)⁺
  =
  r1⁺ <+> r2⁺ <+>
  (r1 <+> r2)** ;; r1 ;; r2⁺ ;; r1 ;; (r1 <+> r2)** <+> 
  r1 ;; r2⁺ <+>
  r2⁺ ;; r1 ;; r2⁺ <+>
  r2⁺ ;; r1 <+>
  r1 ;; (r1 <+> r2)** ;; r1 ;; r2⁺ <+>
  r2⁺ ;; r1 ;; (r1 <+> r2)** ;; r1 ;; r2⁺ <+>
  r2⁺ ;; r1 ;; (r1 <+> r2)** ;; r1.
Proof.
  apply ext_rel.
  kleene A.
Qed.

(** If two relations are acyclic, but their union is cyclic, then there exists
two elements belonging to the cycle that are related by the sequence of:

- The first relation
- The transitive closure of the second relation
- The first relation
*)

Lemma ac_union {A:Type} (x:A) (r1 r2 : relation A) :
  acyclic r1 ->
  acyclic r2 ->
  (r1 <+> r2)⁺ x x ->
  exists y z, (r1 <+> r2)** x y /\
              (r1 ;; r2⁺ ;; r1) y z /\
              (r1 <+> r2)** z x.
Proof.
  intros Hac1 Hac2 Hcyc. unfold cyclic in Hcyc.
  rewrite tc_union_decomposition in Hcyc.
  destruct_disjunction Hcyc.
  - destruct (Hac1 x Hcyc).
  - destruct (Hac2 x Hcyc).
  - destruct Hcyc as [z1 [Hbegin Hcyc]];
    repeat (rewrite <- seq_assoc in Hcyc);
    destruct Hcyc as [z2 [Hmid Hend]];
    repeat (rewrite seq_assoc in Hmid).
    exists z1,z2. auto.
  - apply double_cycle in Hcyc.
    apply double_cycle in Hcyc.
    repeat (rewrite -> seq_assoc in Hcyc).
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z1 [Hbegin Hcyc]].
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z2 [Hmid Hend]].
    exists z1, z2. repeat (try split).
    + apply (incl_rel_thm Hbegin).
      kleene A.
    + apply (incl_rel_thm Hmid).
      kleene A.
    + apply (incl_rel_thm Hend).
      kleene A.
  - apply double_cycle in Hcyc.
    repeat (rewrite -> seq_assoc in Hcyc).
    destruct Hcyc as [z1 [Hbegin Hcyc]].
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z2 [Hmid Hend]].
    exists z1, z2. repeat (try split).
    + apply (incl_rel_thm Hbegin).
      kleene A.
    + apply (incl_rel_thm Hmid).
      kleene A.
    + apply (incl_rel_thm Hend).
      kleene A.
  - apply double_cycle in Hcyc.
    apply double_cycle in Hcyc.
    repeat (rewrite -> seq_assoc in Hcyc).
    destruct Hcyc as [z1 [Hbegin Hcyc]].
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z2 [Hmid Hend]].
    exists z1, z2. repeat (try split).
    + apply (incl_rel_thm Hbegin).
      kleene A.
    + apply (incl_rel_thm Hmid).
      kleene A.
    + apply (incl_rel_thm Hend).
      kleene A.
  - apply double_cycle in Hcyc.
    repeat (rewrite -> seq_assoc in Hcyc).
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z1 [Hbegin Hcyc]].
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z2 [Hmid Hend]].
    exists z1, z2. repeat (try split).
    + apply (incl_rel_thm Hbegin).
      kleene A.
    + apply (incl_rel_thm Hmid).
      kleene A.
    + apply (incl_rel_thm Hend).
      kleene A.
  - apply double_cycle in Hcyc.
    repeat (rewrite -> seq_assoc in Hcyc).
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z1 [Hbegin Hcyc]].
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z2 [Hmid Hend]].
    exists z1, z2. repeat (try split).
    + apply (incl_rel_thm Hbegin).
      kleene A.
    + apply (incl_rel_thm Hmid).
      kleene A.
    + apply (incl_rel_thm Hend).
      kleene A.
  - apply double_cycle in Hcyc.
    repeat (rewrite -> seq_assoc in Hcyc).
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z1 [Hbegin Hcyc]].
    rewrite <- seq_assoc in Hcyc.
    rewrite <- seq_assoc in Hcyc.
    destruct Hcyc as [z2 [Hmid Hend]].
    exists z1, z2. repeat (try split).
    + apply (incl_rel_thm Hbegin).
      kleene A.
    + apply (incl_rel_thm Hmid).
      kleene A.
    + apply (incl_rel_thm Hend).
      kleene A.
Qed.


(** The transitive closure of a strict linear order is itself *)

Lemma lso_is_tc {A:Type} (so:relation A) (s: Ensemble A):
  linear_strict_order so s -> so⁺ = so.
Proof.
  intros [[H1 H2] H3]; apply ext_rel; split; intros x y H.
  - destruct H as [z [H4 H5]].
    induction H5.
    + apply H2 with (x2 := x0); split; auto.
    + auto.
    + auto.
  - apply tc_incl_itself. auto.
Qed.

(** A strict linear order is acyclic *)

Lemma lin_strict_ac {A:Type} (s:Ensemble A) (r : relation A):
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

Lemma transitive_tc {A:Type} (r: relation A):
  (forall x1 x2 x3, (r x1 x2) /\ (r x2 x3) -> (r x1 x3)) ->
  r⁺ = r.
Proof.
  intros Htrans.
  apply ext_rel. split; intros x y H.
  - destruct H as [z [H H']].
    induction H' as [w z H2 | w | v w z H1 IH1 H2 IH2].
    + apply (Htrans x w z); split; auto.
    + auto.
    + apply IH2. apply IH1. auto.
  - exists y; split; auto. apply rt_refl; auto.
Qed.

(** If a relation is acyclic, its transitive closure is acyclic *)

Lemma tc_ac_is_ac {A:Type} (r: relation A):
  acyclic r ->
  acyclic (r⁺).
Proof.
  unfold acyclic. rewrite tc_of_tc_is_tc.
  auto.
Qed.
