(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Ensembles.
Require Import Classical_Prop.
Require Import Nat.
From RC11 Require Import util.
From RC11 Require Import proprel_classic.
From RelationAlgebra Require Import 
  lattice prop monoid rel kat_tac normalisation kleene kat rewriting.

Open Scope rel_notations.

(** The file contains the definition of complete executions. It corresponds to 
section 3.1 (and to the very first paragraph of section 3.2) of the article *)

(** * Basic types *)

(** ** Locations and values *)

(** We abstract from word-size and alignment issues for now,
representing both memory locations and the values that may be
stored in them by natural numbers. *)

Definition Word := nat.

Definition Loc := Word.

Definition Val := Word.

(** ** Modes *)

(** Modes indicate if an event is atomic or not and if so, at which level of
atomicity.

The possible modes are: non-atomic, relaxed, acquire, release, acquire-release
and sequentially consistent
*)

Inductive Mode : Set :=
| Na : Mode
| Rlx : Mode
| Acq : Mode
| Rel : Mode
| AcqRel : Mode
| Sc : Mode.

(** *** Modes ordering *)

Definition eq_mode (m1 m2 : Mode) : bool :=
  match (m1, m2) with
  | (Na, Na)
  | (Rlx, Rlx)
  | (Acq, Acq)
  | (Rel, Rel)
  | (AcqRel, AcqRel)
  | (Sc, Sc) => true
  | _ => false
  end.

Lemma eq_mode_refl (m: Mode):
  eq_mode m m.
Proof. destruct m; auto. Qed.


(** There is a strict partial order on modes such that:

- [Na] is weaker than [Rlx]
- [Rlx] is weaker than [Acq] and [Rel]
- [Acq] and [Rel] are weaker than [AcqRel]
- [AcqRel] is weaker than [Sc]. *)

Definition weaker_mode (m1 m2 : Mode) : bool :=
  match (m1, m2) with
  | (Na, Na) => false
  | (Na, _) => true
  | (Rlx, Na) | (Rlx, Rlx) => false
  | (Rlx, _) => true
  | (Acq, AcqRel) | (Acq, Sc) => true
  | (Acq, _) => false
  | (Rel, AcqRel) | (Rel, Sc) => true
  | (Rel, _) => false
  | (AcqRel, Sc) => true
  | (AcqRel, _) => false
  | (Sc, _) => false
  end.

Definition stronger_or_eq_mode (m1 m2 : Mode) : bool :=
  negb (weaker_mode m1 m2).

Hint Unfold stronger_or_eq_mode : exec.

(** *** Read mode *)

(** A read event can have mode non-atomic, relaxed, acquire or sequentially
consistent *)

Definition read_mode (m: Mode) : Prop :=
  match m with
  | Na | Rlx | Acq | Sc => True
  | _ => False
  end.

(** *** Write mode *)

(** A write event can have mode non-atomic, relaxed, release or sequentially
consistent *)

Definition write_mode (m: Mode) : Prop :=
  match m with
  | Na | Rlx | Rel | Sc => True
  | _ => False
  end.

(** *** Fence mode *)

(** A fence event can have mode acquire, release, acquire-release or sequentially
consistent *)
 
Definition fence_mode (m: Mode) : Prop :=
  match m with
  | Acq | Rel | AcqRel | Sc => True
  | _ => False
  end.

(** ** Event *)

(** An event can be:

- A read event, it then has a read mode, a location and a value
- A write event, it then has a write mode, a location and a value
- A fence event, it then has a fence mode

Every single event has a unique event id
*)

Inductive Event : Type :=
| Read (eid: nat) (m: Mode) (l: Loc) (v: Val)
| Write (eid: nat) (m: Mode) (l: Loc) (v: Val)
| Fence (eid: nat) (m: Mode).

Instance incl_event_trans : Transitive (Included Event).
Proof. compute; auto. Qed.

Definition is_read (e: Event) : Prop :=
  match e with
  | Read _ _ _ _ =>  True
  | Write _ _ _ _ => False
  | Fence _ _ => False
  end.

Definition is_write (e: Event) : Prop :=
  match e with
  | Read _ _ _ _ =>  False
  | Write _ _ _ _ => True
  | Fence _ _ => False
  end.

Definition is_fence (e: Event) : Prop :=
  match e with
  | Read _ _ _ _ =>  False
  | Write _ _ _ _ => False
  | Fence _ _ => True
  end.


(** ** Validity conditions *)

(** Is the mode of an event valid *)

Definition valid_mode (e: Event) : Prop :=
  match e with
  | Read _ m _ _ => read_mode m
  | Write _ m _ _ => write_mode m
  | Fence _ m => fence_mode m
  end.

(** ** Getter functions *)

(** Get the id of an event *)

Definition get_eid (e: Event) : nat :=
  match e with
  | Read eid _ _ _ => eid
  | Write eid _ _ _ => eid
  | Fence eid _ => eid
  end.

(** Get the location of an event if it has one *)

Definition get_loc (e: Event) : option Loc :=
  match e with
  | Read _ _ l _ => Some l
  | Write _ _ l _ => Some l
  | Fence _ _ => None
  end.

(** Get the value of an event if it has one *)

Definition get_val (e: Event) : option Val :=
  match e with
  | Read _ _ _ v => Some v
  | Write _ _ _ v => Some v
  | Fence _ _ => None
  end.

(** Get the mode of an event *)

Definition get_mode (e: Event) : Mode :=
  match e with
  | Read _ m _ _ => m
  | Write _ m _ _ => m
  | Fence _ m => m
  end.

(** ** Events validity *)

(** Are the modes of a set of events valid *)

Definition valid_evts (evts: Ensemble Event) : Prop :=
  (forall e1 e2, (In _ evts e1) -> (In _ evts e2) -> 
    (get_eid e1) <> (get_eid e2) \/ e1 = e2) /\
  (forall e, (In _ evts e) -> valid_mode e).

(** ** Order Extension of events relation *)

(** We admit that we can extend any partial order on events to a total order.
This extension is called a linear extension. The module [OEEvt] specifies
the properties of linear extension of events, and satisfies the general
module type [OrdExt].
*)

Module OEEvt <: OrdExt.

Definition Elt := Event.

(** This extension is called a linear extension (LE) *)

Parameter LE : rlt Event -> rlt Event.

(** A relation is included in its linear extension and this extension is
a strict linear order (i.e. it is total) *)

Axiom OE : forall (s S:Ensemble Event) (r:rlt Event),
  Included _ s S ->
  partial_order r s ->
  r ≦  (LE r) /\
  linear_strict_order (LE r) S.

(** The linear extension of a strict linear order on events is itself *)

Axiom le_lso : forall (s:Ensemble Event) (r:rlt Event),
  linear_strict_order r s -> LE r = r.
End OEEvt.

Import OEEvt.

(** * Basic relations *)

(** ** Identity relations *)

Definition E : prop_set Event := top.

Definition R : prop_set Event :=
  fun e =>
    match e with
    | Read _ _ _ _ => top
    | _ => bot
    end.

Definition W : prop_set Event :=
  fun e =>
    match e with
    | Write _ _ _ _ => top
    | _ => bot
    end.

Definition F : prop_set Event :=
  fun e =>
    match e with
    | Fence _ _ => top
    | _ => bot
    end.

Definition M (m:Mode) : prop_set Event :=
  fun e => (get_mode e) = m.

Definition Mse (m: Mode) : prop_set Event :=
  fun e =>
    if (stronger_or_eq_mode (get_mode e) m) then top else bot.

(** No event can be both a write event an read event *)

Lemma rw_0: [R] ⋅ [W] ≦ empty.
Proof.
  intros x y H.
  destruct H as [z [Heqx Hw] [Heqy Hr]].
  rewrite Heqy in Hr.
  destruct x, y; cbv in Hw, Hr;
  intuition congruence.
Qed.

Lemma wr_0: [W] ⋅ [R] ≦ empty.
Proof.
  intros x y H.
  destruct H as [z [Heqx Hr] [Heqy Hw]].
  rewrite Heqy in Hw.
  destruct x, y; cbv in Hw, Hr;
  intuition congruence.
Qed.

(** ** Relations restrictions *)

(** [res_eq_loc r] restricts a relation [r] to the pairs of events that affect 
the same location *)

Definition res_eq_loc (r: rlt Event) : rlt Event :=
  fun x => fun y =>
    r x y /\
    (get_loc x) = (get_loc y).

(** [res_neq_loc r] restricts a relation [r] to the pairs of events that affect 
a different location *)

Definition res_neq_loc (r: rlt Event) : rlt Event :=
  fun x => fun y =>
    r x y /\
    (get_loc x) <> (get_loc y).

(** Restricting relations to the event that affect the same location, or that
affect a different location preserve inclusion of relations *)

Lemma res_loc_incl (r1 r2: rlt Event) :
  r1 ≦ r2 -> (res_eq_loc r1) ≦ (res_eq_loc r2).
Proof.
  intros H x y [Hr1 Heqloc].
  split; auto.
  apply H; auto.
Qed.

Lemma res_neq_loc_incl (r1 r2: rlt Event):
  r1 ≦ r2 -> (res_neq_loc r1) ≦ (res_neq_loc r2).
Proof.
  intros H x y [Hr1 Hneqloc].
  split; auto.
  apply H; auto.
Qed.

(** [res_mode m r] restricts a relation [r] to the pairs of events that have mode
[m] *)

Definition res_mode (m: Mode) (r: rlt Event) :=
  [M m] ⋅ r ⋅ [M m].

Lemma res_mode_conds : forall m r x y,
  (get_mode x) = m /\
  (get_mode y) = m /\
  r x y ->
  (res_mode m r) x y.
Proof.
  intros m r x y [Hfst [Hsnd Hr]].
  exists y.
  - exists x; try split; auto.
  - split; auto.
Qed.

Lemma res_mode_simp {m:Mode} {r: relation _} {x y: _}:
  (res_mode m r) x y ->
  (get_mode x) = m /\
  (get_mode y) = m /\
  r x y.
Proof.
  intros H.
  destruct H as [z [z' [H1 H2] H3] [H4 H5]]. 
  repeat (try split).
  - auto.
  - rewrite H4 in H5. auto.
  - rewrite <- H1 in H3. rewrite H4 in H3. auto.
Qed.

Lemma res_mode_fst_mode : forall m r x y,
  (res_mode m r) x y ->
  (get_mode x) = m.
Proof.
  intros m r x y H.
  destruct (res_mode_simp H) as [Hfst [Hsnd Hr]]. auto.
Qed.

Lemma res_mode_snd_mode : forall m r x y,
  (res_mode m r) x y ->
  (get_mode y) = m.
Proof.
  intros m r x y H.
  destruct (res_mode_simp H) as [Hfst [Hsnd Hr]]. auto.
Qed.

Lemma res_mode_rel {m: Mode} {r: relation _} {x y: _}:
  (res_mode m r) x y ->
  r x y.
Proof.
  intros H.
  destruct (res_mode_simp H) as [Hfst [Hsnd Hr]]. auto.
Qed.

Definition res_neq_mode (m:Mode) (r: rlt Event) :=
  [!M m] ⋅ r ⋅ [!M m] ⊔
  [M m] ⋅ r ⋅ [!M m] ⊔
  [!M m] ⋅ r ⋅ [M m].

Lemma dcmp_in_res_neq_res (m: Mode) (r: rlt Event) :
  r = (res_neq_mode m r) ⊔ (res_mode m r).
Proof.
  apply ext_rel.
  unfold res_neq_mode, res_mode.
  kat.
Qed.

Lemma res_mode_incl (m:Mode) (r1 r2: rlt Event):
  r1 ≦ r2 -> (res_mode m r1) ≦ (res_mode m r2).
Proof.
  intros Hincl.
  unfold res_mode.
  apply incl_dot.
  apply incl_dot.
  all: auto.
Qed.

Lemma res_neq_incl (m:Mode) (r1: rlt Event):
  (res_neq_mode m r1) ≦ r1.
Proof.
  unfold res_neq_mode. kat.
Qed.

(** ** Set of reads and writes on a set of events *)

Definition reads (evts: Ensemble Event) : Ensemble Event :=
  fun e => (In _ evts e) /\ is_read e.

Definition writes (evts: Ensemble Event) : Ensemble Event :=
  fun e => (In _ evts e) /\ is_write e.

Definition writes_loc (evts: Ensemble Event) (l: Loc) : Ensemble Event :=
  fun e => 
    (In _ evts e) /\
    is_write e /\
    (get_loc e) = Some l.

Lemma writes_loc_incl (e1 e2: Ensemble Event) (l: Loc) (x: Event):
  Included _ e1 e2 ->
  In _ (writes_loc e1 l) x ->
  In _ (writes_loc e2 l) x.
Proof.
  intros Hincl [Hevts [Hw Hl]].
  apply Hincl in Hevts.
  repeat (apply conj); auto.
Qed.

Lemma writes_loc_evts (e: Ensemble Event) (l: Loc) (x: Event):
  In _ (writes_loc e l) x ->
  In _ e x.
Proof. intros [? _]. auto. Qed.

Lemma writes_loc_is_write (e: Ensemble Event) (l: Loc) (x: Event):
  In _ (writes_loc e l) x ->
  is_write x.
Proof. intros [_ [? _]]. auto. Qed.

Lemma writes_loc_loc (e: Ensemble Event) (l: Loc) (x: Event):
  In _ (writes_loc e l) x ->
  (get_loc x) = Some l.
Proof. intros [_ [_ ?]]. auto. Qed.

(** ** Sequenced before *)

(** A sequenced before relation is valid if it is a strict partial order and
if for each location, there is an initialisation event that sets the location
to 0, is sequenced before all the events of the program and after no events *)

Definition valid_sb (evts: Ensemble Event) (sb : rlt Event) : Prop :=
  (linear_strict_order sb evts) /\
  (forall (l : Loc),
  exists (e: Event),
    (get_loc e) = Some l /\
    (get_val e) = Some O /\
    ~(In _ (ran sb) e) /\
    forall e', In _ (ran sb) e' -> sb e e').

Ltac destruct_sb_v H :=
  destruct H as [Hsb_lso Hsbinit].

(** ** Read-modify-write relation *)

(** A read event and a write event to the same location that are connected by an
immediate edge in the sequenced-before relation are called a read-modify-write
pair if their modes are one of the following pairs:

- [(Rlx, Rlx)]
- [(Acq, Rlx)]
- [(Rlx, Rel)]
- [(Acq, Rel)]
- [(Sc, Sc)]
 *)
 
Definition valid_rmw_pair (sb : rlt Event) (r: Event) (w: Event) : Prop :=
  match (get_mode r, get_mode w) with
  | (Rlx, Rlx) | (Acq, Rlx) | (Rlx, Rel) | (Acq, Rel) | (Sc, Sc) =>
    (is_read r /\
     is_write w /\
     (get_loc r) = (get_loc w) /\
     (imm sb) r w)
  | _ => False
  end.

(** A read-modify-write relation is a set of read-modify-write pairs *)

Definition valid_rmw (evts: Ensemble Event) (sb : rlt Event) (rmw : rlt Event) : Prop :=
  (forall r w, rmw r w -> valid_rmw_pair sb r w) /\
  (rmw = [I evts] ⋅ rmw ⋅ [I evts]).

Ltac destruct_rmw_v H :=
  destruct H as [Hrmw_vpairs Hrmw_in_e].

(** ** Reads-from relation *)

(** The reads-from relation connects a write and a read events of the same value to
the same location and is such that if [rf r1 w] and [rf r2 w], then [r1 = r2].
To put it more simply, the read-from relation connects every read event to
exactly one write event that wrote the value it reads
*)

Definition valid_rf (evts : Ensemble Event) (rf : rlt Event) : Prop :=
  (forall w r, 
    rf w r ->
    ((get_loc w) = (get_loc r) /\
     (get_val w) = (get_val r))) /\
  (rf = [I evts] ⋅ rf ⋅ [I evts]) /\
  ([W]⋅rf⋅[R] = rf) /\
  (forall w1 w2 r,
    (rf w1 r) /\ (rf w2 r) -> w1 = w2).

Ltac destruct_rf_v H :=
  destruct H as [Hrfco [Hrf_in_e [Hrfwr Hrfun]]].

(** The sequence of read-from and of the converse of read-from is a reflexive
relation. This means that each read can read the value of only one write *)

Lemma rf_unique (evts: Ensemble Event) (rf: rlt Event):
  valid_rf evts rf ->
  rf⋅rf° ≦ 1.
Proof.
  intros Hval x y [z Hrf Hrfconv].
  simp_cnv Hrfconv.
  destruct_rf_v Hval.
  generalize (Hrfun x y z). 
  intuition auto.
Qed.

Lemma rf_incl_same_loc (evts: Ensemble Event) (rf r: rlt Event):
  valid_rf evts rf ->
  rf ≦ r ->
  rf ≦ res_eq_loc r.
Proof.
  intros Hval Hincl x y Hrf.
  destruct_rf_v Hval.
  destruct (Hrfco _ _ Hrf) as [Hsameloc _].
  split; auto. apply Hincl; auto.
Qed.

Lemma rf_valid_test_right (evts: Ensemble Event) (rf: rlt Event) (t: prop_set Event):
  valid_rf evts rf ->
  valid_rf evts (rf ⋅ [t]).
Proof.
  intros Hval.
  unfold valid_rf.
  destruct_rf_v Hval.
  split;[|split;[|split]].
  - intros w1 w2 r. eapply Hrfco.
    destruct r as [? Hr [Heq _]].
    rewrite Heq in Hr; auto.
  - rewrite Hrf_in_e at 1. apply ext_rel. kat.
  - rewrite <- Hrfwr at 2. apply ext_rel. kat.
  - intros w1 w2 r. intros [Hw1 Hw2].
    apply (Hrfun w1 w2 r).
    split.
    + destruct Hw1 as [z H [Heq _]]. rewrite Heq in H. auto.
    + destruct Hw2 as [z H [Heq _]]. rewrite Heq in H. auto.
Qed.

Lemma rf_valid_test_left (evts: Ensemble Event) (rf: rlt Event) (t: prop_set Event):
  valid_rf evts rf ->
  valid_rf evts ([t] ⋅ rf).
Proof.
  intros Hval.
  unfold valid_rf.
  destruct_rf_v Hval.
  split;[|split;[|split]].
  - intros w1 w2 r. eapply Hrfco.
    destruct r as [? [Heq _] Hr].
    rewrite <- Heq in Hr; auto.
  - rewrite Hrf_in_e at 1. apply ext_rel. kat.
  - rewrite <- Hrfwr at 2. apply ext_rel. kat.
  - intros w1 w2 r. intros [Hw1 Hw2].
    apply (Hrfun w1 w2 r).
    split.
    + destruct Hw1 as [z [Heq _] H]. rewrite <- Heq in H. auto.
    + destruct Hw2 as [z [Heq _] H]. rewrite <- Heq in H. auto.
Qed.

(** ** Modification order *)

(** The modification order is a strict partial order on the write events, which 
is the disjoint union of total orders on the write events to a specific location
for each location.
It correponds to write serialisation or coherence order in some other works on 
axiomatic memory models.
*)

Definition mo_for_loc (mo : rlt Event) (l : Loc) : rlt Event :=
  fun w1 => fun w2 =>
    mo w1 w2 /\
    (get_loc w1) = (Some l) /\
    (get_loc w2) = (Some l).

Definition valid_mo (evts: Ensemble Event) (mo : rlt Event) : Prop :=
  ([W]⋅mo⋅[W] = mo) /\
  (forall x y, mo x y ->
               (get_loc x) = (get_loc y)) /\
  (partial_order mo evts) /\
  (forall l, total_rel (mo_for_loc mo l) (writes_loc evts l)).

Ltac destruct_mo_v H :=
  destruct H as [Hmoww [Hmosameloc [Hmopo Hmotot]]].

(** * Executions *)

(** ** Validity *)

(** An execution is:
- A set of events with valid modes
- A valid sequenced-before relation on these events
- A valid reads-from relation on these events
- A valid modification order on these events
*)

Record Execution : Type := mkex {
  evts : Ensemble Event;
  sb : rlt Event;
  rmw : rlt Event;
  rf : rlt Event;
  mo : rlt Event;
}.

Definition valid_exec (e: Execution) : Prop :=
  (* valid events mode *)
  valid_evts e.(evts) /\
  (* sequenced-before is valid *)
  valid_sb e.(evts) e.(sb) /\
  (* read-modify-write is valid *)
  valid_rmw e.(evts) e.(sb) e.(rmw) /\
  (* reads-from is valid *)
  valid_rf e.(evts) e.(rf) /\
  (* modification order is valid *)
  valid_mo e.(evts) e.(mo).
 
Ltac destruct_val_exec H :=
  destruct H as [Hevts_v [Hsb_v [Hrmw_v [Hrf_v Hmo_v]]]].

Ltac inverse_val_exec H :=
  inversion H as [Hevts_v [Hsb_v [Hrmw_v [Hrf_v Hmo_v]]]].

(** *** Lemmas about valid executions *)

Section ValidExecs.

Variable ex : Execution.
Variable val_exec : valid_exec ex.

(** Same eid implies same event *)

Lemma same_eid_same_evts (x y : Event):
  In _ (evts ex) x ->
  In _ (evts ex) y ->
  get_eid x = get_eid y ->
  x = y.
Proof.
  intros Hx Hy H.
  destruct_val_exec val_exec.
  destruct Hevts_v as [Hevts_v _].
  destruct (Hevts_v x y Hx Hy).
  - intuition auto.
  - auto.
Qed.

(** In a valid execution, events related by sequenced-before belong to the set
of events of the execution *)

Lemma sb_orig_evts (x y : Event):
  (sb ex) x y ->
  In _ (evts ex) x.
Proof.
  intros Hsb.
  destruct_val_exec val_exec.
  destruct Hsb_v as [[[Hsb_v _] _] _].
  rewrite Hsb_v in Hsb.
  destruct Hsb as [z [z' [_ Ht] _] _].
  auto.
Qed.

Lemma sb_dest_evts (x y : Event):
  (sb ex) x y ->
  In _ (evts ex) y.
Proof.
  intros Hsb.
  destruct_val_exec val_exec.
  destruct Hsb_v as [[[Hsb_v _] _] _].
  rewrite Hsb_v in Hsb.
  destruct Hsb as [z _ [Heq Ht]].
  rewrite Heq in Ht.
  auto.
Qed.

(** In a valid execution, the origin of a reads-from is a write event *)

Lemma rf_orig_write x y:
  (rf ex) x y ->
  is_write x.
Proof.
  intros Hrf.
  destruct_val_exec val_exec.
  destruct_rf_v Hrf_v.
  rewrite <- Hrfwr in Hrf.
  destruct Hrf as [z [z' Hw Hrf] Hr].
  destruct Hw as [Heq Hw].
  destruct x. simpl in Hw.
  - inversion Hw.
  - cbv; auto.
  - inversion Hw.
Qed.

(** In a valid execution, the destination of a reads-from is a read event *)

Lemma rf_dest_read x y:
  (rf ex) x y ->
  is_read y.
Proof.
  intros Hrf.
  destruct_val_exec val_exec.
  destruct_rf_v Hrf_v.
  rewrite <- Hrfwr in Hrf.
  destruct Hrf as [z [z' Hw Hrf] Hr].
  destruct Hr as [Heq Hr].
  rewrite Heq in Hr.
  destruct y; simpl in Hr.
  - cbv; auto.
  - inversion Hr.
  - inversion Hr.
Qed.

(** In a valid execution, two events related by read-from affect the same 
location *)

Lemma rf_same_loc x y:
  (rf ex) x y ->
  (get_loc x) = (get_loc y).
Proof.
  intros Hrf.
  destruct_val_exec val_exec.
  destruct_rf_v Hrf_v.
  destruct (Hrfco x y Hrf) as [Hloc _].
  auto.
Qed.

(** In a valid execution, events related by read-from belong to the set of
events of the execution *)

Lemma rf_orig_evts (x y: Event):
  (rf ex) x y ->
  In _ (evts ex) x.
Proof.
  intros Hrf.
  destruct_val_exec val_exec.
  destruct_rf_v Hrf_v.
  rewrite Hrf_in_e in Hrf.
  destruct Hrf as [z [z' [_ Ht] _] _].
  auto.
Qed.

Lemma rf_dest_evts (x y : Event):
  (rf ex) x y ->
  In _ (evts ex) y.
Proof.
  intros Hrf.
  destruct_val_exec val_exec.
  destruct_rf_v Hrf_v.
  rewrite Hrf_in_e in Hrf.
  destruct Hrf as [z _ [Heq Ht]].
  rewrite Heq in Ht.
  auto.
Qed.

(** In a valid execution, events related by read-modify-write order belong to 
the set of events of the execution *)

Lemma rmw_orig_evts (x y : Event):
  (rmw ex) x y ->
  In _ (evts ex) x.
Proof.
  intros Hrmw.
  destruct_val_exec val_exec.
  destruct_rmw_v Hrmw_v.
  rewrite Hrmw_in_e in Hrmw.
  destruct Hrmw as [z [z' [_ Ht] _] _].
  auto.
Qed.

Lemma rmw_dest_evts (x y : Event):
  (rmw ex) x y ->
  In _ (evts ex) y.
Proof.
  intros Hrmw.
  destruct_val_exec val_exec.
  destruct_rmw_v Hrmw_v.
  rewrite Hrmw_in_e in Hrmw.
  destruct Hrmw as [z _ [Heq Ht]].
  rewrite Heq in Ht.
  auto.
Qed.

(** The read-modify-write relation is included in the sequenced-before
relation *)

Lemma rmw_incl_sb:
  (rmw ex) ≦ (sb ex).
Proof.
  intros x y Hrmw.
  destruct_val_exec val_exec.
  destruct_rmw_v Hrmw_v.
  apply Hrmw_vpairs in Hrmw as Hrmwp.
  unfold valid_rmw_pair in Hrmwp.
  destruct (get_mode x); destruct (get_mode y);
  intuition (auto using (imm_rel_implies_rel (sb ex))).
Qed.

(** The read-modify-write relation is included in the immediate edges of the
sequenced-before relation *)

Lemma rmw_incl_imm_sb:
  (rmw ex) ≦ imm (sb ex).
Proof.
  intros x y Hrmw.
  destruct_val_exec val_exec.
  destruct_rmw_v Hrmw_v.
  apply Hrmw_vpairs in Hrmw as Hrmwp.
  unfold valid_rmw_pair in Hrmwp.
  (destruct (get_mode x); destruct (get_mode y)).
  all: intuition auto.
Qed.

(** In a valid execution, the origin of a read-modify-write edge is a read 
event *)

Lemma rmw_orig_read (x y: Event):
  (rmw ex) x y ->
  is_read x.
Proof.
  intros Hrmw.
  destruct_val_exec val_exec.
  destruct_rmw_v Hrmw_v.
  apply Hrmw_vpairs in Hrmw as Hrmwp.
  unfold valid_rmw_pair in Hrmwp.
  destruct (get_mode x); destruct (get_mode y);
  intuition auto.
Qed.

(** In a valid execution, the destination of a read-modify-write edge is write
event *)

Lemma rmw_dest_write (x y: Event):
  (rmw ex) x y ->
  is_write y.
Proof.
  intros Hrmw.
  destruct_val_exec val_exec.
  destruct_rmw_v Hrmw_v.
  apply Hrmw_vpairs in Hrmw as Hrmwp.
  unfold valid_rmw_pair in Hrmwp.
  destruct (get_mode x); destruct (get_mode y);
  intuition auto.
Qed.

(** In a valid execution, two events related by the read-modify-write relation
affect the same location *)

Lemma rmw_same_loc (x y: Event):
  (rmw ex) x y ->
  (get_loc x) = (get_loc y).
Proof.
  intros Hrmw.
  destruct_val_exec val_exec.
  destruct_rmw_v Hrmw_v.
  apply Hrmw_vpairs in Hrmw.
  unfold valid_rmw_pair in Hrmw.
  destruct (get_mode x); destruct (get_mode y);
  intuition auto.
Qed.

(** In a valid execution, events related by modification order belong to the set
of events of the execution *)

Lemma mo_orig_evts (x y : Event):
  (mo ex) x y ->
  In _ (evts ex) x.
Proof.
  intros Hmo.
  destruct_val_exec val_exec.
  destruct_mo_v Hmo_v.
  destruct Hmopo as [Hmo_v _].
  rewrite Hmo_v in Hmo.
  destruct Hmo as [z [z' [_ Ht] _] _].
  auto.
Qed.

Lemma mo_dest_evts (x y : Event):
  (mo ex) x y ->
  In _ (evts ex) y.
Proof.
  intros Hmo.
  destruct_val_exec val_exec.
  destruct_mo_v Hmo_v.
  destruct Hmopo as [Hmo_v _].
  rewrite Hmo_v in Hmo.
  destruct Hmo as [z _ [Heq Ht]].
  rewrite Heq in Ht.
  auto.
Qed.

(** In a valid execution, the origin of a modification-order is a write *)

Lemma mo_orig_write (x y : Event):
  (mo ex) x y ->
  is_write x.
Proof.
  intros Hmo.
  destruct_val_exec val_exec.
  destruct_mo_v Hmo_v.
  rewrite <- Hmoww in Hmo.
  destruct Hmo as [? [? Hxw]].
  destruct Hxw as [_ Hxw].
  unfold W in Hxw. destruct x.
  - inversion Hxw.
  - cbv; auto.
  - inversion Hxw.
Qed.

(** In a valid execution, the destination of a modification-order is a write *)

Lemma mo_dest_write (x y : Event):
  (mo ex) x y ->
  is_write y.
Proof.
  intros Hmo.
  destruct_val_exec val_exec.
  destruct_mo_v Hmo_v.
  rewrite <- Hmoww in Hmo.
  destruct Hmo as [z ? Hyw].
  destruct Hyw as [Heq Hyw].
  rewrite Heq in Hyw.
  destruct y; simpl in Hyw.
  - inversion Hyw.
  - cbv; auto.
  - inversion Hyw.
Qed.

(** In a valid execution, two events related by modification order affect the 
same location *)

Lemma mo_same_loc (x y : Event):
  (mo ex) x y ->
  (get_loc x) = (get_loc y).
Proof.
  intros Hmo.
  destruct_val_exec val_exec.
  destruct_mo_v Hmo_v.
  auto.
Qed.

(** If two write events to the same location are different, they must be related
by mo in a direction or the other *)

Lemma mo_diff_write (x y: Event) (l: Loc):
  In _ (writes_loc (evts ex) l) x ->
  In _ (writes_loc (evts ex) l) y ->
  x <> y ->
  (mo ex x y \/ mo ex y x).
Proof.
  intros Hxlw Hylw Hdiff.
  destruct_val_exec val_exec.
  destruct_mo_v Hmo_v.
  unfold total_rel in Hmotot.
  specialize (Hmotot l x y Hdiff Hxlw Hylw).
  destruct Hmotot as [Hmotot|Hmotot].
  - left. destruct Hmotot. auto.
  - right. destruct Hmotot. auto.
Qed.

(** mo is transitive *)

Lemma mo_trans (x y z: Event):
  (mo ex) x y ->
  (mo ex) y z ->
  (mo ex) x z.
Proof.
  intros Hmo1 Hmo2.
  destruct_val_exec val_exec.
  destruct_mo_v Hmo_v.
  destruct Hmopo as [_ [Hmotrans _]].
  apply Hmotrans. exists y; auto.
Qed.

End ValidExecs.

(** Atomic events are events that are either in the domain or in the range of
[rmw] *)

Definition At (ex: Execution) : Ensemble Event :=
  Union _ (dom ex.(rmw)) (ran ex.(rmw)).

(** ** Completeness *)

(** An execution is complete when it is valid and when every read reads a value
that was written at some point *)

Definition complete_exec (e: Execution) :=
  valid_exec e /\ Included _ (reads (evts e)) (ran e.(rf)).