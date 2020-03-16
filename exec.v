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
From RelationAlgebra Require Import 
  lattice prop monoid rel kat_tac normalisation kleene kat.

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
*)

Inductive Event : Type :=
| Read (m: Mode) (l: Loc) (v: Val)
| Write (m: Mode) (l: Loc) (v: Val)
| Fence (m: Mode).

Instance incl_event_trans : Transitive (Included Event).
Proof. compute; auto. Qed.

Definition is_read (e: Event) : Prop :=
  match e with
  | Read _ _ _ =>  True
  | Write _ _ _ => False
  | Fence _ => False
  end.

Definition is_write (e: Event) : Prop :=
  match e with
  | Read _ _ _ =>  False
  | Write _ _ _ => True
  | Fence _ => False
  end.

Definition is_fence (e: Event) : Prop :=
  match e with
  | Read _ _ _ =>  False
  | Write _ _ _ => False
  | Fence _ => True
  end.


(** ** Validity conditions *)

(** Is the mode of an event valid *)

Definition valid_mode (e: Event) : Prop :=
  match e with
  | Read m _ _ => read_mode m
  | Write m _ _ => write_mode m
  | Fence m => fence_mode m
  end.

(** Are the modes of a set of events valid *)

Definition valid_evts (evts: Ensemble Event) : Prop :=
  (forall e, (In _ evts e) -> valid_mode e).

(** ** Getter functions *)

(** Get the location of an event if it has one *)

Definition get_loc (e: Event) : option Loc :=
  match e with
  | Read _ l _ => Some l
  | Write _ l _ => Some l
  | Fence _ => None
  end.

(** Get the value of an event if it has one *)

Definition get_val (e: Event) : option Val :=
  match e with
  | Read _ _ v => Some v
  | Write _ _ v => Some v
  | Fence _ => None
  end.

(** Get the mode of an event *)

Definition get_mode (e: Event) : Mode :=
  match e with
  | Read m _ _ => m
  | Write m _ _ => m
  | Fence m => m
  end.

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

Definition E : dset Event := top.

Definition R : dset Event :=
  fun e =>
    match e with
    | Read _ _ _ => top
    | _ => bot
    end.

Definition W : dset Event :=
  fun e =>
    match e with
    | Write _ _ _ => top
    | _ => bot
    end.

Definition F : dset Event :=
  fun e =>
    match e with
    | Fence _ => top
    | _ => bot
    end.

Definition M (m:Mode) : dset Event :=
  fun e =>
    if (eq_mode (get_mode e) m) then top else bot.

Lemma M_get_mode_equiv (e: Event) (m: Mode):
  (M m) e <-> (get_mode e) = m.
Proof.
  split;
  unfold M; destruct (get_mode e); simpl;
  destruct m; simpl;
  intuition congruence.
Qed.

Lemma M_get_mode_refl (e: Event) (m: Mode):
  [M m] e e <-> (get_mode e) = m.
Proof.
  split; intros H.
  - unfold inj in H. simpl in H.
    destruct H as [_ H].
    apply M_get_mode_equiv. auto.
  - split; auto.
    apply M_get_mode_equiv. auto.
Qed.

Definition Mse (m: Mode) : dset Event :=
  fun e =>
    if (stronger_or_eq_mode (get_mode e) m) then top else bot.

(*
(** Every event is in relation [(E_eqmode m)] with itself if and only if it has 
mode [m] *)

Definition E_eqmode (m: Mode) : rlt Event :=
  fun x => fun y => (x = y) /\
                    (get_mode x) = m.

Definition 

(** Every write event is in relation [(W_eqmode m)] with itself if and only if it
has mode [m] *)

Definition W_eqmode (m: Mode) : rlt Event :=
  [W] ⋅ (E_eqmode m).

(** Every fence event is in relation [(F_eqmode m)] with itself if and only if it
has mode [m] *)

Definition F_eqmode (m: Mode) : rlt Event :=
  [F] ⋅ (E_eqmode m).

(** Every read event is in relation [(R_eqmode m)] with itself if and only if it
has mode [m] *)

Definition R_eqmode (m: Mode) : rlt Event :=
  [R] ⋅ (E_eqmode m).

(** Every event is in relation [(E_seqmode m)] with itself if and only if it has
a mode strong or equal to [m] *)

Definition E_seqmode (m: Mode) : rlt Event :=
  fun x => fun y => (x = y) /\
                    stronger_or_eq_mode (get_mode x) m.

Lemma e_seqmode_refl : forall x m m',
  (get_mode x) = m' ->
  stronger_or_eq_mode m' m ->
  (E_seqmode m) x x.
Proof.
  intros x m m' Hmode Hstr.
  split; auto. rewrite Hmode. auto.
Qed.

(** Every write event is in relation [(W_seqmode m)] with itself if and only if 
it has a mode strong or equal to [m] *)

Definition W_seqmode (m: Mode) : rlt Event :=
  [W] ⋅ (E_seqmode m).

(** Every read event is in relation [(R_seqmode m)] with itself if and only if 
it has a mode strong or equal to [m] *)

Definition R_seqmode (m: Mode) : rlt Event :=
  [R] ⋅ (E_seqmode m).

(** Every fence event is in relation [(F_seqmode m)] with itself if and only if
it has a mode stronger or equal to [m] *)

Definition F_seqmode (m: Mode) : rlt Event :=
  [F] ⋅ (E_seqmode m).
*)

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
    apply M_get_mode_equiv. auto.
  - split; [|apply M_get_mode_equiv]; auto.
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
  - apply M_get_mode_equiv. auto.
  - apply M_get_mode_equiv. rewrite H4 in H5. auto.
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

Lemma res_neq_incl (m:Mode) (r1: rlt Event):
  (res_neq_mode m r1) ≦ r1.
Proof.
  unfold res_neq_mode. kat.
Qed.

(** ** Sequenced before *)

(** A sequenced before relation is valid if it is a strict partial order and
if for each location, there is an initialisation event that sets the location
to 0, is sequenced before all the events of the program and after no events *)

Definition valid_sb (evts: Ensemble Event) (sb : rlt Event) : Prop :=
  (linear_strict_order sb evts) /\
  (Included _ (udr sb) (evts)) /\
  (forall (l : Loc),
  exists (e: Event),
    (get_loc e) = Some l /\
    (get_val e) = Some O /\
    ~(In _ (ran sb) e) /\
    forall e', In _ (ran sb) e' -> sb e e').

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
  (Included _ (udr rmw) evts).

(** ** Reads-from relation *)

(** The reads-from relation connects a write and a read events of the same value to
the same location and is such that if [rf r1 w] and [rf r2 w], then [r1 = r2].
To put it more simply, the read-from relation connects every read event to
exactly one write event that wrote the value it reads
*)

Definition valid_rf (evts : Ensemble Event) (rf : rlt Event) : Prop :=
  (forall w r, 
    rf w r ->
    (In _ evts w /\
     In _ evts r /\
     (get_loc w) = (get_loc r) /\
     (get_val w) = (get_val r))) /\
  (Included _ (udr rf) evts) /\
  ([W]⋅rf⋅[R] = rf) /\
  (forall w1 w2 r,
    (rf w1 r) /\ (rf w2 r) -> w1 = w2).

(** The sequence of read-from and of the converse of read-from is a reflexive
relation. This means that each read can read the value of only one write *)

Lemma rf_unique (evts: Ensemble Event) (rf: rlt Event):
  valid_rf evts rf ->
  rf⋅rf° ≦ 1.
Proof.
  intros Hval x y [z Hrf Hrfconv].
  simp_cnv Hrfconv.
  destruct Hval as [_ [_ [_ H]]].
  generalize (H x y z). 
  intuition auto.
Qed.

Lemma rf_incl_same_loc (evts: Ensemble Event) (rf r: rlt Event):
  valid_rf evts rf ->
  rf ≦ r ->
  rf ≦ res_eq_loc r.
Proof.
  intros Hval Hincl x y Hrf.
  destruct Hval as [Hval _].
  destruct (Hval _ _ Hrf) as [_ [_ [Hsameloc _]]].
  split; auto. apply Hincl; auto.
Qed.

Lemma rf_valid_test_right (evts: Ensemble Event) (rf: rlt Event) (t: dset Event):
  valid_rf evts rf ->
  valid_rf evts (rf ⋅ [t]).
Proof.
  intros Hval.
  unfold valid_rf in *.
  destruct Hval as [Hv1 [Hv4 [Hv2 Hv3]]].
  split;[|split;[|split]].
  - intros w r.
    intros [z Hrf [Heq _]].
    rewrite Heq in Hrf.
    destruct (Hv1 w r Hrf) as [? [? [? ?]]].
    split; [|split;[|split]]; auto.
  - transitivity (udr rf); auto.
    apply test_right_udr.
  - rewrite <- Hv2 at 2. apply ext_rel. kat.
  - intros w1 w2 r. intros [Hw1 Hw2].
    apply (Hv3 w1 w2 r).
    split.
    + destruct Hw1 as [z H [Heq _]]. rewrite Heq in H. auto.
    + destruct Hw2 as [z H [Heq _]]. rewrite Heq in H. auto.
Qed.

Lemma rf_valid_test_left (evts: Ensemble Event) (rf: rlt Event) (t: dset Event):
  valid_rf evts rf ->
  valid_rf evts ([t] ⋅ rf).
Proof.
  intros Hval.
  unfold valid_rf in *.
  destruct Hval as [Hv1 [Hv4 [Hv2 Hv3]]].
  split;[|split;[|split]].
  - intros w r.
    intros [z [Heq _] Hrf].
    rewrite <- Heq in Hrf.
    destruct (Hv1 w r Hrf) as [? [? [? ?]]].
    split; [|split;[|split]]; auto.
  - transitivity (udr rf); auto.
    apply test_left_udr.
  - rewrite <- Hv2 at 2. apply ext_rel. kat.
  - intros w1 w2 r. intros [Hw1 Hw2].
    apply (Hv3 w1 w2 r).
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
  (partial_order mo evts) /\
  (forall l, total_rel (mo_for_loc mo l) evts).

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

Ltac destruct_sb_v H :=
  destruct H as [Hsb_lso [Hsb_in_e Hsbinit]].

Ltac destruct_rmw_v H :=
  destruct H as [Hrmw_vpairs Hrmw_in_e].

Ltac destruct_rf_v H :=
  destruct H as [Hrfco [Hrf_in_e [Hrfwr Hrfun]]].

Ltac destruct_mo_v H :=
  destruct H as [Hmoww [Hmopo Hmotot]].

(** *** Lemmas about valid executions *)

Section ValidExecs.

Variable ex : Execution.
Variable val_exec : valid_exec ex.

(** In a valid execution, the origin of a reads-from is a write event *)

Lemma rf_orig_write x y:
  (rf ex) x y ->
  is_write x.
Proof.
  intros Hrf.
  destruct_val_exec val_exec.
  destruct Hrf_v as [_ [_ [Hrf_v _]]].
  rewrite <- Hrf_v in Hrf.
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
  destruct Hrf_v as [_ [_ [Hrf_v _]]].
  rewrite <- Hrf_v in Hrf.
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
  destruct Hrf_v as [Hrf_v _].
  destruct (Hrf_v x y Hrf) as [_ [_ [Hloc _]]].
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
  destruct Hrf_v as [Hrf_v _].
  apply Hrf_v in Hrf as [Hfin _].
  auto.
Qed.

Lemma rf_dest_evts (x y : Event):
  (rf ex) x y ->
  In _ (evts ex) y.
Proof.
  intros Hrf.
  destruct_val_exec val_exec.
  destruct Hrf_v as [Hrf_v _].
  apply Hrf_v in Hrf as [_ [Hfin _]].
  auto.
Qed.

(** In a valid execution, events related by sequenced-before belong to the set
of events of the execution *)

Lemma sb_orig_evts (x y : Event):
  (sb ex) x y ->
  In _ (evts ex) x.
Proof.
  intros Hsb.
  destruct_val_exec val_exec.
  destruct Hsb_v as [_ [Hsb_v _]].
  apply Hsb_v. left; exists y; auto.
Qed.

Lemma sb_dest_evts (x y : Event):
  (sb ex) x y ->
  In _ (evts ex) y.
Proof.
  intros Hsb.
  destruct_val_exec val_exec.
  destruct Hsb_v as [_ [Hsb_v _]].
  apply Hsb_v. right; exists x; auto.
Qed.

End ValidExecs.
  
(** ** Getters *)

Definition reads (ex: Execution) : Ensemble Event :=
  fun e => (In _ ex.(evts) e) /\ is_read e.

Definition writes (ex: Execution) : Ensemble Event :=
  fun e => (In _ ex.(evts) e) /\ is_write e.

(** ** Completeness *)

(** An execution is complete when it is valid and when every read reads a value
that was written at some point *)

Definition complete_exec (e: Execution) :=
  valid_exec e /\ Included _ (reads e) (ran e.(rf)).