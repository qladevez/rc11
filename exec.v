(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Ensembles.
From RC11 Require Import util.

Import RelNotations.

Set Implicit Arguments.

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

(** There is a strict partial order on modes such that:

- [Na] is weaker than [Rlx]
- [Rlx] is weaker than [Acq] and [Rel]
- [Acq] and [Rel] are weaker than [AcqRel]
- [AcqRel] is weaker than [Sc]. *)

Definition weaker_mode (m1 m2 : Mode) : Prop :=
  match (m1, m2) with
  | (Na, Na) => False
  | (Na, _) => True
  | (Rlx, Na) | (Rlx, Rlx) => False
  | (Rlx, _) => True
  | (Acq, AcqRel) | (Acq, Sc) => True
  | (Acq, _) => False
  | (Rel, AcqRel) | (Rel, Sc) => True
  | (Rel, _) => False
  | (AcqRel, Sc) => True
  | (AcqRel, _) => False
  | (Sc, _) => False
  end.

Definition stronger_or_eq_mode (m1 m2 : Mode) : Prop :=
  ~(weaker_mode m1 m2).

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

Definition valid_evts (evts: set Event) : Prop :=
  forall e, (In _ evts e) -> valid_mode e.

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

Parameter LE : Rln Event -> Rln Event.

(** A relation is included in its linear extension and this extension is
a strict linear order (i.e. it is total) *)

Parameter OE : forall (s S:set Event) (r:Rln Event),
  Included _ s S ->
  partial_order r s ->
  rel_incl r (LE r) /\
  linear_strict_order (LE r) S.

(** The linear extension of a strict linear order on events is itself *)

Parameter le_lso : forall (s:set Event) (r:Rln Event),
  linear_strict_order r s -> LE r = r.
End OEEvt.

Import OEEvt.

(** * Basic relations *)

(** ** Identity relations *)

(** Every write event is in relation [W] with itself *)

Definition W : Rln Event :=
  fun x => fun y => 
    (x = y) /\ is_write x /\ is_write y.

(** Every read event is in relation [R] with itself *)

Definition R : Rln Event :=
  fun x => fun y => (x = y) /\ is_read x /\ is_read y.

(** Every fence event is in relation [F] with itself *)

Definition F : Rln Event :=
  fun x => fun y => (x = y) /\ is_fence x /\ is_fence y.

(** Every event is in relation [(E_eqmode m)] with itself if and only if it has 
mode [m] *)

Definition E_eqmode (m: Mode) : Rln Event :=
  fun x => fun y => (x = y) /\
                    (get_mode x) = m.

(** Every write event is in relation [(W_eqmode m)] with itself if and only if it
has mode [m] *)

Definition W_eqmode (m: Mode) : Rln Event :=
  rel_seq W (E_eqmode m).

(** Every fence event is in relation [(F_eqmode m)] with itself if and only if it
has mode [m] *)

Definition F_eqmode (m: Mode) : Rln Event :=
  rel_seq F (E_eqmode m).

(** Every read event is in relation [(R_eqmode m)] with itself if and only if it
has mode [m] *)

Definition R_eqmode (m: Mode) : Rln Event :=
  rel_seq R (E_eqmode m).

(** Every event is in relation [(E_seqmode m)] with itself if and only if it has
a mode strong or equal to [m] *)

Definition E_seqmode (m: Mode) : Rln Event :=
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

Definition W_seqmode (m: Mode) : Rln Event :=
  rel_seq W (E_seqmode m).

(** Every read event is in relation [(R_seqmode m)] with itself if and only if 
it has a mode strong or equal to [m] *)

Definition R_seqmode (m: Mode) : Rln Event :=
  rel_seq R (E_seqmode m).

(** Every fence event is in relation [(F_seqmode m)] with itself if and only if
it has a mode stronger or equal to [m] *)

Definition F_seqmode (m: Mode) : Rln Event :=
  rel_seq F (E_seqmode m).
  
(** ** Relations restrictions *)

(** [res_eq_loc r] restricts a relation [r] to the pairs of events that affect 
the same location *)

Definition res_eq_loc (r: Rln Event) :=
  fun x => fun y =>
    r x y /\
    (get_loc x) = (get_loc y).

(** [res_neq_loc r] restricts a relation [r] to the pairs of events that affect 
a different location *)

Definition res_neq_loc (r: Rln Event) :=
  fun x => fun y =>
    r x y /\
    (get_loc x) <> (get_loc y).

(** [res_mode m r] restricts a relation [r] to the pairs of events that have mode
[m] *)

Definition res_mode (m: Mode) (r: Rln Event) :=
  (E_eqmode m) ;; r ;; (E_eqmode m).

Lemma res_mode_conds : forall m r x y,
  (get_mode x) = m /\
  (get_mode y) = m /\
  r x y ->
  (res_mode m r) x y.
Proof.
  intros m r x y [Hfst [Hsnd Hr]].
  exists x; split.
  - split; auto.
  - exists y; split.
    + auto.
    + split; auto.
Qed.

Lemma res_mode_simp : forall m r x y,
  (res_mode m r) x y ->
  (get_mode x) = m /\
  (get_mode y) = m /\
  r x y.
Proof.
  intros m r x y H.
  destruct H as [z [[H0 H1] H2]].
  destruct H2 as [z1 [H3 [H4 H5]]]. 
  repeat (try split).
  - auto.
  - rewrite H4 in H5. auto.
  - rewrite H4 in H3. rewrite <- H0 in H3. auto.
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

Lemma res_mode_rel : forall m r x y,
  (res_mode m r) x y ->
  r x y.
Proof.
  intros m r x y H.
  destruct (res_mode_simp H) as [Hfst [Hsnd Hr]]. auto.
Qed.

(** ** Sequenced before *)

(** A sequenced before relation is valid if it is a strict partial order and
if for each location, there is an initialisation event that sets the location
to 0, is sequenced before all the events of the program and after no events *)

Definition valid_sb (evts: set Event) (sb : Rln Event) : Prop :=
  (linear_strict_order sb evts) /\
  (Included _ (udr sb) (evts)) /\
  (forall (l : Loc),
  exists (e: Event),
    (get_loc e) = Some l /\
    (get_val e) = Some 0 /\
    ~(In _ (dom sb) e) /\
    forall e', In _ (dom sb) e' -> sb e e').

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
 
Definition valid_rmw_pair (sb : Rln Event) (r: Event) (w: Event) : Prop :=
  match (get_mode r, get_mode w) with
  | (Rlx, Rlx) | (Acq, Rlx) | (Rlx, Rel) | (Acq, Rel) | (Sc, Sc) =>
    (is_read r /\
     is_write w /\
     (get_loc r) = (get_loc w) /\
     (imm sb) r w)
  | _ => False
  end.

(** A read-modify-write relation is a set of read-modify-write pairs *)

Definition valid_rmw (sb : Rln Event) (rmw : Rln Event) : Prop :=
  forall r w, rmw r w -> valid_rmw_pair sb r w.

(** ** Reads-from relation *)

(** The reads-from relation connects a write and a read events of the same value to
the same location and is such that if [rf r1 w] and [rf r2 w], then [r1 = r2].
To put it more simply, the read-from relation connects every read event to
exactly one write event that wrote the value it reads
*)

Definition valid_rf (evts : set Event) (rf : Rln Event) : Prop :=
  (forall w r, 
    rf w r ->
    (In _ evts w /\
     In _ evts r /\
     is_write w /\
     is_read r /\
     (get_loc w) = (get_loc r) /\
     (get_val w) = (get_val r))) /\
  (forall w1 w2 r,
    (rf w1 r) /\ (rf w2 r) -> w1 = w2).

(** ** Modification order *)

(** The modification order is a strict partial order on the write events, which 
is the disjoint union of total orders on the write events to a specific location
for each location.
It correponds to write serialisation in some other works on axiomatic memory
models.
*)

Definition mo_for_loc (mo : Rln Event) (l : Loc) : Rln Event :=
  fun w1 => fun w2 =>
    mo w1 w2 /\
    (get_loc w1) = (Some l) /\
    (get_loc w2) = (Some l).

Definition valid_mo (evts: set Event) (mo : Rln Event) : Prop :=
  (forall w1 w2, mo w1 w2 ->
    In _ evts w1 /\
    In _ evts w2 /\
    is_write w1 /\
    is_write w2) /\
  (forall l, linear_strict_order (mo_for_loc mo l) evts).


(** * Executions *)

(** ** Validity *)

(** An execution is:
- A set of events with valid modes
- A valid sequenced-before relation on these events
- A valid reads-from relation on these events
- A valid modification order on these events
*)

Record Execution : Type := mkex {
  evts : set Event;
  sb : Rln Event;
  rmw : Rln Event;
  rf : Rln Event;
  mo : Rln Event;
}.

Definition valid_exec (e: Execution) : Prop :=
  (* valid events mode *)
  valid_evts e.(evts) /\
  (* sequenced-before is valid *)
  valid_sb e.(evts) e.(sb) /\
  (* read-modify-write is valid *)
  valid_rmw e.(sb) e.(rmw) /\
  (* reads-from is valid *)
  valid_rf e.(evts) e.(rf) /\
  (* modification order is valid *)
  valid_mo e.(evts) e.(mo).
 
Ltac destruct_val_exec H :=
  destruct H as [Hevts_v [Hsb_v [Hrmw_v [Hrf_v Hmo_v]]]].

(** *** Lemmas about valid executions *)

(** In a valid execution, the origin of a reads-from is a write event *)

Lemma rf_orig_write : forall ex x y,
  valid_exec ex ->
  (rf ex) x y ->
  is_write x.
Proof.
  intros ex x y Hval Hrf.
  destruct_val_exec Hval.
  destruct Hrf_v as [Hrf_v _].
  destruct (Hrf_v x y Hrf) as [_ [_ [Hw _]]].
  auto.
Qed.

Lemma rf_dest_read : forall ex x y,
  valid_exec ex ->
  (rf ex) x y ->
  is_read y.
Proof.
  intros ex x y Hval Hrf.
  destruct_val_exec Hval.
  destruct Hrf_v as [Hrf_v _].
  destruct (Hrf_v x y Hrf) as [_ [_ [_ [Hw _]]]].
  auto.
Qed.

Lemma rf_same_loc : forall ex x y,
  valid_exec ex ->
  (rf ex) x y ->
  (get_loc x) = (get_loc y).
Proof.
  intros ex x y Hval Hrf.
  destruct_val_exec Hval.
  destruct Hrf_v as [Hrf_v _].
  destruct (Hrf_v x y Hrf) as [_ [_ [_ [_ [H _]]]]].
  auto.
Qed.
  
(** ** Getters *)

Definition reads (ex: Execution) : set Event :=
  fun e => (In _ ex.(evts) e) /\ is_read e.

Definition writes (ex: Execution) : set Event :=
  fun e => (In _ ex.(evts) e) /\ is_write e.

(** ** Completeness *)

(** An execution is complete when it is valid and when every read reads a value
that was written at some point *)

Definition complete_exec (e: Execution) :=
  valid_exec e /\ Included _ (reads e) (ran e.(rf)).