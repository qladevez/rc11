(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

From RelationAlgebra Require Import 
  lattice prop monoid rel kat_tac normalisation kleene kat rewriting.
From RC11 Require Import util.
From RC11 Require Import exec.
Require Import Ensembles.

Open Scope rel_notations.

(** This file defines what it means to be valid on the RC11 memory model *)

Section RC11.

Variable ex: Execution.
Variable Hval: valid_exec ex.

Definition rf := (rf ex).
Definition mo := (mo ex).
Definition sb := (sb ex).
Definition rmw := (rmw ex).
Definition evts := (evts ex).

(** * Derived relations *)

(** ** Reads-before *)

(** A read event [r] reads-before a write event [w] if it reads-from a write
event sequenced before [w] by the modification order. It corresponds to the
from-read relation in some other works on axiomatic memory models. *)

Definition rb :=
  rf ° ⋅ mo.

(** In a valid_execution, two events related by read-before belong to the set of
events of the execution *)

Lemma rb_orig_evts (x y : Event):
  rb x y ->
  In _ evts x.
Proof.
  intros Hrb.
  destruct Hrb as [z Hrf Hmo].
  simp_cnv Hrf.
  eapply rf_dest_evts; eauto.
Qed.

Lemma rb_dest_evts (x y : Event):
  rb x y ->
  In _ evts y.
Proof.
  intros Hrb.
  destruct Hrb as [z Hrf Hmo].
  eapply mo_dest_evts; eauto.
Qed.

Lemma rb_orig_read (x y : Event):
  rb x y ->
  is_read x.
Proof.
  intros Hrb.
  destruct Hrb as [z Hrf Hmo].
  simp_cnv Hrf.
  eapply rf_dest_read; eauto.
Qed.

Lemma rb_dest_write (x y : Event):
  rb x y ->
  is_write y.
Proof.
  intros Hrb.
  destruct Hrb as [z Hrf Hmo].
  eapply mo_dest_write; eauto.
Qed.

Lemma rb_same_loc (x y : Event):
  rb x y ->
  (get_loc x) = (get_loc y).
Proof.
  intros Hrb.
  destruct Hrb as [z Hrf Hmo].
  simp_cnv Hrf.
  apply rf_same_loc in Hrf.
  apply mo_same_loc in Hmo.
  congruence.
  eauto. eauto.
Qed.

(** ** Extended coherence order *)

(** The extended coherence order is the transitive closure of the union of
reads-from, modification order and reads-before. It corresponds to the 
communication relation in some other works on axiomatic memory models *)

Definition eco := (rf ⊔ mo ⊔ rb)^+.

Lemma rf_wr:
  rf ≡ [W] ⋅ rf ⋅ [R].
Proof.
  destruct_val_exec Hval.
  destruct Hrf_v as [_ [_ [Hwr _]]].
  fold rf in Hwr. rewrite Hwr. unfold rf; intuition.
Qed.

Lemma mo_ww:
  mo ≡ [W] ⋅ mo ⋅ [W].
Proof.
  destruct_val_exec Hval.
  destruct Hmo_v as [Hmo _].
  fold mo in Hmo. rewrite Hmo. unfold mo; intuition.
Qed.

Open Scope rel_notations.

Lemma rb_rw:
  rb ≡ [R] ⋅ rb ⋅ [W].
Proof.
  unfold rb.
  rewrite mo_ww.
  rewrite rf_wr.
  ra_normalise.
  rewrite 2injcnv.
  kat.
Qed.

(** We can rewrite [eco] as the union of read-from, modification-order and read-
before sequenced before the reflexive closure of read-from *)

Open Scope rel_notations.

Ltac elim_conflicting_rw :=
  rewrite rf_wr, mo_ww, rb_rw;
  mrewrite rw_0; kat.

Ltac elim_conflicting_wr :=
  rewrite rf_wr, mo_ww, rb_rw;
  mrewrite wr_0; kat.

(** We can reformulation the [eco] relation as a relation that is not a 
reflexive transitive closure *)

Lemma eco_rfmorb_seq_rfref:
  eco = rf ⊔ ((mo ⊔ rb) ⋅ rf?).
Proof.
  unfold eco.
  apply ext_rel. apply eq_as_inclusion. split.
  - kat.
  - apply itr_ind_l1.
    + kat.
    + assert (mo⋅mo ≦ mo) as Hmo_trans.
      { destruct_val_exec Hval. destruct_mo_v Hmo_v.
        destruct Hmopo as [_ [Hmotrans _]].
        unfold "⋅" in Hmotrans. rewrite Hmotrans. ra_normalise. auto. }
    ra_normalise. rewrite Hmo_trans. ra_normalise.
    repeat (try (apply leq_cupx)).
    1, 5, 7: kat.
    (* all: upgrade_to_kat Event. *)
    1, 2, 7: elim_conflicting_rw.
    2, 4, 6, 8: elim_conflicting_wr.
    all: unfold rb.
    all: destruct_val_exec Hval.
    1, 3: mrewrite (rf_unique _ _ Hrf_v).
    3, 4: destruct_mo_v Hmo_v;
          destruct Hmopo as [_ [Hmotrans _]];
          mrewrite Hmotrans.
    all: kat.
Qed.

(** In a valid execution, the read-from relation is irreflexive *)

Lemma rf_irr:
  irreflexive rf.
Proof.
  unfold irreflexive.
  rewrite rf_wr, refl_double, capone.
  mrewrite rw_0. ra.
Qed.

(** In a valid execution, the modification order is irreflexive *)

Lemma mo_irr:
  irreflexive mo.
Proof.
  apply irreflexive_is_irreflexive.
  intros x Hnot.
  destruct_val_exec Hval.
  destruct_mo_v Hmo_v.
  destruct Hmopo as [_ [_ ?]].
  apply (H x). auto.
Qed.

(** In a valid execution, the reads-before relation is irreflexive *)

Lemma rb_irr:
  irreflexive rb.
Proof.
  unfold irreflexive.
  rewrite rb_rw, refl_double, capone.
  mrewrite wr_0. ra.
Qed.

(** We can deduce from this that [eco] is acyclic *)

Lemma eco_acyclic:
  acyclic eco.
Proof.
  unfold acyclic.
  assert (eco^+ = eco). { apply ext_rel; unfold eco; kat. }
  rewrite H.
  rewrite eco_rfmorb_seq_rfref.
  rewrite irreflexive_is_irreflexive.
  ra_normalise.
  repeat (rewrite union_inter).
  repeat (apply leq_cupx).
  - apply rf_irr.
  - rewrite rb_rw.
    rewrite refl_double.
    rewrite capone.
    mrewrite wr_0. ra.
  - destruct_val_exec Hval. destruct_mo_v Hmo_v.
    destruct Hmopo as [_ [_ Hmoirr]].
    rewrite irreflexive_is_irreflexive in Hmoirr.
    auto.
  - unfold rb.
    rewrite refl_shift; auto.
    destruct_val_exec Hval.
    mrewrite (rf_unique _ _ Hrf_v).
    ra_normalise.
    destruct_mo_v Hmo_v. destruct Hmopo as [_ [_ Hmoirr]].
    rewrite irreflexive_is_irreflexive in Hmoirr.
    auto.
  - rewrite rf_wr, mo_ww.
    rewrite refl_shift. auto.
    mrewrite rw_0. ra_normalise.
    auto.
Qed.

(** ** Release sequence *)

(** The release sequence of a write event contains the write itself (if it is
atomic) and all later atomic writes to the same location in the same thread, as 
well as all read-modify-write that recursively read from such writes. *)

Definition rs  :=
  [W] ⋅ sb ? ⋅ [W] ⋅ [Mse Rlx] ⋅ (rf ⋅ rmw) ^*.

(** ** Synchronises with *)

(** A release event [a] synchronises with an acquire event [b] whenever [b] (or,
in case [b] is a fence, a [sb]-prior read) reads from the release sequence of
[a] *)

Definition sw :=
  [Mse Rel] ⋅ ([F] ⋅ sb) ? ⋅ rs ⋅ rf ⋅ [R] ⋅ [Mse Rlx] ⋅ (sb ⋅ [F]) ? ⋅ [Mse Acq].

(** ** Happens-before *)

(** Intuitively, the happens-before relation records when an event is globally
perceived as occurring before another one.
We say that an event happens-before another one if there is a path between the
two events consisting of [sb] and [sw] edges *)

Definition hb  :=
  (sb ⊔ sw)^+.
  
(** ** SC-before *)

Definition scb :=
 sb ⊔  ((res_neq_loc sb) ⋅ hb ⋅ (res_neq_loc sb)) ⊔ (res_eq_loc hb) ⊔ mo ⊔  rb.

(** ** Partial-SC base *)

(** We give a semantic to SC atomics by enforcing the order in which they should
occur *)

Definition psc_base :=
  ([M Sc] ⊔ (([F] ⋅ [M Sc]) ⋅ (hb ?))) ⋅
  (scb) ⋅
  ([M Sc] ⊔ ((hb ?) ⋅ ([F] ⋅ [M Sc]))).

(** ** Partial-SC fence *)

(** We give a semantic to SC fences by enforcing the order in which they should
occur *)

Definition psc_fence :=
  [F] ⋅ [M Sc] ⋅ (hb ⊔ (hb ⋅ eco ⋅ hb)) ⋅ [F] ⋅ [M Sc].

(** ** Partial SC *)

Definition psc :=
  psc_base ⊔ psc_fence.

(** * RC11-consistency *)

(** ** Coherence *)

(** The coherence condition is also called SC-per-location. It guarantees that,
if we consider only the events on one location in the execution, the subset of
the execution is sequentially consistent. In practice, it forbids a set of 
patterns in executions. These patterns are detailed in proposition 1 of section
3.4 in the article, and we prove that they are indeed forbidden by the coherence
condition *)

Definition coherence :=
  forall x, ~(hb ⋅ eco ?) x x.
  

(** In a coherent execution, [hb] is irreflexive. This means that an event
should not occur before itself. *)

Lemma coherence_irr_hb:
  coherence -> (forall x, ~hb x x).
Proof.
  intros H x Hnot.
  apply (H x). exists x.
  - auto.
  - right. simpl; auto.
Qed.

(** In a coherent execution, [rf];[hb] is irreflexive. This means that an event
should not read a value written by a write event occuring in the future. *)

Lemma coherence_no_future_read:
  coherence -> (forall x, ~ (rf ⋅ hb) x x).
Proof.
  intros H x Hnot.
  destruct Hnot.
  eapply H. exists x.
  - eauto.
  - left. apply tc_incl_itself. left. left. auto.
Qed.

(** In a coherent execution, [mo];[rf];[hb] is irreflexive. This means that a
write [w1] can not occur in modification order before a write [w2], if the value
written by [w2] was read by a read event sequenced before [w1]. It forbids the
following pattern in executions:

<<
     rf
 Wx----->Rx
 ^        |
 |        |sb
 |        v
 +------+Wx
     mo
>>
*)

Lemma coherence_coherence_rw:
  coherence -> (forall x, ~ (mo ⋅ rf ⋅ hb) x x).
Proof.
  intros H x Hnot.
  destruct Hnot as [z [z' Hmo Hrf] Hhb].
  apply (H z). exists x.
  - auto.
  - left. apply tc_trans with (y := z'); apply tc_incl_itself.
    + left. right. auto.
    + left. left. auto.
Qed.

(** In a coherent execution, [mo];[hb] is irreflexive. This means that a write
can not modify the memory before a write that precedes it in sequenced-before *)

Lemma coherence_coherence_ww:
  coherence -> (forall x, ~ (mo ⋅ hb) x x).
Proof.
  intros H x Hnot.
  destruct Hnot as [z Hmo Hhb].
  apply (H z). exists x.
  - auto.
  - left. apply tc_incl_itself. left. right. auto.
Qed.

(** In a coherent execution, [mo];[hb];[rf-1] is irreflexive. This means that
a read event cannot read from a write event whose value has been overwritten
by another write, preceding the read in sequenced before. It forbids the
following pattern in executions:

<<
      mo
  Wx----->Wx
  |        |
  |        | sb
  |        v
  +------>Rx
      rf
>>
*)

Lemma coherence_coherence_wr:
  coherence -> (forall x, ~ (mo ⋅ hb ⋅ rf°) x x).
Proof.
  intros H x Hnot.
  destruct Hnot as [z [y Hmo Hhb] Hinvrf].
  apply (H y). exists z.
  - auto.
  - left. apply tc_incl_itself.
    right.
    exists x; auto.
Qed.

(** In a coherent execution, [mo];[rf];[hb];[rf-1] is irreflexive. This means
that if two reads following each other in sequenced-before read values written
by two write events, these two write events must appear in the same order in the
modification order. We forbid the following pattern in executions:

<<
        rf
   Wx-------->Rx
   ^           |
 mo|           |sb
   |           v
   Wx+------->Rx
        rf
>>
*)

Lemma coherence_coherence_rr:
  coherence -> (forall x, ~ (mo ⋅ rf ⋅ hb ⋅ rf°) x x).
Proof.
  intros H x Hnot.
  destruct Hnot as [w [y' [z Hmo Hrf] Hhb] Hinvr].
  apply (H y'). exists w.
  - auto.
  - left. apply tc_trans with (y := z); apply tc_incl_itself.
    + right. exists x; auto.
    + left. left. auto.
Qed.

(** The coherence condition is equivalent to the uniproc condition in some other
memory models *)

Theorem coherence_is_uniproc:
  coherence -> irreflexive (sb ⋅ eco).
Proof.
  intros Hco.
  apply seq_refl_incl_left with (r3 := hb).
  - unfold sb, hb. kat.
  - rewrite eco_rfmorb_seq_rfref.
    unfold irreflexive.
    ra_normalise.
    repeat (rewrite union_inter).
    repeat (apply leq_cupx).
    + pose proof (coherence_no_future_read Hco).
      rewrite irreflexive_is_irreflexive in H. unfold irreflexive in H.
      apply refl_shift in H. auto.
    + pose proof (coherence_coherence_wr Hco).
      rewrite irreflexive_is_irreflexive in H. unfold irreflexive in H.
      apply refl_shift in H. rewrite dotA in H. apply refl_shift in H.
      fold rb in H. auto.
    + pose proof (coherence_coherence_ww Hco).
      rewrite irreflexive_is_irreflexive in H. unfold irreflexive in H.
      apply refl_shift in H. auto.
    + pose proof (coherence_coherence_rr Hco).
      rewrite irreflexive_is_irreflexive in H. unfold irreflexive in H.
      do 2 (apply refl_shift in H; repeat (rewrite dotA in H)).
      unfold rb. repeat (rewrite dotA). auto.
    + pose proof (coherence_coherence_rw Hco).
      rewrite irreflexive_is_irreflexive in H. unfold irreflexive in H.
      apply refl_shift in H. rewrite dotA in H. auto.
Qed.

(** ** Atomicity *)

(** Atomicity ensures that the read and the write composing a RMW pair are
adjacent in [eco]: there is no write event in between *)

Definition atomicity :=
  forall x y, ~ (rmw ⊓ (rb ⋅ mo)) x y.

(** ** SC *)

(** The SC condition gives a semantic to SC atomics and fences in executions. It
is defined. It is defined  *)

Definition SC :=
  acyclic psc.

(** ** No-thin-air *)

(** We want to forbid out-of-thin-air, which means excluding executions where
the value written by a write event depends on the value read by a read event,
which reads from this same write event. *)

Definition no_thin_air :=
  acyclic (sb ⊔ rf).

(** ** RC11-consistent executions *)

(** An execution is RC11-consistent when it verifies the four conditions we just
defined *)

Definition rc11_consistent :=
  coherence /\atomicity /\ SC /\ no_thin_air.

(** * SC-consistent executions *)

(** An execution is SC-consistent if:

- The execution respects the atomicity condition
- The communication relation [eco] is compatible with the program order.
*)

Definition sc_consistent :=
  atomicity /\ acyclic (sb ⊔ rf ⊔ mo ⊔ rb).

End RC11.