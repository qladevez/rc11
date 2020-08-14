(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

From RelationAlgebra Require Import 
  lattice prop monoid rel kat_tac normalisation kleene kat rewriting.
From RC11 Require Import util proprel_classic.
From RC11 Require Import exec.
Require Import Ensembles Classical_Prop.

Open Scope rel_notations.

(** This file defines what it means to be valid on the RC11 memory model *)

Section RC11.

Variable ex: Execution.

(** * Derived relations *)

(** ** Reads-before *)

(** A read event [r] reads-before a write event [w] if it reads-from a write
event sequenced before [w] by the modification order. It corresponds to the
from-read relation in some other works on axiomatic memory models. *)

Definition rb :=
  (rf ex) ° ⋅ (mo ex).

Lemma rf_wr:
  valid_exec ex ->
  (rf ex) ≡ [W] ⋅ (rf ex) ⋅ [R].
Proof.
  intros Hval.
  destruct_val_exec Hval.
  destruct Hrf_v as [_ [_ [Hwr _]]].
  fold rf in Hwr. rewrite Hwr. unfold rf; intuition.
Qed.

Lemma mo_ww:
  valid_exec ex ->
  (mo ex) ≡ [W] ⋅ (mo ex) ⋅ [W].
Proof.
  intros Hval.
  destruct_val_exec Hval.
  destruct Hmo_v as [Hmo _].
  fold mo in Hmo. rewrite Hmo. unfold mo; intuition.
Qed.

Lemma rb_rw:
  valid_exec ex ->
  rb ≡ [R] ⋅ rb ⋅ [W].
Proof.
  intros Hval.
  unfold rb.
  rewrite (mo_ww Hval).
  rewrite (rf_wr Hval).
  ra_normalise.
  rewrite 2injcnv.
  kat.
Qed.

(** In a valid execution, the sequenced-before relation is irreflexive *)

Lemma sb_irr:
  valid_exec ex ->
  irreflexive (sb ex).
Proof.
  intros Hval.
  apply irreflexive_is_irreflexive.
  destruct_val_exec Hval.
  destruct_sb_v Hsb_v.
  destruct Hsb_lso as [[_ [_ Hsbirr]] _].
  intros x. apply Hsbirr.
Qed.

(** In a valid execution, the read-from relation is irreflexive *)

Lemma rf_irr:
  valid_exec ex ->
  irreflexive (rf ex).
Proof.
  intros Hval.
  unfold irreflexive.
  rewrite (rf_wr Hval), refl_double, capone.
  mrewrite rw_0. ra.
Qed.

(** In a valid execution, the modification order is irreflexive *)

Lemma mo_irr:
  valid_exec ex ->
  irreflexive (mo ex).
Proof.
  intros Hval.
  apply irreflexive_is_irreflexive.
  intros x Hnot.
  destruct_val_exec Hval.
  destruct_mo_v Hmo_v.
  destruct Hmopo as [_ [_ ?]].
  apply (H x). auto.
Qed.

(** In a valid execution, the reads-before relation is irreflexive *)

Lemma rb_irr:
  valid_exec ex ->
  irreflexive rb.
Proof.
  intros Hval.
  unfold irreflexive.
  rewrite (rb_rw Hval), refl_double, capone.
  mrewrite wr_0. ra.
Qed.

(** In a valid_execution, two events related by read-before belong to the set of
events of the execution *)

Lemma rb_orig_evts (x y : Event):
  valid_exec ex ->
  rb x y ->
  In _ (evts ex) x.
Proof.
  intros Hval Hrb.
  destruct Hrb as [z Hrf Hmo].
  simp_cnv Hrf.
  eapply rf_dest_evts; eauto using Hval.
Qed.

Lemma rb_dest_evts (x y : Event):
  valid_exec ex ->
  rb x y ->
  In _ (evts ex) y.
Proof.
  intros Hval Hrb.
  destruct Hrb as [z Hrf Hmo].
  eapply mo_dest_evts; eauto using Hval.
Qed.

(** In a valid execution, an event in the origin of read-before is a read
event *)

Lemma rb_orig_read (x y : Event):
  valid_exec ex ->
  rb x y ->
  is_read x.
Proof.
  intros Hval Hrb.
  destruct Hrb as [z Hrf Hmo].
  simp_cnv Hrf.
  eapply rf_dest_read; eauto using Hval.
Qed.

(** In a valid execution, an event in the destination of read-before is a
write event *)

Lemma rb_dest_write (x y : Event):
  valid_exec ex ->
  rb x y ->
  is_write y.
Proof.
  intros Hval Hrb.
  destruct Hrb as [z Hrf Hmo].
  eapply mo_dest_write; eauto using Hval.
Qed.

(** In a valid execution, two events related by read-before affect the same
location *)

Lemma rb_same_loc (x y : Event):
  valid_exec ex ->
  rb x y ->
  (get_loc x) = (get_loc y).
Proof.
  intros Hval Hrb.
  destruct Hrb as [z Hrf Hmo].
  simp_cnv Hrf.
  apply rf_same_loc in Hrf.
  apply mo_same_loc in Hmo.
  congruence.
  all: eauto using Hval.
Qed.

Variable Hcomp: complete_exec ex.

Lemma Hval: valid_exec ex.
Proof. destruct Hcomp; auto. Qed.

(** ** Extended coherence order *)

(** The extended coherence order is the transitive closure of the union of
reads-from, modification order and reads-before. It corresponds to the 
communication relation in some other works on axiomatic memory models *)

Definition eco := ((rf ex) ⊔ (mo ex) ⊔ rb)^+.

(** We can rewrite [eco] as the union of read-from, modification-order and read-
before sequenced before the reflexive closure of read-from *)

Open Scope rel_notations.

Ltac elim_conflicting_rw :=
  rewrite (rf_wr Hval), (mo_ww Hval), (rb_rw Hval);
  mrewrite rw_0; kat.

Ltac elim_conflicting_wr :=
  rewrite (rf_wr Hval), (mo_ww Hval), (rb_rw Hval);
  mrewrite wr_0; kat.

(** We can reformulation the [eco] relation as a relation that is not a 
reflexive transitive closure *)

Lemma eco_rfmorb_seq_rfref:
  eco = (rf ex) ⊔ (((mo ex) ⊔ rb) ⋅ (rf ex)?).
Proof.
  unfold eco.
  apply ext_rel. apply antisym.
  - apply itr_ind_l1.
    + kat.
    + assert ((mo ex)⋅(mo ex) ≦ (mo ex)) as Hmo_trans.
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
  - kat.
Qed.


(** In a valid execution, the union of sequenced-before, reads-from, 
modification order and reads-before is irreflexive *)

Lemma sbrfmorb_irr:
  irreflexive (sb ex ⊔ rf ex ⊔ mo ex ⊔ rb).
Proof.
  apply irreflexive_union.
  apply irreflexive_union.
  apply irreflexive_union.
  apply (sb_irr Hval).
  apply (rf_irr Hval).
  apply (mo_irr Hval).
  apply (rb_irr Hval).
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
  - apply (rf_irr Hval).
  - rewrite (rb_rw Hval).
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
  - rewrite (rf_wr Hval), (mo_ww Hval).
    rewrite refl_shift. auto.
    mrewrite rw_0. ra_normalise.
    auto.
Qed.

(** ** Release sequence *)

(** The release sequence of a write event contains the write itself (if it is
atomic) and all later atomic writes to the same location in the same thread, as 
well as all read-modify-write that recursively read from such writes. *)

Definition rs  :=
  [W] ⋅ (sb ex) ? ⋅ [W] ⋅ [Mse Rlx] ⋅ ((rf ex) ⋅ (rmw ex)) ^*.

(** ** Synchronises with *)

(** A release event [a] synchronises with an acquire event [b] whenever [b] (or,
in case [b] is a fence, a [sb]-prior read) reads from the release sequence of
[a] *)

Definition sw :=
  [Mse Rel] ⋅ ([F] ⋅ (sb ex)) ? ⋅ rs ⋅ (rf ex) ⋅ [R] ⋅ [Mse Rlx] ⋅ ((sb ex) ⋅ [F]) ? ⋅ [Mse Acq].

(** The synchronises-with relation is included in the transitive closure of the
union of sequenced-before and reads-from *)

Lemma sw_incl_sbrf:
  sw ≦ ((sb ex) ⊔ (rf ex))^+.
Proof.
  unfold sw, rs. rewrite rmw_incl_sb. kat. auto using Hval.
Qed.
  
(** ** Happens-before *)

(** Intuitively, the happens-before relation records when an event is globally
perceived as occurring before another one.
We say that an event happens-before another one if there is a path between the
two events consisting of [sb] and [sw] edges *)

Definition hb  :=
  ((sb ex) ⊔ sw)^+.

(** The happens-before relation is included in the transitive closure of the
union of sequenced-before and reads-from *)

Lemma hb_incl_sbrf:
  hb ≦ ((sb ex) ⊔ (rf ex))^+.
Proof.
  unfold hb. rewrite sw_incl_sbrf. kat.
Qed.
  
(** ** SC-before *)

Definition scb :=
 (sb ex) ⊔  ((res_neq_loc (sb ex)) ⋅ hb ⋅ (res_neq_loc (sb ex))) ⊔ (res_eq_loc hb) ⊔ (mo ex) ⊔  rb.

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
  coherence -> (forall x, ~ ((rf ex) ⋅ hb) x x).
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
  coherence -> (forall x, ~ ((mo ex) ⋅ (rf ex) ⋅ hb) x x).
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
  coherence -> (forall x, ~ ((mo ex) ⋅ hb) x x).
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
  coherence -> (forall x, ~ ((mo ex) ⋅ hb ⋅ (rf ex)°) x x).
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
  coherence -> (forall x, ~ ((mo ex) ⋅ (rf ex) ⋅ hb ⋅ (rf ex)°) x x).
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
  coherence -> irreflexive ((sb ex) ⋅ eco).
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
  forall x y, ~ ((rmw ex) ⊓ (rb ⋅ (mo ex))) x y.

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
  acyclic ((sb ex) ⊔ (rf ex)).

(** ** RC11-consistent executions *)

(** An execution is RC11-consistent when it verifies the four conditions we just
defined *)

Definition rc11_consistent :=
  coherence /\ atomicity /\ SC /\ no_thin_air.

(** Coherence implies that [rmw] is included in [rb] *)

Lemma rc11_rmw_incl_rb:
  rc11_consistent ->
  rmw ex ≦ rb.
Proof.
  intros [Hco _] x y Hrmw.
  unfold coherence in Hco.
  unfold hb, eco in Hco.
  unfold rb. byabsurd.
  destruct (Hco x).
  assert (exists z, (rf ex) z x) as [z Hrf].
  { destruct Hcomp as [_ Hrf].
    unfold ran in Hrf. apply Hrf.
    split.
    - apply (rmw_orig_evts _ Hval _ y Hrmw).
    - apply (rmw_orig_read _ Hval _ y Hrmw).
  }
  destruct (classic (y = z)) as [Hyz|Hyz].
  - apply (rmw_incl_sb _ Hval) in Hrmw.
    rewrite <-Hyz in Hrf.
    exists y.
    + apply tc_incl_itself. left. auto.
    + left. apply tc_incl_itself. left. left. auto.
  - assert (exists l, (get_loc y = Some l) /\ (get_loc z = Some l))
    as [l [Hl1 Hl2]].
    { apply (rf_dest_read _ Hval) in Hrf as Hxw.
      apply (rf_same_loc _ Hval) in Hrf.
      apply (rmw_same_loc _ Hval) in Hrmw.
      rewrite <-Hrmw, Hrf. destruct x.
      - exists l. intuition auto.
      - exists l. intuition auto.
      - simpl in Hxw. intuition auto.
    }
    edestruct (mo_diff_write _ Hval) as [Hmo|Hmo]; eauto.
    + repeat (apply conj).
      * apply (rmw_dest_evts _ Hval x). auto.
      * apply (rmw_dest_write _ Hval x). auto.
      * eauto.
    + repeat (apply conj).
      * apply (rf_orig_evts _ Hval _ x). auto.
      * apply (rf_orig_write _ Hval _ x). auto.
      * auto.
    + exists y.
      { apply (rmw_incl_sb _ Hval) in Hrmw.
        apply (incl_rel_thm Hrmw). kat. }
      left. apply tc_trans with z.
      * apply (incl_rel_thm Hmo). kat.
      * apply (incl_rel_thm Hrf). kat.
    + destruct Hcontr. exists z.
      * apply (incl_rel_thm Hrf). kat.
      * apply (incl_rel_thm Hmo). kat.
Qed.

(** * SC-consistent executions *)

(** An execution is SC-consistent if:

- The execution respects the atomicity condition
- The communication relation [eco] is compatible with the program order.
*)

Definition sc_consistent :=
  atomicity /\ acyclic ((sb ex) ⊔ (rf ex) ⊔ (mo ex) ⊔ rb).

End RC11.