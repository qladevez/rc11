(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

From RC11 Require Import util.
From RC11 Require Import exec.

Import RelNotations.

Set Implicit Arguments.

(** This file defines what it means to be valid on the RC11 memory model *)

(** * Derived relations *)

(** ** Reads-before *)

(** A read event [r] reads-before a write event [w] if it reads-from a write
event sequenced before [w] by the modification order. It corresponds to the
from-read relation in some other works on axiomatic memory models. *)

Definition rb (exec: Execution) :=
  rel_seq (inv_strict exec.(rf)) exec.(mo).

(** ** Extended coherence order *)

(** The extended coherence order is the transitive closure of the union of
reads-from, modification order and reads-before. It corresponds to the 
communication relation in some other works on axiomatic memory models *)

Definition eco (exec: Execution) :=
  tc (rel_union exec.(rf) (rel_union exec.(mo) (rb exec))).

(** ** Release sequence *)

(** The release sequence of a write event contains the write itself (if it is
atomic) and all later atomic writes to the same location in the same thread, as 
well as all read-modify-write that recursively read from such writes. *)

Definition rs (exec: Execution) :=
  W ;; (res_eq_loc exec.(sb) ?) ;; (W_seqmode Rlx) ;; 
    ((exec.(rf) ;; exec.(rmw)) **).

(** ** Synchronises with *)

(** A release event [a] synchronises with an acquire event [b] whenever [b] (or,
in case [b] is a fence, a [sb]-prior read) reads from the release sequence of
[a] *)

Definition sw (exec: Execution) :=
  (E_seqmode Rel) ;; ( (F ;; exec.(sb)) ?) ;; (rs exec) ;; exec.(rf) ;;
    (R_seqmode Rlx) ;; ((exec.(sb) ;; F) ?) ;; (E_seqmode Acq).

(** ** Happens-before *)

(** Intuitively, the happens-before relation records when an event is globally
perceived as occurring before another one.
We say that an event happens-before another one if there is a path between the
two events consisting of [sb] and [sw] edges *)

Definition hb (exec: Execution) :=
  (rel_union exec.(sb) (sw exec))⁺.
  
(** ** SC-before *)

Definition scb (exec: Execution) :=
  rel_union exec.(sb)
 (rel_union ((res_neq_loc exec.(sb)) ;; (hb exec) ;; (res_neq_loc exec.(sb)))
 (rel_union (res_eq_loc (hb exec))
 (rel_union exec.(mo) (rb exec)))).

(** ** Partial-SC base *)

(** We give a semantic to SC atomics by enforcing the order in which they should
occur *)

Definition psc_base (exec: Execution) :=
  (rel_union (E_eqmode Sc) ((F_eqmode Sc) ;; ((hb exec) ?))) ;;
  (scb exec) ;;
  (rel_union (E_eqmode Sc) (((hb exec) ?) ;; (F_eqmode Sc))).  

(** ** Partial-SC fence *)

(** We give a semantic to SC fences by enforcing the order in which they should
occur *)

Definition psc_fence (exec: Execution) :=
  (F_eqmode Sc) ;;
  (rel_union (hb exec) ((hb exec) ;; (eco exec) ;; (hb exec))) ;;
  (F_eqmode Sc).

(** ** Partial SC *)

Definition psc (exec: Execution) :=
  rel_union (psc_base exec) (psc_fence exec).

(** * RC11-consistency *)

(** ** Coherence *)

(** The coherence condition is also called SC-per-location. It guarantees that,
if we consider only the events on one location in the execution, the subset of
the execution is sequentially consistent. In practice, it forbids a set of 
patterns in executions. These patterns are detailed in proposition 1 of section
3.4 in the article, and we prove that they are indeed forbidden by the coherence
condition *)

Definition coherence (exec: Execution) :=
  forall x, ~(hb exec ;; ((eco exec) ?)) x x.

(** In a coherent execution, [hb] is irreflexive. This means that an event
should not occur before itself. *)

Lemma coherence_irr_hb:
  forall ex, (coherence ex) -> (forall x, ~ (hb ex) x x).
Proof.
  intros ex H x Hnot. unfold coherence, rel_seq, not in H.
  apply (H x). exists x; split.
  - auto.
  - apply maybe_reflexive.
Qed.

(** In a coherent execution, [rf];[hb] is irreflexive. This means that an event
should read a value written by a write event occuring in the future. *)

Lemma coherence_no_future_read:
  forall ex, (coherence ex) -> (forall x, ~ (ex.(rf) ;; (hb ex)) x x).
Proof.
  intros ex H x Hnot.
  destruct Hnot as [z Hnot].
  apply (H z). exists x. destruct Hnot; split.
  - auto.
  - unfold eco, rel_union, maybe. left.
    apply trc_step. auto.
Qed.

(** In a coherent execution, [mo];[rf];[hb] is irreflexive. This means that a
write [w1] can not occur in modification order before a write [w2], if the value
written by [w2] was read by a read event sequenced before [w1]. It forbids the
following pattern in executions:

<<
     rf
 Wx+---->Rx
 ^        +
 |        |sb
 |        v
 +------+Wx
     mo
>>
*)

Lemma coherence_coherence_rw:
  forall ex, (coherence ex) -> (forall x, ~ (ex.(mo) ;; ex.(rf) ;; (hb ex)) x x).
Proof.
  intros ex H x Hnot.
  destruct Hnot as [z [Hmo [z' [Hr Hhb]]]].
  apply (H z'). exists x; split.
  - auto.
  - unfold eco, rel_union, maybe. left.
    apply trc_ind with (z := z); apply trc_step; auto.
Qed.

(** In a coherent execution, [mo];[hb] is irreflexive. This means that a write
can not modify the memory before a write that precedes it in sequenced-before *)

Lemma coherence_coherence_ww:
  forall ex, (coherence ex) -> (forall x, ~ (ex.(mo) ;; (hb ex)) x x).
Proof.
  intros ex H x Hnot.
  destruct Hnot as [z [Hmo Hhb]].
  apply (H z). exists x; split.
  - auto.
  - unfold eco, rel_union, maybe. left.
    apply trc_step. auto.
Qed.

(** In a coherent execution, [mo];[hb];[rf-1] is irreflexive. This means that
a read event cannot read from a write event whose value has been overwritten
by another write, preceding the read in sequenced before. It forbids the
following pattern in executions:

<<
      mo
  Wx+---->Wx
  +        +
  |        | sb
  |        v
  +------>Rx
      rf
>>
*)

Lemma coherence_coherence_wr:
  forall ex, 
    (coherence ex) -> 
    (forall x, ~ (ex.(mo) ;; (hb ex) ;; (inv_strict ex.(rf))) x x).
Proof.
  intros ex H x Hnot.
  destruct Hnot as [z [Hmo [y [Hhb Hinvrf]]]].
  apply (H z). exists y; split.
  - auto.
  - left.
    apply trc_step. right. right.
    unfold rb, rel_seq. exists x. auto.
Qed.

(** In a coherent execution, [mo];[rf];[hb];[rf-1] is irreflexive. This means
that if two reads following each other in sequenced-before read values written
by two write events, these two write events must appear in the same order in the
modification order. We forbid the following pattern in executions:

<<
        rf
   Wx+------->Rx
   ^           +
 mo|           |sb
   +           v
   Wx+------->Rx
        rf
>>
*)

Lemma coherence_coherence_rr:
  forall ex,
    (coherence ex) ->
    (forall x, ~ (ex.(mo) ;; ex.(rf) ;; (hb ex) ;; (inv_strict ex.(rf))) x x).
Proof.
  intros ex H x Hnot.
  destruct Hnot as [w [Hmo [y [Hrf [z [Hhb Hinvrf]]]]]].
  apply (H y). exists z; split.
  - auto.
  - left. apply trc_ind with (z := w); apply trc_step.
    + right. right. exists x; split; auto.
    + left. auto.
Qed.

(** ** Atomicity *)

(** Atomicity ensures that the read and the write composing a RMW pair are
adjacent in [eco]: there is no write event in between *)

Definition atomicity (exec: Execution) :=
  forall x y, ~ (rel_inter exec.(rmw) ((rb exec) ;; exec.(mo))) x y.

(** ** SC *)

(** The SC condition gives a semantic to SC atomics and fences in executions. It
is defined. It is defined  *)

Definition SC (exec: Execution) :=
  acyclic (psc exec).

(** ** No-thin-air *)

(** We want to forbid out-of-thin-air, which means excluding executions where
the value written by a write event depends on the value read by a read event,
which reads from this same write event. *)

Definition no_thin_air (exec: Execution) :=
  acyclic (rel_union exec.(sb) exec.(rf)).

(** ** RC11-consistent executions *)

(** An execution is RC11-consistent when it verifies the four conditions we just
defined *)

Definition rc11_consistent (exec: Execution) :=
  (coherence exec) /\
  (atomicity exec) /\
  (SC exec) /\
  (no_thin_air exec).

(** * SC-consistent executions *)

(** An execution is SC-consistent if:

- The execution respects the atomicity condition
- The communication relation [eco] is compatible with the program order.
*)

Definition sc_consistent (exec: Execution) :=
  (atomicity exec) /\
  (acyclic (rel_union exec.(sb)
           (rel_union exec.(rf)
           (rel_union exec.(mo)
                      (rb exec))))).