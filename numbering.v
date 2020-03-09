(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

From RelationAlgebra Require Import 
  lattice prop monoid rel kat_tac normalisation kleene kat rewriting.
Require Import Ensembles.
Require Import Lia.
From RC11 Require Import util.
From RC11 Require Import exec.
From RC11 Require Import prefix.
From RC11 Require Import conflict.

(** This file defines the notion of numbering on the events of an execution. *)

(** ** Definition *)

(** A valid numbering on an execution assigns to each event of the execution a
distinct number such that, if two events are related by the transitive closure
of the union of the sequenced-before and read-from relations of the execution,
then the numbering of the first event is smaller than the numbering of the
second event *)

Module Type Numbering.

Parameter numbering : Execution -> (Event -> nat).

Axiom numbering_injective: forall ex x y, numbering ex x <> numbering ex y.

Axiom numbering_coherent: 
  forall ex x y, ((sb ex) ⊔ (rf ex)) x y ->
                 numbering ex x < numbering ex y.

Lemma numbering_coherent_rtc (ex: Execution) (x y: Event):
  ((sb ex) ⊔ (rf ex))^* x y ->
  numbering ex x <= numbering ex y.
Proof.
  generalize x y.
  clear x y.
  apply rtc_ind.
  - intros x y Hstep. apply numbering_coherent in Hstep. lia.
  - auto.
  - intros x y z _ IH1 _ IH2. lia.
Qed.


Lemma numbering_coherent_tc (ex: Execution) (x y: Event):
  ((sb ex) ⊔ (rf ex))^+ x y ->
  numbering ex x < numbering ex y.
Proof.
  intros [z Hstep Hrtc].
  apply numbering_coherent in Hstep.
  apply numbering_coherent_rtc in Hrtc.
  lia.
Qed.

(** In every execution, there is a last event whose numbering is greater than
the one of all the other events *)

Axiom numbering_bounded :
  forall ex, { e | forall x, numbering ex e >= numbering ex x}.

Definition has_number (ex: Execution) (e: Event) (k:nat) : Prop :=
  numbering ex e = k.

End Numbering.

Module NumberingPrefix (Numbering: Numbering).

Import Numbering.

Definition bounded_exec (ex: Execution) (n: nat) : Execution :=
  {|
    evts := Intersection _ (evts ex) (fun x => numbering ex x <= n);
    sb := (sb ex);
    rmw := (rmw ex);
    rf := (rf ex);
    mo := (mo ex);
  |}.


(** In a valid execution, if two events are related by [sb ex ⊔ rf ex], they 
belong to the events of [ex] *)

Lemma sbrf_in_events (ex: Execution) (x y : Event) :
  valid_exec ex ->
  ((sb ex) ⊔ (rf ex)) x y ->
  In _ (evts ex) x /\
  In _ (evts ex) y.
Proof.
  intros Hval [Hsb | Hrf]; split;
  eauto using sb_orig_evts, sb_dest_evts, rf_orig_evts, rf_dest_evts.
Qed.

(** Any bounding of a valid execution is a prefix of this execution *)

Lemma bounded_exec_is_prefix (ex: Execution) (n: nat) :
  valid_exec ex ->
  prefix (bounded_exec ex n) ex.
Proof.
  intros Hval.
  split; [|split].
  - apply intersection_included_itself.
  - intros x y Hnum.
    generalize (sbrf_in_events _ _ _ Hval Hnum); intros [Hx Hy].
    apply (numbering_coherent _ _ _) in Hnum.
    intros H. destruct H as [y Hevts Hbound]; split.
    + auto.
    + unfold In in *; lia.
  - compute; auto.
Qed.

(** There is a bound high enough so that the bounding of the execution 
corresponds to the execution *)

Lemma bounded_execution_itself_exists (ex: Execution):
  exists k, (bounded_exec ex k) = ex.
Proof.
  destruct (numbering_bounded ex) as [k Hsup].
  exists (numbering ex k). destruct ex.
  unfold bounded_exec. f_equal. simpl.
  apply ext_set. intros x. split; intros H.
  - apply intersection_included_itself in H.
    apply H.
  - split.
    + apply H.
    + unfold In. apply (Hsup x).
Qed.

(** ** Smallest conflicting prefix *)

(** A bound encodes the smallest possible conflicting prefix if all the other
bounds producing a conflicting prefix are bigger *)

Definition smallest_conflicting_bounding (ex: Execution) (bound: nat) :=
  conflicting (bounded_exec ex bound) /\
  (forall n, conflicting (bounded_exec ex n) ->
             n > bound).

Axiom smallest_conflicting_bounding_exists:
  forall ex, conflicting ex ->
             (exists bound, smallest_conflicting_bounding ex bound).

(** The bounding smaller than the smallest conflicting bounding are not 
conflicting *)

Lemma smaller_than_smallest_not_conflicting (ex: Execution) (bound: nat):
  (smallest_conflicting_bounding ex bound) ->
  forall smaller, smaller < bound -> 
                  ~(conflicting (bounded_exec ex smaller)).
Proof.
  intros [_ Hsmallest] smaller Hsmaller Hnot.
  apply Hsmallest in Hnot.
  lia.
Qed.

(** ** Minimal conflicting pair *)

(** If an execution contains conflicts, there is a unique pair of events that
are in conflict and belong to the smallest conflicting prefix of the execution *)

Definition minimal_conflicting_pair (ex: Execution) (bound: nat) (j k: Event) :=
  (smallest_conflicting_bounding ex bound) /\
  (c_events (bounded_exec ex bound) j k).

Lemma mcp_exists (ex: Execution):
  conflicting ex ->
  (exists bound j k, minimal_conflicting_pair ex bound j k).
Proof.
  intros Hconf.
  destruct (smallest_conflicting_bounding_exists _ Hconf) as [bound Hsmallest].
  exists bound.
  destruct Hsmallest as [[j [k Hpreconf]] Hsmallest].
  exists j, k. split; [split|]; auto.
Qed.

(** In a minimal conflicting pair, at least one of the two events is not SC *)

Lemma mcp_not_sc (ex: Execution) (bound: nat) (j k: Event):
  (minimal_conflicting_pair ex bound j k) ->
  ((get_mode j) <> Sc \/ (get_mode k) <> Sc).
Proof.
  intros [_ [[H | H] _]]; [left|right]; auto.
Qed.

(** In a minimal conflicting pair, the events are not connected by (sb U rf)⁺ in
any direction *)

Lemma mcp_sbrf (ex: Execution) (bound: nat) (j k: Event):
  (minimal_conflicting_pair ex bound j k) ->
  (~(((sb ex) ⊔ (res_mode Sc (rf ex)))^+ j k) /\
   ~(((sb ex) ⊔ (res_mode Sc (rf ex)))^+ k j)).
Proof.
  intros [_ [_ H]]. auto.
Qed.

(** In a minimal conflicting pair, the bound is the numbering of the second
conflicting event *)
(*
Lemma mcp_num_snd_evt (ex: Execution) (bound: nat) (j k: Event):
  (minimal_conflicting_pair ex bound j k) ->
  (numbering ex k = bound).
Proof.
  intros [Hscb Hconf].
  destruct (Compare_dec.lt_eq_lt_dec (numbering ex k) bound) as [[Hlt|Heq]|Hgt].
  - exfalso. destruct Hscb as [_ H].
    assert (conflicting (bounded_exec ex (numbering ex k))) as Hconf'
    by (exists j,k; auto).
    apply H in Hconf'. lia.
  - auto.
  - Check c_events.
*)

End NumberingPrefix.
