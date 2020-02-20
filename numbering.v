(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Ensembles.
Require Import Lia.
From RC11 Require Import util.
From RC11 Require Import exec.
From RC11 Require Import rc11.
From RC11 Require Import prefix.
From RC11 Require Import conflict.

Import RelNotations.

(** This file defines the notion of numbering on the events of an execution. *)

(** * Definition *)

(** A valid numbering on an execution assigns to each event of the execution a
distinct number such that, if two events are related by the transitive closure
of the union of the sequenced-before and read-from relations of the execution,
then the numbering of the first event is smaller than the numbering of the
second event *)

Module Type Numbering.

Parameter numbering : Execution -> (Event -> nat).

Axiom numbering_injective : forall ex x y, numbering ex x <> numbering ex y.

Axiom numbering_coherent : 
  forall ex x y, ((sb ex) <+> (rf ex)) x y ->
                 numbering ex x < numbering ex y.

Definition has_number (ex: Execution) (e: Event) (k:nat) : Prop :=
  numbering ex e = k.

End Numbering.

(** We can build a prefix of an execution by restricting the events of an
execution to the events with a numbering strictly inferior to a certain bound. 
*)

Module NumberingPrefix (Numbering: Numbering).

Import Numbering.

Definition bounded_exec (ex: Execution) (n: nat) : Execution :=
  {|
    evts := Intersection _ (evts ex) (fun x => numbering ex x < n);
    sb := (sb ex);
    rmw := (rmw ex);
    rf := (rf ex);
    mo := (mo ex);
  |}.

(** In a valid execution, if two events are related by [sb ex <+> rf ex], they 
belong to the events of [ex] *)

Lemma sbrf_in_events (ex: Execution) (x y : Event) :
  valid_exec ex ->
  ((sb ex) <+> (rf ex)) x y ->
  In _ (evts ex) x /\
  In _ (evts ex) y.
Proof.
  intros Hval [Hsb | Hrf]; split.
  - apply sb_orig_evts with (y:=y); auto.
  - apply sb_dest_evts with (x:=x); auto.
  - apply rf_orig_evts with (y:=y); auto.
  - apply rf_dest_evts with (x:=x); auto.
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

(* We should say something about the finiteness of the set of events *)
(*
Lemma bounded_execution_itself_exists (ex: Execution):
  exists k, (bounded_exec ex k) = ex.
*)

(** If there an execution contains conflicts, there is a bounding of size [k] of
the execution such that [k] is the smallest bounding of the execution containing
a conflict *)

Definition smallest_conflicting_bounding (ex: Execution) (bound:nat) :=
  conflicting (bounded_exec ex bound) /\
  (forall n, conflicting (bounded_exec ex n) ->
             n > bound).

Lemma not_exists_scb_implies_forall_not_scb (ex: Execution):
  ~(exists bound, smallest_conflicting_bounding ex bound) <->
  (forall bound, ~(smallest_conflicting_bounding ex bound)).
Proof.
  split; intros H.
  - intros bound Hnot. apply H. exists bound; auto.
  - intros [bound Hnot]. apply (H bound); auto.
Qed.

Lemma exists_smallest_conflicting_bouding (ex: Execution):
  conflicting ex ->
  (exists bound, smallest_conflicting_bounding ex bound).
Proof.
  intros Hconflict.

End NumberingPrefix.
