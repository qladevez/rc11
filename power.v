(* 
A formalisation of the Power memory model.

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Ensembles.
Require Import Classical_Prop.
Require Import Nat.
From RC11 Require Import util.
From RC11 Require Import proprel_classic.
From RelationAlgebra Require Import 
  lattice prop monoid rel kat_tac normalisation kleene kat rewriting.

(** * Power Memory Model *)

(** ** Basic defintions *)

Definition Word := nat.
Definition Loc := Word.
Definition Val := Word.

Inductive Event : Type :=
  | Read (eid: nat) (l: Loc) (v: Val)
  | Write (eid: nat) (l: Loc) (v: Val)
  | LFence (eid: nat)
  | FFence (eid: nat).

Definition loc (e: Event) :=
  match e with
  | Write _ l _ => Some l
  | Read _ l _ => Some l
  | _ => None
  end.

Record Execution : Type := mkex {
  evts : Ensemble Event;
  sb : rlt Event;
  rmw : rlt Event;
  rf : rlt Event;
  mo : rlt Event;
}.

Definition E : prop_set Event := top.

Definition R : prop_set Event :=
  fun e =>
    match e with
    | Read _ _ _ => top
    | _ => bot
    end.

Definition W : prop_set Event :=
  fun e =>
    match e with
    | Write _ _ _ => top
    | _ => bot
    end.

Definition rb (e: Execution) : rlt Event :=
    (rf e)°⋅(mo e).

Definition ext (e: Execution) (r: rlt Event) : rlt Event :=
  fun x y =>
    r x y /\ ~(sb e x y) /\ ~(sb e y x).

Definition int (e: Execution) (r: rlt Event) : rlt Event :=
  fun x y =>
    r x y /\ (sb e x y \/ sb e y x).

Definition same_loc (r: rlt Event) :=
  fun x y => r x y /\ (loc x = loc y).

Definition rfi (e: Execution) := int e (rf e).
Definition rfe (e: Execution) := ext e (rf e).
Definition moe (e: Execution) := ext e (mo e).
Definition rbe (e: Execution) := ext e (rb e).


(** ** Power ppo *)

(** The dependency relations and their properties *)

Hypothesis addr ctrl_isync ctrl data: rlt Event.

Hypothesis addr_re : addr ≦ [R]⋅addr⋅[R ⊔ W].
Hypothesis data_rw : data ≦ [R]⋅data⋅[W].

Definition deps := addr ⊔ ctrl ⊔ data.

(** The ppo relation *)

Definition rdw (e: Execution) := ((rbe e) ⋅ (rfe e)) ⊓ sb e.
Definition detour (e: Execution) := ((moe e) ⋅ (rfe e)) ⊓ sb e.

Definition ii0 (e: Execution) : rlt Event := addr ⊔ data ⊔ (rdw e) ⊔ (rfi e).
Definition ic0 (e: Execution) : rlt Event := bot.
Definition ci0 (e: Execution) : rlt Event := ctrl_isync ⊔ (detour e).
Definition cc0 (e: Execution) : rlt Event := data ⊔ ctrl ⊔ (addr⋅((sb e) ?)) ⊔ (same_loc (sb e)).

Inductive ci (e: Execution): rlt Event := ci_c : (ci0 e ⊔ (ci e⋅ii e) ⊔ (cc e⋅ci e)) ≦ ci e
     with ii (e: Execution): rlt Event := ii_c : (ii0 e ⊔ (ci e ⊔ ((ic e⋅ci e) ⊔ (ii e⋅ii e)))) ≦ ii e
     with cc (e: Execution): rlt Event := cc_c : (cc0 e ⊔ (ci e ⊔ ((ci e⋅ic e) ⊔ (cc e⋅cc e)))) ≦ cc e
     with ic (e: Execution): rlt Event := ic_c : (ic0 e ⊔ (ii e ⊔ cc e ⊔ (ic e⋅cc e ⊔ ii e⋅ic e))) ≦ ic e.

Definition ppo (e: Execution) :=
  [R]⋅ii e⋅[R] ⊔ [R]⋅ic e⋅[W].

Lemma addr_incl_ppo (e: Execution):
  addr ≦ (ppo e).
Proof.
  intros x y H. apply addr_re in H.
  apply simpl_trt_hyp in H as [Hr [Hrel Hrw]].
  destruct Hrw as [Hr'|Hw];[left|right]; simpl_trt.
  - apply ii_c. left. unfold ii0. incl_rel_kat Hrel.
  - apply ic_c. right. left. left.
    apply ii_c. left. unfold ii0. incl_rel_kat Hrel.
Qed.

Lemma data_incl_ppo (e: Execution):
  data ≦ (ppo e).
Proof.
  intros x y H. apply data_rw in H.
  apply simpl_trt_hyp in H as [Hr [Hrel Hw]].
  right; simpl_trt.
  apply ic_c. right. left. left.
  apply ii_c. left. unfold ii0. incl_rel_kat Hrel.
Qed.

End Deps.
