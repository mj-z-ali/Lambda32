Require Import Classical.

Notation "¬ P" := (not P) (at level 75, right associativity).


(* Standard Definition of 1-bit carry-out*)
Definition CO (a b c : Prop) : Prop :=
  (a /\ b) \/ (a /\ c) \/ (b /\ c).


Theorem CO_Correct :
  forall a b c : Prop,
    CO a b c <-> 
     (¬a /\ b /\ c) \/ (a /\ ¬b /\ c) \/ (a /\ b /\ ¬c) \/ (a /\ b /\ c).

Proof.
  intros a b c. (* Introduce the propositions *)
  unfold CO.  (* Unfold the definition CO *)
  tauto.
Qed.


