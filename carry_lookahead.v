Require Import Classical.

Notation "¬ P" := (not P) (at level 75, right associativity).


(* Standard Definition of 1-bit carry-out*)
Definition CO_1BIT (a b c : Prop) : Prop :=
  (a /\ b) \/ (a /\ c) \/ (b /\ c).

(* Above is standard definition. Really, no need to prove it.*)
Theorem CO_1BIT_Correct :
  forall a b c : Prop,
    CO_1BIT  a b c <-> 
     (¬a /\ b /\ c) \/ (a /\ ¬b /\ c) \/ (a /\ b /\ ¬c) \/ (a /\ b /\ c).

Proof.
  intros a b c. (* Introduce the propositions *)
  unfold CO_1BIT .  (* Unfold the definition CO_1BIT  *)
  tauto.
Qed.

(*Standard Definition of S_0 in 1-bit Full-Adder*)
Definition S_0_1BIT (a b c : Prop) : Prop := 
  (¬a /\ ¬b /\ c) \/ (¬a /\ b /\ ¬c) \/ (a /\ b /\ c) \/ (a /\ ¬b /\ ¬c).

(*S_0 in carry-lookahead adder x2*)
Definition CLAX2_S_0 (a b c : Prop) : Prop :=
  (¬a /\ ¬b /\ c) \/ (¬a /\ b /\ ¬c) \/ (a /\ b /\ c) \/ (a /\ ¬b /\ ¬c).

Theorem CLAX2_S_0_Correct :
  forall a b c : Prop,
  CLAX2_S_0 a b c <-> S_0_1BIT a b c.

Proof.
  reflexivity.
Qed.


(*S_1 in carry-lookahead adder x2*)
Definition CLAX2_S_1 (a1 a0 b1 b0 c : Prop) : Prop :=
  (c /\ a1 /\ a0 /\ b1) \/ (c /\ a1 /\ b1 /\ b0) \/ (c /\ ¬a1 /\ a0 /\ ¬b1) \/ (c /\ ¬a1 /\ ¬b1 /\ b0) \/ 
  (a1 /\ ¬a0 /\ ¬b1 /\ ¬b0) \/ (¬a1 /\ ¬a0 /\ b1 /\ ¬b0) \/ (¬c /\ a1 /\ ¬b1 /\ ¬ b0) \/ (¬c /\ a1 /\ ¬a0 /\ ¬b1) \/
  (¬c /\ ¬a1 /\ b1 /\ ¬b0) \/ (¬c /\ ¬a1 /\ ¬a0 /\ b1) \/ (¬a1 /\ a0 /\ ¬b1 /\ b0) \/ (a1 /\ a0 /\ b1 /\ b0).

(*S_1 in CLAX2 should be equivalent to sum of second bits from a and b and the carryout from previous bits*)
Theorem CLAX2_S_1_Correct : 
  forall a1 a0 b1 b0 c : Prop,
  CLAX2_S_1 a1 a0 b1 b0 c <-> S_0_1BIT a1 b1 (CO_1BIT a0 b0 c).

Proof. 
  intros a1 a0 b1 b0 c0.
  unfold CLAX2_S_1, S_0_1BIT, CO_1BIT. 
  tauto.
Qed.

(*CO in carry-lookahead adder x2*)
Definition CLAX2_CO (a1 a0 b1 b0 c : Prop) : Prop :=
  (c /\ b1 /\ b0) \/ (c /\ a1 /\ a0) \/ (a1 /\ b1) \/ (c /\ a0 /\ b1) \/ (c /\ a1 /\ b0) \/ (a0 /\ b1 /\ b0) \/ (a1 /\ a0 /\ b0).

(*Carryout in CLAX2 should be equivalent to 2-rounds of 1-bit carryout*)
Theorem CLAX2_CO_Correct :
  forall a1 a0 b1 b0 c : Prop,
    CLAX2_CO a1 a0 b1 b0 c <-> CO_1BIT a1 b1 (CO_1BIT a0 b0 c).

Proof.
  intros a1 a0 b1 b0 c0.
  unfold CLAX2_CO, CO_1BIT.
  tauto.
Qed.






