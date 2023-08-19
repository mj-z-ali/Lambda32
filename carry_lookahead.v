Require Import Classical.
Require Import List.
Import ListNotations.


Notation "¬ P" := (not P) (at level 75, right associativity).


(* Standard Definition of 1-bit carry-out*)
Definition CO (a b c : Prop) : Prop :=
  (a /\ b) \/ (a /\ c) \/ (b /\ c).

(* Above is standard definition. Really, no need to prove it.*)
Theorem CO_Correct :
  forall a b c : Prop,
    CO  a b c <-> 
     (¬a /\ b /\ c) \/ (a /\ ¬b /\ c) \/ (a /\ b /\ ¬c) \/ (a /\ b /\ c).

Proof.
  intros a b c. (* Introduce the propositions *)
  unfold CO .  (* Unfold the definition CO_1BIT  *)
  tauto.
Qed.

(* Standard Definition of S_0 in 1-bit Full-Adder *)
Definition S0 (a b c : Prop) : Prop := 
  (¬a /\ ¬b /\ c) \/ (¬a /\ b /\ ¬c) \/ (a /\ b /\ c) \/ (a /\ ¬b /\ ¬c).

(* S_0 in carry-lookahead adder x2 *)
Definition S0LA (a b c : Prop) : Prop :=
  (¬a /\ ¬b /\ c) \/ (¬a /\ b /\ ¬c) \/ (a /\ b /\ c) \/ (a /\ ¬b /\ ¬c).

Theorem S0LA_Correct :
  forall a b c : Prop,
  S0LA a b c <-> S0 a b c.

Proof.
  reflexivity.
Qed.


(* S_1 in carry-lookahead adder x2 *)
Definition S1LA (a1 a0 b1 b0 c : Prop) : Prop :=
  (c /\ a1 /\ a0 /\ b1) \/ (c /\ a1 /\ b1 /\ b0) \/ (c /\ ¬a1 /\ a0 /\ ¬b1) \/ (c /\ ¬a1 /\ ¬b1 /\ b0) \/ 
  (a1 /\ ¬a0 /\ ¬b1 /\ ¬b0) \/ (¬a1 /\ ¬a0 /\ b1 /\ ¬b0) \/ (¬c /\ a1 /\ ¬b1 /\ ¬ b0) \/ (¬c /\ a1 /\ ¬a0 /\ ¬b1) \/
  (¬c /\ ¬a1 /\ b1 /\ ¬b0) \/ (¬c /\ ¬a1 /\ ¬a0 /\ b1) \/ (¬a1 /\ a0 /\ ¬b1 /\ b0) \/ (a1 /\ a0 /\ b1 /\ b0).

(* S_1 in carry-lookahead should be equivalent to sum of second bits from a and b and the carryout from previous bits *)
Theorem S1LA_Correct : 
  forall a1 a0 b1 b0 c : Prop,
  S1LA a1 a0 b1 b0 c <-> S0 a1 b1 (CO a0 b0 c).

Proof. 
  intros a1 a0 b1 b0 c0.
  unfold S1LA, S0, CO. 
  tauto.
Qed.

(* Carry-out in carry-lookahead adder x2 *)
Definition COLA (a1 a0 b1 b0 c : Prop) : Prop :=
  (c /\ b1 /\ b0) \/ (c /\ a1 /\ a0) \/ (a1 /\ b1) \/ (c /\ a0 /\ b1) \/ (c /\ a1 /\ b0) \/ (a0 /\ b1 /\ b0) \/ (a1 /\ a0 /\ b0).

(* Carry-out in carry-lookahead adder x2 should be equivalent to standard carry-out on 2 bits *)
Theorem COLA_Correct :
  forall a1 a0 b1 b0 c : Prop,
    COLA a1 a0 b1 b0 c <-> CO a1 b1 (CO a0 b0 c).

Proof.
  intros a1 a0 b1 b0 c0.
  unfold COLA, CO.
  tauto.
Qed.

(* Standard carry-out of full-adder *)
Fixpoint FACO (a b : list Prop) (c : Prop) : Prop := 
  match a, b with
  |  a_head :: a_tail, b_head :: b_tail => CO a_head b_head (FACO a_tail b_tail c)
  | _, _ => c
  end.

(* Carry-out of carry-lookahead full-adder *)
Fixpoint FACOLA (a b : list Prop) (c : Prop) : Prop :=
  match a, b with
  | a_head :: a_0 :: a_tail, b_head :: b_0 :: b_tail => COLA a_head a_0 b_head b_0 (FACOLA a_tail b_tail c)
  | _, _ => c
  end.

(* Standard S_0 of full-adder *)
Definition FAS0 (a b : list Prop) (c : Prop) : Prop :=
  match a, b with
  | a_head :: a_tail, b_head :: b_tail => S0 a_head b_head (FACO a_tail b_tail c)
  | _, _ => c
  end.

(* S_0 of carry-lookahead full-adder  *)
Definition FAS0LA (a b : list Prop) (c : Prop) : Prop :=
  match a, b with
  | a_head :: a_tail, b_head :: b_tail => S0LA a_head b_head (FACOLA a_tail b_tail c)
  | _, _ => c
  end.

(* S_1 of carry-lookahead full-adder *)
Definition FAS1LA (a b : list Prop) (c : Prop) : Prop :=
  match a, b with
  | a_head :: a_0 :: a_tail, b_head :: b_0 :: b_tail => S1LA a_head a_0 b_head b_0 (FACOLA a_tail b_tail c)
  | _, _ => c
  end.

(* Validating correctness of carry-lookahead full-adder against the standard full-adder *)

Theorem FACOLA_Correct : 
  forall (a b : list Prop) (c : Prop), 
  length a >= 2 /\ length b >= 2 -> 
  FACOLA a b c <-> FACO a b c.
Proof.
  intros a b c [HlenA HlenB].
Admitted.

Theorem FAS0LA_Correct :
  forall (a b : list Prop) (c : Prop), 
  length a >= 2 /\ length b >= 2 -> 
  FAS0LA a b c <-> FAS0 a b c.
Proof.
  intros a b c [HlenA HlenB].
Admitted.

Theorem FAS1LA_Correct :
  forall (a b : list Prop) (c : Prop), 
  length a >= 2 /\ length b >= 2 -> 
  FAS1LA a b c <-> FAS0 a b c.
Proof.
  intros a b c [HlenA HlenB].
Admitted.

(*
(P(a_k-1, a_k-2, b_k-1, b_k-2, ... P(a_1, a_0, b_1, b_0, c_0) /\ b_k+1 /\ b_k) \/ 
((P(a_k-1, a_k-2, b_k-1, b_k-2, ... P(a_1, a_0, b_1, b_0, c_0) /\ a_k+1 /\ a_k) \/ 
(a_k+1 /\ b+k) \/ 
((P(a_k-1, a_k-2, b_k-1, b_k-2, ... P(a_1, a_0, b_1, b_0, c_0) /\ a_k /\ b_k+1) \/ 
((P(a_k-1, a_k-2, b_k-1, b_k-2, ... P(a_1, a_0, b_1, b_0, c_0) /\ a_k+1 /\ b_k) \/ 
(a_k /\ b_k+1 /\ b_k) \/ 
(a_k+1 /\ a_k /\ b_k)


(a_k+1 /\ b_k+1) \/ 
(a_k+1 /\ [(a_k /\ b_k) \/ (a_k /\ C(a_k-1, b_k-1, C...)) \/ (b_k /\ C(a_k-1, b_k-1, C...)) ] \/ 
(b_k+1 /\ [(a_k /\ b_k) \/ (a_k /\ C(a_k-1, b_k-1, C...)) \/ (b_k /\ C(a_k-1, b_k-1, C...)) ])

*)