Require Import Classical.
Require Import List.
Import ListNotations.


Notation "¬ P" := (not P) (at level 75, right associativity).


(* Definition of carry-out in a standard full-adder configuration *)
Definition CO (a b c : Prop) : Prop :=
  (a /\ b) \/ (a /\ c) \/ (b /\ c).

(* Theorem to reinforce that our minimal definition of carry-out is the standard *)
Theorem CO_Correct :
  forall a b c : Prop,
    CO  a b c <-> 
     (¬a /\ b /\ c) \/ (a /\ ¬b /\ c) \/ (a /\ b /\ ¬c) \/ (a /\ b /\ c).

Proof.
  intros a b c. (* Introduce the propositions *)
  unfold CO .  (* Unfold the definition CO  *)
  tauto.
Qed.

(* Definition of sum output in a standard full-adder configuration *)
Definition S (a b c : Prop) : Prop := 
  (¬a /\ ¬b /\ c) \/ (¬a /\ b /\ ¬c) \/ (a /\ b /\ c) \/ (a /\ ¬b /\ ¬c).


(* Our carry-look-ahead adder has two sum outputs and a carry-out *)

(* Our definition of the first sum output in a carry-lookahead adder x2 *)
Definition CLAS0 (a b c : Prop) : Prop :=
  (¬a /\ ¬b /\ c) \/ (¬a /\ b /\ ¬c) \/ (a /\ b /\ c) \/ (a /\ ¬b /\ ¬c).

(* First sum output in CLA should be the same as sum output in a standard full-adder *)
Theorem CLAS0_Correct :
  forall a b c : Prop,
  CLAS0 a b c <-> S a b c.

Proof.
  reflexivity.
Qed.


(* Second sum output in our carry-look-ahead adder x2 *)
Definition CLAS1 (a1 a0 b1 b0 c : Prop) : Prop :=
  (c /\ a1 /\ a0 /\ b1) \/ (c /\ a1 /\ b1 /\ b0) \/ (c /\ ¬a1 /\ a0 /\ ¬b1) \/ (c /\ ¬a1 /\ ¬b1 /\ b0) \/ 
  (a1 /\ ¬a0 /\ ¬b1 /\ ¬b0) \/ (¬a1 /\ ¬a0 /\ b1 /\ ¬b0) \/ (¬c /\ a1 /\ ¬b1 /\ ¬ b0) \/ (¬c /\ a1 /\ ¬a0 /\ ¬b1) \/
  (¬c /\ ¬a1 /\ b1 /\ ¬b0) \/ (¬c /\ ¬a1 /\ ¬a0 /\ b1) \/ (¬a1 /\ a0 /\ ¬b1 /\ b0) \/ (a1 /\ a0 /\ b1 /\ b0).

(* A standard 2-series carry-ripple configuration is two full-adders, such that the second FA takes the carry-out of the first as input *)

(* Second sum output in carry-look-ahead should be equivalent to second sum output of a standard 2-series carry-ripple configuration *)
Theorem CLAS1_Correct : 
  forall a1 a0 b1 b0 c : Prop,
  CLAS1 a1 a0 b1 b0 c <-> S a1 b1 (CO a0 b0 c).

Proof. 
  intros a1 a0 b1 b0 c0.
  unfold CLAS1, S, CO. 
  tauto.
Qed.

(* Carry-out in our carry-look-ahead adder x2 *)
Definition CLACO (a1 a0 b1 b0 c : Prop) : Prop :=
  (c /\ b1 /\ b0) \/ (c /\ a1 /\ a0) \/ (a1 /\ b1) \/ (c /\ a0 /\ b1) \/ (c /\ a1 /\ b0) \/ (a0 /\ b1 /\ b0) \/ (a1 /\ a0 /\ b0).

(* Carry-out in our carry-look-ahead adder should be equivalent to carry-out of a standard 2-series carry-ripple configuration *)
Theorem CLACO_Correct :
  forall a1 a0 b1 b0 c : Prop,
    CLACO a1 a0 b1 b0 c <-> CO a1 b1 (CO a0 b0 c).

Proof.
  intros a1 a0 b1 b0 c0.
  unfold CLACO, CO.
  tauto.
Qed.

(* Carry-out of a standard N-bit carry-ripple configuration  *)
Fixpoint CRACO (a b : list Prop) (c : Prop) : Prop := 
  match a, b with
  |  a_head :: a_tail, b_head :: b_tail => CO a_head b_head (CRACO a_tail b_tail c)
  | _, _ => c
  end.

(* Carry-out of our N-bit carry-look-ahead adder *)
Fixpoint CLANCO (a b : list Prop) (c : Prop) : Prop :=
  match a, b with
  | a_head :: a_0 :: a_tail, b_head :: b_0 :: b_tail => CLACO a_head a_0 b_head b_0 (CLANCO a_tail b_tail c)
  | _, _ => c
  end.

(* Sum output of a standard N-bit carry-ripple adder *)
Definition CRAS (a b : list Prop) (c : Prop) : Prop :=
  match a, b with
  | a_head :: a_tail, b_head :: b_tail => S a_head b_head (CRACO a_tail b_tail c)
  | _, _ => c
  end.

(* First sum output of our N-bit carry-look-ahead adder  *)
Definition CLANS0 (a b : list Prop) (c : Prop) : Prop :=
  match a, b with
  | a_head :: a_tail, b_head :: b_tail => CLAS0 a_head b_head (CLANCO a_tail b_tail c)
  | _, _ => c
  end.

(* Second sum output of our N-bit carry-look-ahead adder *)
Definition CLANS1 (a b : list Prop) (c : Prop) : Prop :=
  match a, b with
  | a_head :: a_0 :: a_tail, b_head :: b_0 :: b_tail => CLAS1 a_head a_0 b_head b_0 (CLANCO a_tail b_tail c)
  | _, _ => c
  end.

(* Validating correctness of carry-look-ahead adder against the standard carry-ripple adder *)

Theorem CLANCO_Correct : 
  forall (a b : list Prop) (c : Prop), 
  length a >= 2 /\ length b >= 2 -> 
  CLANCO a b c <-> CRACO a b c.
Proof.
  intros a b c [HlenA HlenB].
Admitted.

Theorem CLANS0_Correct :
  forall (a b : list Prop) (c : Prop), 
  length a >= 2 /\ length b >= 2 -> 
  CLANS0 a b c <-> CRAS a b c.
Proof.
  intros a b c [HlenA HlenB].
Admitted.

Theorem CLANS1_Correct :
  forall (a b : list Prop) (c : Prop), 
  length a >= 2 /\ length b >= 2 -> 
  CLANS1 a b c <-> CRAS a b c.
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