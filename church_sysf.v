Require Import Arith.
Import Nat.

Definition pred (n: nat) :=
  match n with
  | O => O
  | S n => n
  end.

Definition CNat := forall A, (A -> A) -> A -> A.
Definition c0 : CNat := fun _ s z => z.
Definition c1 : CNat := fun _ s z => s z.
Definition c2 : CNat := fun _ s z => s (s z).

Fixpoint nat_to_cnat (n: nat) : CNat :=
  fun _ s z =>
    match n with
    | O => z
    | S n => s (nat_to_cnat n _ s z)
    end.

Goal c1 = nat_to_cnat 1.
Proof.
  unfold nat_to_cnat, c1. reflexivity.
Qed.

Definition k {A B:Type} (x: A) (y: B) := x.
Definition i {A: Type} (x: A) := x.
Definition cpred : CNat -> CNat :=
  fun (cn: CNat) (A:Type) (s: A -> A) (z: A) => cn ((A -> A) -> A) (fun p q => q (p s)) (k z) i.

Definition cnat_to_nat (cn: CNat) : nat := cn _ S O.

Goal 1 = cnat_to_nat c1.
Proof.
  reflexivity.
Qed.

Lemma nat_cnat : forall n, cnat_to_nat (nat_to_cnat n) = n.
Proof.
  induction n as [|n'].
  - reflexivity.
  - unfold nat_to_cnat. fold nat_to_cnat.
    unfold cnat_to_nat. unfold cnat_to_nat in IHn'. rewrite IHn'.
    reflexivity.
Qed.

Require Import FunctionalExtensionality.

Lemma cnat_nat : forall cn A s z, nat_to_cnat (cnat_to_nat cn) A s z = cn A s z.
Proof.
  enough (forall cn n A s z, n = cnat_to_nat cn -> nat_to_cnat n A s z = cn A s z).
  - intros cn A s z. apply H. reflexivity.
  - intros cn n. induction n as [|n']; unfold cnat_to_nat; intros A s z H.
    + unfold nat_to_cnat.
Admitted.

Definition csucc : CNat -> CNat :=
  fun cn A s z => s (cn A s z).

(* Lemma cpred_csucc : forall cn A s z, cpred (csucc cn) A s z = cn A s z. *)
(* Proof. *)
(*   intros *. unfold csucc, cpred. unfold i. *)
  
Lemma cpred_pred : forall n, cnat_to_nat (cpred (nat_to_cnat n)) = pred n.
Proof.
  induction n as [|n'].
  - reflexivity.
  - 
Abort.
