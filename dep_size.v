(* wir denken dass man man bei dem Beweis zu 28.4.2 (1) bei der inneren Induktion eine dependent size induction braucht.

Damit man die folgende Induktionshypothese hat:
  forall V (d' : Gamma |- V <: Q), (size d' < size d) -> Gamma |- V <: T

man hat naemlich im Kontext d : Gamma |- S <: Q und bekommt die derivation von d' : Gamma |- U <: Q durch case analysis auf d.
Deswegen braucht man auch eigentlich keine size induction.
 *)

Require Import Arith Lia.

Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Type) :
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
Proof.
  intros H x. apply H.
  induction (f x).
  - intros y. lia.
  - intros y Hy. apply H.
    intros z Hz. apply IHn. lia.
Qed.

Lemma dep_size_ind {X : Type} {Y : X -> Type} (f : forall x, Y x -> nat) (P : forall x, Y x -> Type) :
  (forall x y, (forall x' y', f x' y' < f x y -> P x' y') -> P x y) -> forall x y, P x y.
Proof.
  intros H x y. apply H.
  induction (f x y).
  - intros x' y'. lia.
  - intros x' y' H'. apply H.
    intros x'' y'' H''. apply IHn. lia.
Qed.

(* size ind mit p = const False? wo geht das kaputt? *)
Goal False.
Proof.
  refine (size_ind (fun x => x) (fun _ => False) _ 1).
  intros x IH.
  (* ok breaks here since we need to prove it for *all* x. It's trivial for everything except 0 but for 0 it does not work. *)
Abort.
