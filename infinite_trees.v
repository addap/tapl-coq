Require Import Arith Lia List.
Import ListNotations.

(* From TAPL exercise 21.2.2 to proof that vF <<= Trees *)
Inductive Alphabet := Times | Top.
Inductive N := One | Two.

(* trees are functions from sequences of 1/2 to the symbols *,->,T *)
Definition tree := list N -> option Alphabet.
Definition is_def (t: tree) s := t s <> None.
Definition is_undef (t:tree) s := t s = None.

(* notation for tree that is only defined at root *)
Definition tTop : tree := fun s => if s then Some Top else None.

(* any tree must satisfy the following two rules *)
Class anyTree (t: tree) :=
  {
  empty_def: is_def t [];
  cut: forall pi n, (is_def t (pi ++ [n])) -> (is_def t pi)
  }.

(* the real trees are coercible to anyTree (i.e. all real trees satsify the anyTree rules)
 * also it satisfies the laws for times and top
 * disregard arrow law for now *)
Class realTree (f: tree) (pi: list N) :=
  {
  real_any :> anyTree f;
  times_law: f pi = Some Times -> is_def f (pi ++ [One]) /\ is_def f (pi ++ [Two]);
  (* arr_law: forall pi, f pi = Some Arr -> is_def f (pi ++ [One]) /\ is_def f (pi ++ [Two]); *)
  top_law: f pi = Some Top -> is_undef f (pi ++ [One]) /\ is_undef f (pi ++ [Two])
  }.

(* lemmas how tTop behaves on empty and non-empty sequences *)
Lemma tTop_nil: is_def tTop [].
Proof.
  cbv. congruence.
Qed.

Lemma tTop_cons: forall n pi, is_undef tTop (n :: pi).
Proof.
  intros. cbv. reflexivity.
Qed.

(* Now we can derive an instance for anyTree tTop, i.e. tTop satisfies the first two rules.
 * After that any goal of the form "anyTree tTop" should be proved automatically by Coq. *)
Instance tTop_anyTree : anyTree tTop.
Proof.
  constructor.
  - apply tTop_nil. 
  - intros [|] [|]; simpl.
    1: intros _; apply tTop_nil.
    all: intros H; specialize (H (tTop_cons _ _)) as [].
Qed.

(* We can also derive an instance for realTree tTop. *)
Instance tTop_realTree: forall pi, @realTree tTop pi.
Proof.
  intros pi.
  constructor.
  - apply tTop_anyTree.
  - intros H. destruct pi.
    + injection H. discriminate.
    + discriminate H.
  - intros H. destruct pi. 
    + split; cbv; reflexivity.
    + discriminate H.
Qed.

(* Notation for a tree with a "x" at the root together with two subtrees. *)
Definition tTimes (t1 t2: tree) : tree :=
  fun s => match s with
        | [] => Some Times
        | One :: s => t1 s
        | Two :: s => t2 s
        end.

(* lemmas how tTimes behaves on empty and non-empty sequences. *)
Lemma tTimes_nil t1 t2: is_def (tTimes t1 t2) [].
Proof.
  cbv. discriminate.
Qed.
Lemma tTimes_cons t1 t2 n s: is_def (tTimes t1 t2) (n::s) -> match n with One => is_def t1 s | Two => is_def t2 s end.
Proof.
  intros H. cbv in H. destruct n; assumption.
Qed.

(* tTimes satsifies the first two tree rules. *)
Instance tTimes_anyTree (t1 t2: tree) (Hany1 : anyTree t1) (Hany2 : anyTree t2) : anyTree (tTimes t1 t2).
Proof.
  constructor.
  - cbv. discriminate.
  - intros [|] [|]; simpl.
    + intros _. apply tTimes_nil.
    + intros _. apply tTimes_nil.
    + intros H1%tTimes_cons. destruct n.
      (* need anyTree t1 to apply cut here, but the goal is resolved automatically because of typeclasses. *)
      all: apply cut in H1; assumption.
    + intros H1%tTimes_cons. destruct n.
      all: apply cut in H1; assumption.
Qed.

(* tTimes also satisfies the other two rules provided the subtrees do. *)
Instance tTimes_realTree (t1 t2: tree) (Hany1 : anyTree t1) (Hreal1 : forall pi, realTree t1 pi) (Hany2: anyTree t2) (Hreal2 : forall pi, realTree t2 pi) : forall pi, realTree (tTimes t1 t2) pi.
Proof.
  constructor.
  - apply tTimes_anyTree; assumption.
  - destruct pi. 
    + intros _. split; cbv.
      * apply Hany1.
      * apply Hany2.
    + cbn. destruct n; intros H1; split.
      all: eapply times_law; assumption.
  - destruct pi.
    + discriminate.
    + cbn. destruct n; intros H1; split.
      all: apply top_law; assumption.
Qed.

(* sets of trees are a predicate on the general type tree *)
Definition treeSet := tree -> Prop.

(* the set of real trees are those for which an instance of the realTree typeclass exists.
 * Seems kind of hacky, is there a better way? *)
(* Definition realTrees : treeSet := fun t => exists (_: forall pi, realTree t pi), True. *)

(* the generating function on trees *)
Definition F (R: treeSet) : treeSet :=
  fun t => (t = tTop) \/ (exists t1 t2, t = (tTimes t1 t2) /\ R t1 /\ R t2).

Module greatest_fixpoint_to_trees.
  (* proof for vF <<= Trees *)

  (* I don't want to properly define the greates fixpoint in Coq because the Cofix datatype would have no relation to F. So we just take the relevant properties as hypotheses. *)
  
  (* the greatest fixpoint is a set of trees *)
  Hypothesis gfix : treeSet.

  (* gfix is consistent *)
  Hypothesis gfix_consistent : forall t, gfix t -> F gfix t.

  (* since gfix is defined by F, any tree in gfix is an anyTree *)
  Hypothesis gfix_anyTree : forall t, gfix t -> anyTree t.

  (* Now we can prove that all trees in the greatest fixpoint satisfy the last two rules.
   * Did not even need size induction *)
  Theorem gfix_subset_trees :
    forall t, gfix t -> (forall pi, realTree t pi).
  Proof.
    intros t Ht. specialize (gfix_consistent _ Ht) as Ht'.
    specialize (gfix_anyTree _ Ht) as Hanyt.
    (* induction on pi is enough. I think because I defined rule 2 differently by just adding one instead of an arbitrary sequence. *)
    induction pi as [|n pi] in t, Ht, Ht', Hanyt |- *;
      destruct Ht' as [HtTop|(t1 & t2 & HtTimes & Ht1 & Ht2)]; subst.
    - apply tTop_realTree.
    - specialize (gfix_anyTree _ Ht1) as Ht1'.
      specialize (gfix_anyTree _ Ht2) as Ht2'.
      constructor.
      + apply tTimes_anyTree; assumption.
      + intros _. split. apply Ht1'. apply Ht2'.
      + discriminate.
    - constructor; [ apply tTop_anyTree | discriminate .. ].
    - specialize (gfix_anyTree _ Ht1) as Ht1'.
      specialize (gfix_anyTree _ Ht2) as Ht2'.
      specialize (gfix_consistent _ Ht1) as HF1.
      specialize (gfix_consistent _ Ht2) as HF2.
      constructor.
      + apply tTimes_anyTree; assumption.
      + destruct n; cbn; intros H; split; apply IHpi; assumption.
      + destruct n; intros H; split; cbn.
        all: apply IHpi; assumption.
  Qed.
  
End greatest_fixpoint_to_trees.

(* to prove the original cut rule we actually need size induction. *)
Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Type) :
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
Proof.
  intros H x. apply H.
  induction (f x).
  - intros y. lia.
  - intros y Hy. apply H.
    intros z Hz. apply IHn. lia.
Qed.

(* necessary for the next lemma to do case analysis on a non-empty list *)
Lemma nempty_ca : forall (n: N) pi, exists m sigma, n :: pi = sigma ++ [m].
Proof.
  intros n pi. revert pi n.
  refine (size_ind (fun pi => length pi) (fun pi => forall n, exists m sigma, n :: pi = sigma ++ [m]) _).
  intros [|n' pi] IH n.
  - exists n, []. reflexivity.
  - assert (length pi < length (n' :: pi)) as Hlen by (cbn; lia).
    specialize (IH pi Hlen n') as (m & sigma & H).
    exists m, (n :: sigma).
    rewrite H. cbn. reflexivity.
Qed.

(* original cut rule with arbitraty sigma. *)
Lemma original_cut (t: tree):
  (forall pi n, (is_def t (pi ++ [n]) -> is_def t pi))
  -> forall pi sigma, (is_def t (pi ++ sigma)) -> is_def t pi.
Proof.
  intros Hcut pi sigma. revert sigma pi.
  refine (size_ind (fun pi => length pi) (fun sigma => forall pi, is_def t (pi ++ sigma) -> is_def t pi) _).
  intros [|n sigma] IH pi H.
  - rewrite app_nil_r in H. assumption.
  - destruct (nempty_ca n sigma) as (n' & sigma' & Hsigma').
    rewrite Hsigma' in H. eapply IH with (y:=sigma').
    assert (length sigma = length sigma') as <-.
    { assert (length (n :: sigma) = length (sigma' ++ [n'])) as Hlen by (rewrite Hsigma'; reflexivity).
      cbn in Hlen. rewrite last_length in Hlen.
      apply Nat.succ_inj, Hlen. } 
    cbn. lia.
    eapply Hcut. rewrite <- app_assoc. apply H.
Qed.
