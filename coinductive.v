Require Import Arith Lia.

Module Streams1.
Section Stream.
  Variable A: Type.
  CoInductive stream : Type :=
    Cons : A -> stream -> stream.
End Stream.
Arguments Cons [A].

CoFixpoint zeroes : stream nat := Cons 0 zeroes.
CoFixpoint trues_falses : stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses.

(* We always need some inductive type to recurse on. Evidence that stream has no notion of "smaller" things in a constructor. *)
Fail Fixpoint approx {A} (s:stream A) (n:nat) {struct s} : list A :=
  match n with
  | O => nil
  | S n' =>
    match s with Cons h t => h :: approx t n'
    end
  end.

Fixpoint approx {A} (s:stream A) (n:nat) : list A :=
  match n with
  | O => nil
  | S n' =>
    match s with Cons h t => h :: approx t n'
    end
  end.

Compute approx zeroes 10.
Compute approx trues_falses 10.

(* Fixpoints: consume values of inductive types, arguments to recursive calls must be smaller *)
(* CoFixpoints: produce values of coinductive types, restriction what can be done with the result of corecursive calls. They must always appear under a constructor. *)

Fail CoFixpoint looper : stream nat := looper.

(* a.d. todo, why would approx run forever. Depends on what you mean with forever but I guess the match becomes stuck since s wasn't constructed by a constructor. *)

CoFixpoint map {A B:Type} (f: A -> B) (s:stream A) : stream B :=
  match s with
    Cons h t => Cons (f h) (map f t)
  end.

Fail CoFixpoint filter {A:Type} (f:A -> bool) (s:stream A) : stream A :=
  match s with
    Cons h t => if f h then Cons h (filter f t)
               else filter f t
  end.

CoFixpoint interleave {A:Type} (s1 s2:stream A) : stream A :=
  match s1, s2 with
  | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
  end.

Fail CoFixpoint map' {A B:Type} (f:A -> B) (s:stream A) : stream B :=
  match s with
  | Cons h t => interleave (Cons (f h) (map' f t)) (Cons (f h) (map' f t))
  end.
(* Id we inline interleave we see that it becomes
 Cons h t => Cons (f h) (Cons (f h) (interleave (map' f t) (map' f t)))
 So the corecursive call does not happen directly in a constructor anymore. *)

Definition tl {A:Type} (s:stream A) : stream A :=
  match s with Cons _ s' => s' end.
Fail CoFixpoint bad := tl (Cons 0 bad).
Fail CoFixpoint bad := match (Cons 0 bad) with Cons h t => t end.

CoFixpoint ones : stream nat := Cons 1 ones.
Definition ones' := map S zeroes.
Definition ones'' := Cons 1 ones.

Section stream_eq.
  Variable A: Type.

  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
      stream_eq t1 t2 -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.
Arguments stream_eq [A].

Theorem ones_eq : stream_eq ones ones'.
Proof.
  cofix ones_eq.
Abort.

Definition frob {A:Type} (s:stream A) :=
  match s with Cons h t => Cons h t end.

Theorem frob_eq {A} : forall (s:stream A), s = frob s.
  destruct s. reflexivity.
Qed.

Module subj.
  (* https://www.joachim-breitner.de/blog/726-Coinduction_in_Coq_and_Isabelle *)
  CoInductive natw :=
  | N : natw
  | SS : natw -> natw.

  CoFixpoint infS := SS infS.
  Definition infS' := cofix F := SS F.

  Definition frob (n: natw) :=
    match n with
    | N => N
    | SS x => SS x
    end.

  Lemma frob_eq : forall n, frob n = n.
  Proof.
    unfold frob. intros []; reflexivity.
  Qed.

  Compute infS.
  Compute frob infS.
  Eval simpl in frob_eq infS.
  Fail Check eq_refl : frob infS = infS.
End subj.
                              

Goal ones = ones''.
Proof.
  rewrite (frob_eq ones). unfold frob. simpl.
  unfold ones''. reflexivity.
Qed.

(* Since cofix can unly unfold when it is the discriminee of a match expression we use frob to rewrite our definitions into the identity match, then s can unfold, the match can fire and then we have a Cons on both sides so we apply the constructor.
 Then for the equality of the tails we can use the coinductive hypothesis. *)
Theorem ones_eq : stream_eq ones ones'.
  cofix ones_eq.
  rewrite (frob_eq ones). rewrite (frob_eq ones').
  simpl. constructor. apply ones_eq.
Qed.

Definition hd {A} (s:stream A) : A :=
  match s with Cons t _ => t end.

Section stream_eq_coind.
  Variables (A:Type) (R: stream A -> stream A -> Prop).

  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2.
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2).

  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq s1 s2.
  Proof.
    cofix stream_eq_coind. intros s1 s2 HR.
    destruct s1, s2. specialize (Cons_case_hd _ _ HR).
    specialize (Cons_case_tl _ _ HR).
    simpl in Cons_case_hd. subst. constructor. apply stream_eq_coind, Cons_case_tl.
  Qed.
End stream_eq_coind.
Arguments stream_eq_coind [A].


Theorem ones_eq'' : stream_eq ones ones'.
Proof.
  apply (stream_eq_coind (fun s1 s2 => s1 = ones /\ s2 = ones')).
  - intros s1 s2 [-> ->].
    reflexivity.
  - intros * [-> ->]. split.
    + unfold tl. simpl. reflexivity.
    + unfold tl. simpl. reflexivity.
  - now split.
Qed.

Theorem stream_eq_sound {A:Type} : forall s1 s2:stream A, s1 = s2 -> stream_eq s1 s2.
Proof.
  intros s1 s2 Heq.
  apply (stream_eq_coind (fun s1 s2 => s1 = s2)).
  - intros s1' s2' ->. reflexivity.
  - intros s1' s2' ->. reflexivity.
  - assumption.
Qed.

(* a.d. done, define ones with two constructors and prove equality.
 R in the bisimulation needs strengthening *)
CoFixpoint ones''' := Cons 1 (Cons 1 ones''').

Theorem ones_eq''' : stream_eq ones ones'''.
Proof.
  apply (stream_eq_coind (fun s1 s2 => (s1 = ones /\ s2 = ones''') \/ (s1 = ones /\ s2 = Cons 1 ones''' ))).
  - intros s1 s2 [[-> ->] | [-> ->]]; reflexivity.
  - intros s1 s2 [[-> ->] | [-> ->]].
    + right. split.
      * unfold tl. simpl. reflexivity.
      * unfold tl. simpl. reflexivity.
    + left. split.
      * reflexivity.
      * simpl. reflexivity.
  - left. now split.
Qed.


Print fact.

CoFixpoint fact_slow' (n:nat) := Cons (fact n) (fact_slow' (S n)).
Definition fact_slow := fact_slow' 1.

CoFixpoint fact_iter' (cur acc : nat) := Cons acc (fact_iter' (S cur) (acc * cur)).
Definition fact_iter := fact_iter' 2 1.

Compute approx fact_slow 5.
Compute approx fact_iter 5.

Lemma fact_def : forall x n,
    fact_iter' x (fact n * S n) = fact_iter' x (fact (S n)).
Proof.
  intros x n. simpl. f_equal. lia.
Qed.

Hint Resolve fact_def.

Lemma fact_eq' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
Proof.
  intros n. apply (stream_eq_coind (fun s1 s2 => exists n, s1 = fact_iter' (S n) (fact n) /\ s2 = fact_slow' n)).
  - intros s1 s2 (m&H1&H2). unfold hd.
    subst. simpl. reflexivity.
  - intros * (m&H1&H2). exists (S m). split.
    + subst. simpl. rewrite fact_def. reflexivity.
    + subst. reflexivity.
  - exists n. now split.
Qed.

Theorem fact_eq : stream_eq fact_iter fact_slow.
Proof.
  apply fact_eq'.
Qed.

Section stream_eq_onequant.
  Variables (A B : Type) (f g : A -> stream B).

  Hypothesis Cons_case_hd : forall x, hd (f x) = hd (g x).
  Hypothesis Cons_case_tl : forall x, exists y, tl (f x) = f y /\ tl (g x) = g y.

  Theorem stream_eq_onequant : forall x, stream_eq (f x) (g x).
  Proof.
    intros x. apply (stream_eq_coind (fun s1 s2 => exists x, s1 = f x /\ s2 = g x)).
    - intros * (y&H1&H2).
      subst. apply Cons_case_hd.
    - intros * (y&H1&H2).
      subst. apply Cons_case_tl.
    - exists x. now split.
  Qed.
End stream_eq_onequant.
End Streams1.

(* a.d. done, stream lexi ordering example from here https://paulhe.com/2019/04/17/coinduction.html *)
(* how do we model the lexicographic ordering? *)
Module coind_tutorial.
  CoInductive stream (A:Type) :=
  | Nil : stream A
  | Cons : A -> stream A -> stream A.
  Arguments Nil {A}.
  Arguments Cons {A}.
  
  CoInductive lexi : stream nat -> stream nat -> Prop :=
  | L0 : lexi Nil Nil
  | L1 : forall s1 s2 n1 n2, lexi s1 s2 -> n1 <= n2 -> lexi (Cons n1 s1) (Cons n2 s2).

  (* the following expression in set theory *)
  (* X <<= F(X) *)
  (* should correspond to the following logical expression *)
  (* forall s1 s2, R s1 s2 -> F R s1 s2 *)
  (* a.d. todo, why must F be defined like this. Intuitively we would use forall s1' s2' ... *)
  Definition F (R: stream nat -> stream nat -> Prop) :=
    fun s1 s2 => (s1 = Nil /\ s2 = Nil) \/ (exists s1' s2' n1 n2, n1 <= n2 /\ R s1' s2' /\
                                                        (s1 = Cons n1 s1' /\ s2 = Cons n2 s2')).

  (*
    exists s1' s2' ... X 
    forall s1' s2' ... ~ X

    ~ n1 <= n2 \/ (~ R s1' s2' \/ ~ (s1 = ... /\ s2 = ...))
    n1 <= n2 -> R s1' s2' -> ~ (s1 = ... /\ s2 = ...)
   *)
  Definition aaa := cofix F := Cons 0 F.
  Definition baa := Cons 1 (cofix F := Cons 0 F).

  Fixpoint approx {A} (s:stream A) (n:nat) : list A :=
    match n with
    | 0 => nil
    | S n =>
      match s with
      | Nil => nil
      | Cons h t => h :: approx t n
      end
    end.
  Compute approx aaa 5.
  Compute approx baa 5.

  Definition frob {A} (s:stream A) :=
    match s with
    | Nil => Nil
    | Cons h t => Cons h t
    end.

  Theorem frob_eq {A} : forall (s:stream A), s = frob s.
    destruct s; reflexivity.
  Qed.

  Section lexi_coind.
    Variables (R: stream nat -> stream nat -> Prop).

    Hypothesis Hyp1 : forall s n, ~ R Nil (Cons n s).
    Hypothesis Hyp2 : forall s n, ~ R (Cons n s) Nil.
    Hypothesis Hyp0 : forall s1 s2 n1 n2, R (Cons n1 s1) (Cons n2 s2) -> n1 <= n2 /\ R s1 s2.
    
    Theorem lexi_coind : forall s1 s2, R s1 s2 -> lexi s1 s2.
    Proof.
      cofix lexi_coind. intros s1 s2 HR.
      destruct s1, s2.
      - constructor.
      - (* some hypothesis should give me a contradiction *)
        exfalso. eapply Hyp1, HR.
      - exfalso. eapply Hyp2, HR.
      - specialize (Hyp0 _ _ _ _ HR) as [H0 H1].
        constructor.
        + apply lexi_coind, H1.
        + apply H0.
    Qed.
  End lexi_coind.

  Section lexi_coind2.
    Variable (R: stream nat -> stream nat -> Prop).

    Hypothesis Hyp : forall s1 s2, R s1 s2 -> F R s1 s2.

    Theorem lexi_coind2 : forall s1 s2, R s1 s2 -> lexi s1 s2.
    Proof.
      cofix lexi_coind2. intros s1 s2 HR.
      destruct s1, s2.
      - constructor.
      - specialize (Hyp _ _ HR) as [[H0 H1]|H].
        + discriminate H1.
        + destruct H as (s1' & s2' & n1 & n2 & _ & _ & H & _).
          discriminate H.
      - specialize (Hyp _ _ HR) as [[H0 H1]|H].
        + discriminate H0.
        + destruct H as (s1' & s2' & n1 & n2 & _ & _ & _ & H).
          discriminate H.
      - specialize (Hyp _ _ HR) as [[H0 H1]|H].
        + discriminate H0.
        + constructor.
          * apply lexi_coind2.
            destruct H as (s1' & s2' & n1 & n2 & ? & ? & ? & ?).
            injection H1. injection H2. intros -> -> -> ->. apply H0.
          * destruct H as (s1' & s2' & n1 & n2 & ? & ? & ? & ?).
            injection H1. injection H2. intros -> -> -> ->. apply H.
    Qed.    
  End lexi_coind2.

  Goal lexi aaa baa.
      
    apply (lexi_coind2 (fun s1 s2 => (s1 = aaa /\ s2 = baa) \/ (s1 = aaa /\ s2 = aaa))).
    2: auto.
    intros s1 s2 [[H0 H1]|[H0 H1]].
    - hnf. right. exists aaa, aaa, 0, 1. repeat split.
      + lia.
      + now right.
      + subst. rewrite (frob_eq aaa) at 1. unfold frob. simpl. reflexivity.
      + subst. reflexivity.
    - hnf. right. exists aaa, aaa, 0, 0. repeat split.
      + lia.
      + now right.
      + subst. rewrite (frob_eq aaa) at 1. unfold frob. simpl. reflexivity.
      + subst. rewrite (frob_eq aaa) at 1. unfold frob. simpl. reflexivity.
  Qed. 

  Goal lexi aaa baa.
  Proof.
    apply (lexi_coind (fun s1 s2 => s1 = aaa /\ s2 = baa)).
    - intros * [H _]. rewrite (frob_eq aaa) in H. simpl in H. discriminate.
    - intros * [_ H]. unfold baa in H. discriminate.
    - (* here we are stuck because we can't prove the tail s2 is baa
       So we generalize R *)
      Restart.
    apply (lexi_coind (fun s1 s2 => (s1 = aaa /\ s2 = baa) \/ (s1 = aaa /\ s2 = aaa))).
    - intros * [[H _]|[H _]]; rewrite (frob_eq aaa) in H; simpl in H; discriminate.
    - intros * [[_ H]|[_ H]]; [rewrite (frob_eq baa) in H|rewrite (frob_eq aaa) in H]; simpl in H; discriminate.
    - intros *. rewrite (frob_eq aaa), (frob_eq baa). simpl.
      intros [[H1 H2]|[H1 H2]]; split; injection H1; injection H2.
      + lia.
      + right. subst. rewrite (frob_eq aaa) at 1. rewrite (frob_eq (cofix F := Cons 0 F)).
        split; reflexivity.
      + lia.
      + right. subst. rewrite (frob_eq aaa) at 1 3.
        split; reflexivity.
    - left. split; reflexivity.
  Qed.

  (*
das Praedikat R ist das set X (also alle Argumente die R erfuellen sind im set), lexi ist der greates fixpoint nyF und das coinduction lemma lexi_coind, das man bei cpdt immer definiert, ist der Beweis "X subset von nyF" weil das ja "R impliziert lexi" in propositioneller Sprache entspricht.
und da die Hypothesen des coinduction lemmas den Inversionslemmas entsprechen, denke ich, dass sie das F definieren. (die Hyp1 & Hyp2 sind dann in Coq dazugekommen weil sie in set theory wahrscheinlich implizit da sind). Und wenn man dann in dem letzten Goal das coinduction lemma anwenden moechte, muss man die Hypothesen beweisen, was dann dem Beweis "X subset von F(X)" entsprechen sollte.
Wobei ich mir da noch unsicher bin, weil es wieder falschrum wirkt. "X subset von F(X)" sollte ja so aehnlich sein wie "R s1 s2 -> n1 <= n2 -> R (Cons n1 s1) (Cons n2 s2)"
   *)
End coind_tutorial.

Definition var := nat.
Definition vars := var -> nat.
Definition set (vs: vars) (v: var) (n: nat) : vars :=
  fun v' => if beq_nat v v' then n else vs v'.

Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Plus : exp -> exp -> exp.

Fixpoint evalExp (vs: vars) (e: exp) : nat :=
  match e with
  | Const n => n
  | Var v => vs v
  | Plus e1 e2 => (evalExp vs e1) + (evalExp vs e2)
  end.

Inductive cmd : Set :=
| Assign : var -> exp -> cmd
| Seq : cmd -> cmd -> cmd
| While : exp -> cmd -> cmd.

CoInductive evalCmd : vars -> cmd -> vars -> Prop :=
| EvalAssign : forall vs v e,
    evalCmd vs (Assign v e) (set vs v (evalExp vs e))
| EvalSeq : forall vs1 vs2 vs3 c1 c2,
    evalCmd vs1 c1 vs2 -> evalCmd vs2 c2 vs3 -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs e c,
    evalExp vs e = 0 -> evalCmd vs (While e c) vs
| EvalWhileTrue : forall vs1 vs2 vs3 e c,
    evalExp vs1 e <> 0 -> evalCmd vs1 c vs2 -> evalCmd vs2 (While e c) vs3 -> evalCmd vs1 (While e c) vs3.

Section evalCmd_coind.
  Variable R : vars -> cmd -> vars -> Prop.

  Hypothesis AssignCase : forall vs1 vs2 v e, R vs1 (Assign v e) vs2 -> vs2 = set vs1 v (evalExp vs1 e).
  Hypothesis SeqCase : forall vs1 vs3 c1 c2, R vs1 (Seq c1 c2) vs3 -> exists vs2, R vs1 c1 vs2 /\ R vs2 c2 vs3.
  Hypothesis WhileCase : forall vs1 vs3 e c, R vs1 (While e c) vs3 ->
                                        (evalExp vs1 e = 0 /\ vs3 = vs1)
                                        \/ (exists vs2, evalExp vs1 e <> 0 /\ R vs1 c vs2 /\ R vs2 (While e c) vs3).

  Theorem evalCmd_coind : forall vs1 c vs2, R vs1 c vs2 -> evalCmd vs1 c vs2.
  Proof.
    cofix evalCmd_coind. intros * HR. destruct c.
    - rewrite (AssignCase _ _ _ _ HR). constructor.
    - destruct (SeqCase _ _ _ _ HR) as (vs3&HR1&HR2).
      econstructor; eapply evalCmd_coind; eassumption.
    - destruct (WhileCase _ _ _ _ HR) as [[H0 H1] | (vs3 & H0 & H1 & H2)].
      + subst. econstructor. assumption.
      + econstructor; [idtac | eapply evalCmd_coind .. ]; eassumption.
  Qed.
End evalCmd_coind.

Fixpoint optExp (e:exp) : exp :=
  match e with
  | Plus (Const 0) e => optExp e
  | Plus e1 e2 => Plus (optExp e1) (optExp e2)
  | _ => e
  end. (* a.d. todo, also optimize right add *)

Fixpoint optCmd (c:cmd) : cmd :=
  match c with
  | Assign v e => Assign v (optExp e)
  | Seq c1 c2 => Seq (optCmd c1) (optCmd c2)
  | While e c => While (optExp e) (optCmd c)
  end.

Lemma optExp_correct : forall vs e, evalExp vs (optExp e) = evalExp vs e.
Proof.
  induction e as [n | v | e1 IH1 e2 IH2 ].
  - reflexivity.
  - reflexivity.
  - destruct e1.
    + destruct n. simpl. apply IH2.
      simpl. rewrite IH2. reflexivity.
    + simpl. rewrite IH2. reflexivity.
    + cbn. cbn in IH1. rewrite IH1, IH2. reflexivity.
Qed. 

Lemma optCmd_correct1 : forall vs1 c vs2, evalCmd vs1 c vs2 -> evalCmd vs1 (optCmd c) vs2.
Proof.
  intros * H.
  apply (evalCmd_coind (fun vs1 c' vs2 => exists c, evalCmd vs1 c vs2 /\ c' = optCmd c)).
  - intros vs1' vs2' v e (c' & Hc0 & Hc1). inversion Hc0.
    2-4: subst; simpl in Hc1; discriminate.
    subst. simpl in Hc1. injection Hc1. intros -> ?. subst. rewrite optExp_correct. reflexivity.
  - intros vs1' vs2' c1 c2 (c' & Hc0 & Hc1). inversion Hc0.
    1, 3, 4: subst; simpl in Hc1; discriminate.
    subst. simpl in Hc1. injection Hc1. intros ? ?.
    exists vs3. split; [exists c0|exists c3]; split; assumption.
  - Admitted.
    

    
