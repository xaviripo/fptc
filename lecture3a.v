(* Formalizing and Proving Theorems in Coq --- Homework 3, part a.
   curated by Tobias Kappé, May 2022.

   For today's exercises, you should paste your proofs from the second homework
   into this file, and trim them using the tacticals we learned today.

   However, you may *not* yet use any of the automation tactics we saw; we will
   practice those in lecture-3c.v. *)

Require Import Coq.Program.Equality.

(* Peano's encoding of the natural numbers *)
Inductive nat :=
| Zero              (* 0 is a natural number *)
| Succ (n: nat)     (* if n is a natural number, then so is S(n) *)
.

(* Let's fix some well-known numbers. *)
Notation "0" := Zero.
Notation "1" := (Succ 0).
Notation "2" := (Succ 1).

(* Addition defined by recursion on the second operand. *)
Fixpoint add (n m: nat): nat :=
  match m with
  | 0 => n
  | Succ m' =>
    Succ (add n m')
  end
.

(* We make our life easier by introducing some notation. *)
Infix "+" := add (at level 50, left associativity).

(* Zero is neutral for addition on the left hand side. *)
Lemma add_zero_right (n: nat):
  n + 0 = n
.
Proof.
  simpl.
  reflexivity.
Qed.

(* Zero is neutral for addition on the right hand side. *)
Lemma add_zero_left (n: nat):
  0 + n = n
.
Proof.
  induction n.
  - rewrite add_zero_right.
    reflexivity.
    (* Let's try that again with a different tactic. *)
    Undo.
    easy.
    (* An even shorter way of doing the same thing *)
    Undo.
    Undo.
    now rewrite add_zero_right.
  - simpl.
    now rewrite IHn.
Qed.

(* This is a useful lemma for what follows: adding one to the left operand of
   an addition is the same as adding one to the right operand. *)
Lemma add_succ (n m: nat):
  (Succ n) + m = n + (Succ m)
.
Proof.
  (* Here is the old proof. *)
  simpl.
  induction m.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHm.
    reflexivity.

  (* Once more, with feeling. *)
  Restart.

  (* Apply 'simpl' to any goal that results. *)
  induction m; simpl.
  - reflexivity.
  - now rewrite IHm.

  Restart.

  (* This goal, it turns out, is not easy. *)
  Fail easy.

  (* We can use 'try' to catch possible failure.
     Notice how nothing changes about our goal. *)
  try easy.

  (* We can try to apply 'easy' to each successive goal. *)
  induction m; simpl; try easy.
  (* Notice how the first subgoal has disappeared! No need for bullets. *)
  now rewrite IHm.
Qed.

(* Addition is commutative; let's prove this from the definition. *)
Lemma add_commute (n m: nat):
  n + m = m + n
.
Proof.
  induction m.
  - simpl.
    rewrite add_zero_left.
    reflexivity.
  - rewrite add_succ.
    simpl.
    rewrite IHm.
    reflexivity.

  Restart.

  induction m; simpl.
  - now rewrite add_zero_left.
  - now rewrite add_succ, IHm.
Qed.

(* Homework --- Exercise 1 *)
Lemma add_associate (n m k: nat):
  (n + m) + k = n + (m + k)
.
Proof.
  induction k.
  - now repeat rewrite add_zero_right.
  - simpl.
    f_equal.
    apply IHk.
Qed.

(* Example of repeated re-association and the try tactical. *)
Lemma add_associate_more (n m k l: nat):
  ((n + m) + k) + l = n + (m + (k + l))
.
Proof.
  (* This is a matter of re-associating all brackets to the right. *)
  rewrite add_associate.
  rewrite add_associate.
  reflexivity.

  Restart.

  (* We can also just keep rewriting until the tactic fails. *)
  repeat rewrite add_associate.
  reflexivity.

  Restart.

  (* This tactic fails immediately. *)
  Fail easy.
  (* What would this do? *)
  repeat easy.

  (* The 'repeat' tactical combines with others, like 'now'. *)
  now repeat rewrite add_associate.
Qed.

(* Homework --- Exercise 2 *)
Lemma add_exchange (p q r s: nat):
  (p + q) + (r + s) =
  (p + r) + (q + s)
.
Proof.
  repeat rewrite add_associate.
  rewrite <- add_associate with (n := q).
  rewrite add_commute with (n := q).
  now rewrite add_associate.
Qed.

(* We may also define addition by recursion on the first operand. *)
Fixpoint add' (n m: nat): nat :=
  match n with
  | 0 => m
  | Succ n' =>
    Succ (add' n' m)
  end
.

(* Homework --- Exercise 3 *)
Lemma add_vs_add' (n m: nat):
  n + m = add' n m
.
Proof.
  induction n; simpl.
  - now rewrite add_zero_left.
  - rewrite add_succ.
    simpl.
    f_equal.
    apply IHn.
Qed.

(* Multiplication can also be defined recursively. *)
Fixpoint mul (n m: nat): nat :=
  match m with
  | 0 => 0
  | Succ m' => mul n m' + n
  end
.

Infix "*" := mul (at level 40, left associativity).

(* Zero is annihilating for multiplication. *)
Lemma mul_zero (n: nat):
  0 * n = 0
.
Proof.
  (* Here is the old proof. *)
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    apply IHn.

  (* Let's try that again. *)
  Restart.

  (* The subgoals can be cleared automatically. *)
  induction n; simpl.
  - auto.
  - auto.

  Restart.

  (* Or in one fell swoop. *)
  induction n; simpl; auto.
Qed.

(* Homework --- Exercise 4 *)
Lemma mul_succ (n m: nat):
  (Succ n) * m = m + (n * m)
.
Proof.
  induction m; simpl; try easy.
  rewrite IHm, add_succ.
  simpl.
  now rewrite add_associate.
Qed.

(* Homework --- Exercise 5 *)
Lemma mul_commute (n m: nat):
  n * m = m * n
.
Proof.
  induction m; simpl.
  - now rewrite mul_zero.
  - now rewrite mul_succ, add_commute, IHm.
Qed.

(* Of course, we can also define multiplication differently. *)
Fixpoint mul' (n m: nat): nat :=
  match n with
  | 0 => 0
  | Succ n' => m + mul' n' m
  end
.

(* Homework --- Exercise 6 *)
Lemma mul_vs_mul' (n m: nat):
  n * m = mul' n m
.
Proof.
  induction n; simpl.
  - apply mul_zero.
  - now rewrite mul_succ, IHn.
Qed.

(* Recursively compute the sum of the first n odd numbers. *)
Fixpoint sum_odd (n: nat): nat :=
  match n with
  | 0 => 0
  | Succ n' =>
    (* 2n-1 + sum of the first n-1 odd numbers. *)
    Succ (sum_odd n' + 2 * n')
  end
.

(* The sum of the first n odd numbers is exactly n^2. *)
Lemma sum_odd_is_square (n: nat):
  sum_odd n = n * n
.
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    f_equal.
    rewrite mul_commute with (n := Succ n).
    simpl.
    rewrite mul_commute with (n := 2).
    simpl.
    rewrite add_zero_left.
    rewrite add_associate.
    reflexivity.

  Restart.
  induction n; simpl.
  - auto.
  - rewrite IHn.
    f_equal.
    rewrite mul_commute with (n := Succ n); simpl.
    rewrite mul_commute with (n := 2); simpl.
    now rewrite add_zero_left, add_associate.

  Restart.
  induction n; simpl; auto.
  rewrite IHn.
  f_equal.
  rewrite mul_commute with (n := Succ n); simpl.
  rewrite mul_commute with (n := 2); simpl.
  now rewrite add_zero_left, add_associate.
Qed.

(* Homework --- Exercise 7 *)
Lemma mul_distribute_right (n m k: nat):
  (n + m) * k = n * k + m * k
.
Proof.
  induction k; simpl; try easy.
  rewrite IHk.
  repeat rewrite add_associate.
  f_equal. (* Throwing out the trash *)
  rewrite <- add_associate.
  rewrite (add_commute (m * k)).
  now rewrite add_associate.
Qed.

(* Calculate 1 + 2 + ... + n recursively. *)
Fixpoint accumulate (n: nat): nat :=
  match n with
  | 0 => 0
  | Succ n' => n + (accumulate n')
  end
.

(* Verify that the sum above can also be calculated directly, using the well-
   known expression n(n+1)/2. Because we do not have division, we convert the
   division by two into a multiplication on the other side.

   Homework --- Exercise 8 *)
Lemma gauss_correct (n: nat):
  2 * (accumulate n) = n * (Succ n)
.
Proof.
  (* Not much we can do to improve this proof without using automations *)
  induction n; simpl; try easy.
  rewrite mul_commute, mul_distribute_right, mul_commute.
  rewrite (mul_commute (accumulate n)), IHn.
  rewrite mul_commute.
  simpl (Succ n * 2).
  rewrite add_zero_left, add_succ.
  simpl add.
  f_equal.
  rewrite (add_commute (Succ n)), add_associate, (add_commute (Succ n)).
  rewrite <- add_associate.
  simpl add.
  rewrite add_succ.
  simpl.
  f_equal.
  rewrite (mul_commute (Succ n)).
  simpl.
  rewrite <- add_associate.
  now rewrite (add_commute (n*n)).
Qed.

(* The Fibonacci numbers. *)
Fixpoint fib (n: nat): nat :=
  match n with
  | 0 => 0
  | Succ n' =>
    match n' with
    | 0 => 1
    | Succ n'' =>
      fib n' + fib n''
    end
  end
.

(* Convenient lemma that directly gives the recursive case. *)
Lemma fib_plus_two (n: nat):
  fib (Succ (Succ n)) = fib n + fib (Succ n)
.
Proof.
  now rewrite add_commute.
Qed.

(* The Fibonacci numbers exhibit this interesting property:
    F_{n+m+1) = F_{n+1}F_{m+1} + F_{nm}
  This is known as Honsberger's identity. Let's try and prove it. *)
Lemma fib_multiply (n m: nat):
  fib (n + Succ m) =
  fib (Succ n) * fib (Succ m) + fib n * fib m
.
Proof.
  revert n.
  induction m.
  - intro.
    simpl.
    rewrite add_zero_left.
    reflexivity.
  - intro.
    rewrite <- add_succ.
    rewrite IHm.
    rewrite fib_plus_two.
    rewrite mul_distribute_right.
    rewrite add_associate.
    rewrite mul_commute with (n := fib (Succ n)).
    rewrite mul_commute with (n := fib (Succ n)).
    rewrite <- mul_distribute_right.
    rewrite add_commute with (n := fib (Succ m)).
    rewrite mul_commute with (m := fib (Succ n)).
    rewrite <- fib_plus_two.
    rewrite add_commute.
    reflexivity.

  Restart.
  revert n; induction m; intro.
  - simpl.
    now rewrite add_zero_left.
  - rewrite <- add_succ.
    rewrite IHm.
    rewrite fib_plus_two.
    rewrite mul_distribute_right.
    rewrite add_associate.
    rewrite mul_commute with (n := fib (Succ n)).
    rewrite mul_commute with (n := fib (Succ n)).
    rewrite <- mul_distribute_right.
    rewrite add_commute with (n := fib (Succ m)).
    rewrite mul_commute with (m := fib (Succ n)).
    rewrite <- fib_plus_two.
    now rewrite add_commute.
Qed.

(* We can also define relations inductively, such as "less than or equal". *)
Inductive less_than_equal: nat -> nat -> Prop :=
| LERefl: forall (n: nat), n <= n
| LESucc: forall (n m: nat), n <= m -> n <= Succ m
where "n <= m" := (less_than_equal n m).

(* Less than or equal is a transitive relation. *)
Lemma less_than_equal_trans (n m k: nat):
  n <= m -> m <= k -> n <= k
.
Proof.
  intros.
  induction H0.
  - apply H.
  - apply LESucc.
    apply IHless_than_equal.
    apply H.
Qed.

(* Homework --- Exercise 9 *)
Lemma less_than_equal_shift (n m: nat):
  n <= m -> Succ n <= Succ m
.
Proof.
  intro.
  induction m; simple inversion H.
  - rewrite <- H0, H1.
    apply LERefl.
  - easy.
  - rewrite <- H0, H1.
    apply LERefl.
  - rewrite <- H2, H1.
    inversion H2.
    intro.
    apply LESucc, IHm, H0.
Qed.

(* Any number that is at most zero must actually be zero. *)
Lemma less_than_equal_zero (n: nat):
  n <= 0 -> n = 0
.
Proof.
  intro.
  simple inversion H.
  - rewrite <- H0.
    apply H1.
  - discriminate.
Qed.

(* This relation truly encodes "less than or equal". *)
Lemma less_than_equal_succ (n m: nat):
  n <= Succ m -> n = Succ m \/ n <= m
.
Proof.
  intro.
  simple inversion H.
  - left.
    now rewrite <- H0, <- H1.
  - intro.
    inversion H2.
    right.
    now rewrite <- H1, <- H4.
Qed.

(* Homework --- Exercise 10 *)
Lemma less_than_equal_mono_add_left (n m k: nat):
  n <= m -> n + k <= m + k
.
Proof.
  intro.
  induction k; simpl.
  - apply H.
  - apply less_than_equal_shift, IHk.
Qed.

Lemma less_than_equal_mono_add (n m k l: nat):
  n <= m ->
  k <= l ->
  n + k <= m + l
.
Proof.
  intros.

  (* Coq cannot infer the missing parameter. *)
  Fail apply less_than_equal_trans.

  (* Let's put in a placeholder instead. *)
  eapply less_than_equal_trans.
  (* Notice the ?m filled in for now. *)
  - (* We can now apply left-monotonicity. *)
    apply less_than_equal_mono_add_left.
    (* This means ?m is of the form _ + k, which leaves
       the left-hand side undetermined as ?m. We apply
       our hypothesis about n to fill it in. *)
    apply H.
  - (* Notice how ?m has now been fixed as a result of
       our earlier tactic applications. *)
    rewrite add_commute.
    rewrite add_commute with (n := m).
    apply less_than_equal_mono_add_left.
    apply H0.
Qed.

(* Homework --- Exercise 11 *)
Lemma less_than_equal_mono_mul (n m k: nat):
  n <= m -> n * k <= m * k
.
Proof.
  intro.
  induction k; simpl.
  - apply LERefl.
  (* Here eapply acts as apply because Coq CAN infer the missing parameters *)
  - apply less_than_equal_mono_add.
    + apply IHk.
    + apply H.
Qed.

(* The Lucas numbers are a series defined as follows. *)
Fixpoint lucas (n: nat): nat :=
  match n with
  | 0 => 2
  | Succ n' =>
    match n' with
    | 0 => 1
    | Succ n'' => (lucas n') + (lucas n'')
    end
  end
.

(* As before, this equation comes in handy. *)
Lemma lucas_plus_two (n: nat):
  lucas (Succ (Succ n)) = lucas n + lucas (Succ n)
.
Proof.
  now rewrite add_commute.
Qed.

(* Here is a shorthand for "the predicate P holds up to n". *)
Definition holds_up_to (P: nat -> Prop) (n: nat) :=
  forall (m: nat), less_than_equal m n -> P m
.

(* Here is a version of the strong induction principle. It says that if (1) the
   predicate holds for 0 and (2) given that the predicate holds for all numbers
   less than or equal to n, we can prove it for Succ n, it follows that the
   predicate also holds for ab arbitrary n. Let's prove that it is sound. *)
Lemma strong_induction
  (P: nat -> Prop)
  (HBase: P 0)
  (HStep: forall (n: nat), holds_up_to P n -> P (Succ n))
  (n: nat)
:
  P n
.
Proof.
  enough (forall m, less_than_equal m n -> P m).
  - apply H.
    apply LERefl.
  - induction n.
    + intros.
      rewrite less_than_equal_zero.
      * apply HBase.
      * apply H.
    + intros.
      destruct (less_than_equal_succ m n).
      * exact H.
      * subst.
        apply HStep.
        unfold holds_up_to.
        apply IHn.
      * apply IHn.
        apply H0.

  Restart.

  enough (forall m, less_than_equal m n -> P m).
  - apply H, LERefl.
  - induction n; intros.
    + now rewrite less_than_equal_zero.
    + destruct (less_than_equal_succ m n); auto.
      subst.
      apply HStep.
      unfold holds_up_to.
      apply IHn.
Qed.

(* We can also prove a different induction principle. This one says that if we
   can prove that (1) the claim for zero and one, and (2) given that the claim
   holds for the two precedessors of a number, it also holds for the number
   it self, then the claim holds for all numbers. *)
Lemma pair_induction
  (P: nat -> Prop)
  (HBaseZero: P 0)
  (HBaseOne: P 1)
  (HStep: forall (n: nat), P n -> P (Succ n) -> P (Succ (Succ n)))
  (n: nat)
:
  P n
.
Proof.
  induction n using strong_induction.
  - apply HBaseZero.
  - unfold holds_up_to in H.
    destruct n.
    + apply HBaseOne.
    + apply HStep.
      * apply H.
        apply LESucc.
        apply LERefl.
      * apply H.
        apply LERefl.

  Restart.

  induction n using strong_induction; auto.
  unfold holds_up_to in H.
  destruct n; auto.
  apply HStep; apply H.
  * apply LESucc.
    apply LERefl.
  * apply LERefl.
Qed.

Lemma lucas_vs_fibonnaci (n: nat):
  lucas (Succ n) = fib n + fib (Succ (Succ n))
.
Proof.
  induction n using pair_induction.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - rewrite lucas_plus_two.
    rewrite IHn, IHn0.
    rewrite add_exchange.
    f_equal.
    + rewrite fib_plus_two.
      reflexivity.
    + rewrite fib_plus_two with (n := Succ (Succ n)).
      reflexivity.

  Restart.

  induction n using pair_induction; auto.
  rewrite lucas_plus_two.
  rewrite IHn, IHn0.
  rewrite add_exchange.
  f_equal.
  - now rewrite fib_plus_two.
  - now rewrite fib_plus_two with (n := Succ (Succ n)).
Qed.

(* Homework --- Exercise 12 *)
Lemma skip_induction
  (P: nat -> Prop)
  (HBaseZero: P 0)
  (HBaseOne: P 1)
  (HStep: forall (n: nat), P n -> P (Succ (Succ n)))
  (n: nat)
:
  P n
.
Proof.
  induction n using strong_induction.
  - easy.
  - unfold holds_up_to in H.
    (* At this point, we want to act on the *antecesor* of n,
    so this is basically a natural induction (i.e. separating the case
    for 0 and the rest of the cases).
    Feels a bit weird doing this after a strong induction but
    the hint in the previous hw wanted us to use strong induction *)
    induction n; try easy.
    apply HStep.
    apply (H n).
    apply LESucc.
    apply LERefl.
Qed.


Fixpoint sum_fib (n: nat): nat :=
  match n with
  | 0 => 0
  | Succ n' => fib n + sum_fib n'
  end
.

Lemma sum_fib_succ (n: nat):
  sum_fib (Succ n) = fib (Succ n) + sum_fib n
.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma add_equation (n m: nat):
  n + Succ m = Succ (n + m)
.
Proof.
  reflexivity.
Qed.

(* Homework --- Exercise 13, optional. *)
Lemma sum_fib_direct (n: nat):
  Succ (sum_fib n) = fib (Succ (Succ n))
.
Proof.
  induction n using skip_induction; try easy.
  repeat rewrite sum_fib_succ.
  repeat rewrite <- add_equation.
  rewrite IHn.
  now repeat rewrite <- fib_plus_two.
Qed.
