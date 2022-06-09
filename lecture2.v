(* Formalizing and Proving Theorems in Coq --- Homework 2.
   curated by Tobias Kappé, May 2022.

   For today's exercises, you should complete all of the lemmas marked with
   "Homework" below.

   When proving these lemmas, you may use all of the tactics that we saw in
   the lecture (they also appear in this file). You may *not* use any of the
   other tactics, including in particular automation like "intuition". *)

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
  (* Proceed by induction on the parameter n. *)
  induction n.
  - (* Base case: n is 0. *)
    rewrite add_zero_right.
    reflexivity.
  - (* Inductive step: prove the case for S(n), assuming the case for n.
       First, we unroll the definition of addition. *)
    simpl.
    (* Now we can rewrite part of the goal using the induction hypothesis. *)
    rewrite IHn.
    (* And we're done! *)
    reflexivity.
Qed.

(* This is a useful lemma for what follows: adding one to the left operand of
   an addition is the same as adding one to the right operand. *)
Lemma add_succ (n m: nat):
  (Succ n) + m = n + (Succ m)
.
Proof.
  (* Unroll the definition of addition again. *)
  simpl.
  (* Since add proceeds by recursion on the right operand, our proof also
     proceeds by induction on the right operand. *)
  induction m.
  - (* The base case can be trivialized. *)
    rewrite add_zero_right.
    rewrite add_zero_right.
    reflexivity.
  - (* For the inductive case, note that we have an induction hypothesis about
       m, and we need to prove the claim for S(m). First, we unroll. *)
    simpl.
    (* Now rewrite using the induction hypothesis to obtain a triviality. *)
    rewrite IHm.
    reflexivity.
    (* Let's take some steps back and see an alternative approach. *)
    Undo.
    Undo.
    (* New tactic: prove that the operands to a function are equal in order
       to show that its output is equal. *)
    f_equal.
    (* The remaining proof turns out to be our induction hypothesis. *)
    apply IHm.
Qed.

(* Addition is commutative; let's prove this from the definition. *)
Lemma add_commute (n m: nat):
  n + m = m + n
.
Proof.
  (* As before, induction on the recursive argument is key. *)
  induction m.
  - (* In the base, we can rewrite using the earlier lemmas. *)
    rewrite add_zero_left, add_zero_right.
    reflexivity.
  - (* For the inductive step, let's apply our previous lemma. *)
    rewrite add_succ.
    (* Now we are in a possition where both sides of the equation can be
       simplified by unrolling the definition of addition. *)
    simpl.
    (* Inside the operator, rewrite using the induction hypothesis. *)
    rewrite IHm.
    (* And we're done. *)
    reflexivity.
Qed.

(* Homework --- Exercise 1 *)
Lemma add_associate (n m k: nat):
  (n + m) + k = n + (m + k)
.
Proof.
  induction n.
  - rewrite add_zero_left.
    rewrite add_zero_left.
    reflexivity.
  - rewrite add_succ.
    simpl.
    rewrite add_succ.
    simpl.
    rewrite add_succ.
    simpl.
    f_equal.
    apply IHn.
Qed.

(* Homework --- Exercise 2 *)
Lemma add_exchange (p q r s: nat):
  (p + q) + (r + s) =
  (p + r) + (q + s)
.
Proof.
  rewrite add_associate.
  rewrite <- add_associate with (n := q).
  rewrite add_commute with (n := q).
  rewrite add_associate.
  rewrite <- add_associate.
  reflexivity.
Qed.

(* We may also define addition by recursion on the first operand. *)
Fixpoint add' (n m: nat): nat :=
  match n with
  | 0 => m
  | Succ n' =>
    Succ (add' n' m)
  end
.

(* Homework --- Exercise 3, optional *)
Lemma add_vs_add' (n m: nat):
  n + m = add' n m
.
Proof.
  induction n.
  - simpl.
    rewrite add_zero_left.
    reflexivity.
  - simpl.
    rewrite add_succ.
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
  (* Induction on the only thing we have. *)
  induction n.
  - (* This simplifies immediately. *)
    simpl.
    reflexivity.
  - (* This just simplifies to the induction hypothesis. *)
    simpl.
    apply IHn.
Qed.

(* Homework --- Exercise 4 *)
Lemma mul_succ (n m: nat):
  (Succ n) * m = m + (n * m)
.
Proof.
  induction m.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHm.
    rewrite add_succ.
    simpl.
    rewrite add_associate.
    reflexivity.
Qed.

(* Homework --- Exercise 5 *)
Lemma mul_commute (n m: nat):
  n * m = m * n
.
Proof.
  induction m.
  - simpl.
    rewrite mul_zero.
    reflexivity.
  - simpl.
    rewrite mul_succ.
    rewrite add_commute.
    rewrite IHm.
    reflexivity.
Qed.

(* Of course, we can also define multiplication differently. *)
Fixpoint mul' (n m: nat): nat :=
  match n with
  | 0 => 0
  | Succ n' => m + mul' n' m
  end
.

(* Homework --- Exercise 6, optional *)
Lemma mul_vs_mul' (n m: nat):
  n * m = mul' n m
.
Proof.
  induction n.
  - simpl.
    apply mul_zero.
  - simpl.
    rewrite mul_succ.
    rewrite IHn.
    reflexivity.
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
  (* Start by induction on our only parameter. *)
  induction n.
  - (* The base is just a direct computation. *)
    simpl.
    reflexivity.
  - (* First unfold the definitions of sum_odd and mul. *)
    simpl.
    (* Apply the induction hypothesis. *)
    rewrite IHn.
    (* Focus on the bits under Succ *)
    f_equal.
    (* Commute the multiplication on the right. *)
    rewrite mul_commute with (n := Succ n).
    (* Simplify using the definition of mul. *)
    simpl.
    (* Commute the second multiplication, unfold *)
    rewrite mul_commute with (n := 2).
    simpl.
    (* Get rid of the zero on the left. *)
    rewrite add_zero_left.
    (* Shift the brackets around. *)
    rewrite add_associate.
    reflexivity.
Qed.

(* Homework --- Exercise 7 *)
Lemma mul_distribute_right (n m k: nat):
  (n + m) * k = n * k + m * k
.
Proof.
  induction k.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHk.
    rewrite add_associate.
    rewrite add_associate.
    f_equal. (* Throwing out the trash *)
    rewrite <- add_associate.
    rewrite (add_commute (m * k)).
    rewrite add_associate.
    reflexivity.
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
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    (* I'm probably not doing this as you intended because I need distributivity on the other side *)
    rewrite mul_commute.
    rewrite mul_distribute_right.
    rewrite mul_commute.
    rewrite (mul_commute (accumulate n)).
    rewrite IHn.
    (* Now we make both sides into Succ(...) to use f_equal *)
    rewrite mul_commute.
    simpl (Succ n * 2).
    rewrite add_zero_left.
    rewrite add_succ.
    simpl add.
    f_equal.
    (* Again, fix the right side to have Succ(...) *)
    rewrite (add_commute (Succ n)).
    rewrite add_associate.
    rewrite (add_commute (Succ n)).
    rewrite <- add_associate.
    simpl add.
    (* Now the left side *)
    rewrite add_succ.
    simpl.
    f_equal.
    rewrite (mul_commute (Succ n)).
    simpl.
    rewrite <- add_associate.
    rewrite (add_commute (n*n)).
    reflexivity.
Qed.

(* Let's try to define the Fibonacci numbers. *)
Fail Fixpoint fib (n: nat): nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | Succ (Succ n) =>
    fib n + fib (Succ n)
  end
.

(* Oops, Coq did not like that! It turns out you cannot write recursive
   functions that cannot (easily) be shown to terminate. Fortunately, the
   following does work. *)
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
  simpl.
  rewrite add_commute.
  reflexivity.
Qed.

(* The Fibonacci numbers exhibit this interesting property:
    F_{n+m+1) = F_{n+1}F_{m+1} + F_{nm}
  This is known as Honsberger's identity. Let's try and prove it. *)
Lemma fib_multiply (n m: nat):
  fib (n + Succ m) =
  fib (Succ n) * fib (Succ m) + fib n * fib m
.
Proof.
  induction m.
  - (* The base case is simple enough. *)
    simpl.
    rewrite add_zero_left.
    reflexivity.
  - (* Shift the 1 to the left. *)
    rewrite <- add_succ.
    (* At this point, the induction hypothesis does *not* apply! *)
    Fail rewrite IHm.
    (* The problem is that the goal is about the successor of n, while the
       induction hypothesis is about n. Let's try this again. *)
    Restart.

  (* This time we prove a more general statement. *)
  revert n.
  (* Notice how the goal changed from a statement about the m we had in
     context to a statement about all n (with n now out of context. *)
  induction m.
  - (* We now need to pull n back into the context again. *)
    intro.
    (* The rest of the base strategy is the same. *)
    simpl.
    rewrite add_zero_left.
    reflexivity.
  - (* As before, we pull n back into the context. *)
    intro.
    (* Notice how our induction hypothesis is more general now, quantifying
       over all n. We proceed with the same strategy as before. *)
    rewrite <- add_succ.
    (* Now, the induction hypothesis *does* apply. *)
    rewrite IHm.
    (* Unroll the recursive Fibonacci term on the left. *)
    rewrite fib_plus_two.
    (* Distribute the multiplication. *)
    rewrite mul_distribute_right.
    (* Shift parentheses around (not on the slides) *)
    rewrite add_associate.
    (* We do not have a lemma for left-distributivity, so we emulate it by
       moving some terms around. First, we commute two multiplications. *)
    rewrite mul_commute with (n := fib (Succ n)).
    rewrite mul_commute with (n := fib (Succ n)).
    (* Now we can use distributivity in reverse. *)
    rewrite <- mul_distribute_right.
    (* Finally we commute the terms again. *)
    rewrite add_commute with (n := fib (Succ m)).
    rewrite mul_commute with (m := fib (Succ n)).
    (* Fold the recursive Fibonacci term again. *)
    rewrite <- fib_plus_two.
    (* Switch the terms of the sum. *)
    rewrite add_commute.
    (* And we're done! *)
    reflexivity.
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
  (* We use this tactic to pull in *all* premises. *)
  intros.
  (* Now proceed by induction on the construction of the right hypothesis. *)
  induction H0.
  - (* In the base, m <= k because m = k. Coq has figured this out on our
       behalf, and applied some substitutions already. *)
    apply H.
  - (* Here, m <= k because k = Succ l, and k <= l. Coq has also knows this,
       but (somewhat confusingly) uses the symbol n0 for m, and m for l.
       To show that n <= Succ m, we can use the second constructor. *)
    apply LESucc.
    (* Now we can apply the induction hypothesis. *)
    apply IHless_than_equal.
    (* The goal is now reduced to a premise. *)
    apply H.
Qed.

(* Homework --- Exercise 9 *)
Lemma less_than_equal_shift (n m: nat):
  n <= m -> Succ n <= Succ m
.
Proof.
  intro.
  induction m.
  - simple inversion H.
    + rewrite <- H0.
      rewrite H1.
      apply LERefl.
    + discriminate.
  - simple inversion H.
    + rewrite <- H0.
      rewrite H1.
      apply LERefl.
    + rewrite <- H2.
      rewrite H1.
      inversion H2.
      intro.
      apply LESucc.
      apply IHm.
      apply H0.
Qed.

(* Any number that is at most zero must actually be zero. *)
Lemma less_than_equal_zero (n: nat):
  n <= 0 -> n = 0
.
Proof.
  (* Pull the premise into the context. *)
  intro.
  (* The "simple inversion" tactic considers each of the reasons why an
     inductive predicate might be true. *)
  simple inversion H.
  - (* First case: n <= 0 because there exists an n0 with n0 = 0 and n0 = n.
       Coq has already put the necessary premises in context. *)
    rewrite <- H0.
    apply H1.
  - (* Second case: n <= 0 because there exists an m with n <= m and also
       Succ m = 0. But that is absurd, because Succ and 0 are distinct
       constructors of nat. We can use "discriminate" to discharge the goal .*)
    discriminate.
Qed.

(* This relation truly encodes "less than or equal". *)
Lemma less_than_equal_succ (n m: nat):
  n <= Succ m -> n = Succ m \/ n <= m
.
Proof.
  intro.
  (* Invert the inductive predicate. *)
  simple inversion H.
  - (* First case: n <= Succ m by LERefl. This means that there exists an n0
       such that n = n0 and n0 = Succ m. We prove the left disjunct. *)
    left.
    rewrite <- H0, <- H1.
    reflexivity.
  - (* Second case: n <= Succ m by LESucc. This means that there exists an
       n0 such that n = n0, an m0 such that Succ m0 = m, and that n0 <= m0. *)
    intro.
    (* Because Succ m0 = Succ m, it follows that m = m0. *)
    inversion H2.
    (* We prove the right conjunct with some rewrites. *)
    right.
    rewrite <- H1, <- H4.
    apply H0.
Qed.

(* Homework --- Exercise 10 *)
Lemma less_than_equal_mono_add_left (n m k: nat):
  n <= m -> n + k <= m + k
.
Proof.
  intro.
  induction k.
  - simpl.
    apply H.
  - simpl.
    apply less_than_equal_shift.
    apply IHk.
Qed.

Lemma less_than_equal_mono_add (n m k l: nat):
  n <= m ->
  k <= l ->
  n + k <= m + l
.
Proof.
  intros.
  (* Prove that n + k <= m + k <= m + l. *)
  apply less_than_equal_trans with (m := m + k).
  - (* This follows from the monotonicity lemma. *)
    apply less_than_equal_mono_add_left.
    apply H.
  - (* The monotonicity lemma operates on the left, but addition commutes, so
       we swap the operands on both sides of the inequality around. *)
    rewrite add_commute.
    rewrite add_commute with (n := m).
    (* Now we can apply the monotonicity lemma again. *)
    apply less_than_equal_mono_add_left.
    apply H0.
Qed.

(* Homework --- Exercise 11, optional

   Hint: you can use the lemma above! *)
Lemma less_than_equal_mono_mul (n m k: nat):
  n <= m -> n * k <= m * k
.
Proof.
  intro.
  induction k.
  - simpl.
    apply LERefl.
  - simpl.
    apply less_than_equal_mono_add.
    + apply IHk.
    + apply H.
Qed.

(* Homework --- Exercise 12:

   We can also define "less than or equal" differently, by specifying that it
   is the inductive relation satisfying the following rules:
   * For all n, n is less than or equal to n.
   * For all n, n is less than or equal to Succ n.
   * For all n, if n is less than or equal to m, and m is less than or equal to
     k, then n is less than or equal to k.

   Work out this definition by filling out the three-clause inductive below.
*)
Reserved Notation "n <== m" (at level 70, no associativity).
Inductive less_than_equal': nat -> nat -> Prop :=
| LE'Base: forall (n: nat), n <== n
| LE'Step: forall (n: nat), n <== Succ n
| LE'Trans: forall (n m k: nat), n <== m -> m <== k -> n <== k

(* Hint 2: Be sure to use the notation "<==" instead of "<="! *)
where "n <== m" := (less_than_equal' n m).

(* Homework --- Exercise 13, optional challenge

   Show that the two definitions of "less than or equal" are equivalent.

   Hint: split the "if and only if", and then proceed by induction on the
   construction of the premise. *)

Lemma le_defs_equivalent_ltr (n m: nat):
  n <= m -> n <== m
.
Proof.
  intro.
  induction m.
  - apply less_than_equal_zero in H.
    rewrite H.
    apply LE'Base.
  - inversion H.
    + apply LE'Base.
    + apply IHm in H2.
      (* I'm shocked that this even worked. *)
      apply (LE'Trans n m (Succ m) H2 (LE'Step m)).
Qed.

Lemma le_defs_equivalent_rtl (n m: nat):
  n <== m -> n <= m
.
Proof.
  (* ??? *)
Admitted.

Lemma le_defs_equivalent (n m: nat):
  n <= m <-> n <== m
.
Proof.
  split.
  - apply le_defs_equivalent_ltr.
  - apply le_defs_equivalent_rtl.
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
  simpl.
  rewrite add_commute.
  reflexivity.
Qed.

(* The Lucas numbers relate to the Fibonacci numbers as follows. *)
Lemma lucas_vs_fibonnaci (n: nat):
  lucas (Succ n) = fib n + fib (Succ (Succ n))
.
Proof.
  (* Let's give this a try using good old induction. *)
  induction n.
  - (* The base case is easy enough. *)
    simpl.
    reflexivity.
  - rewrite lucas_plus_two.
    rewrite IHn.
    (* No induction hypothesis about "lucas n"... we're stuck! *)
Abort.

(* Here is the induction principle that Coq generated for us, based on the
   definition of natural numbers. It is applied under the hood when we invoke
   the induction tactic. *)
Check nat_ind.

(* The second premise says: given that P holds for n, we can show that it
   holds for P (Succ n). But we need something stronger, namely that P m holds
   for all m <= n. This is known as strong induction.

   Fortunately, Coq allows us to add our own induction principles, as long as
   we can prove that they are sound. *)

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
  (* We prove something slightly stronger, namely that the predicate holds for
     all m less than or equal to n. *)
  enough (forall m, less_than_equal m n -> P m).
  - (* In our first subgoal, we should show that the stronger claim implies the
       end goal of this lemma. This works fairly easily. *)
    apply H.
    apply LERefl.
  - (* Now we proceed by plain induction on n, proving the stronger claim. *)
    induction n.
    + (* Pull the quantified variable and hypothesis into the context. *)
      intros.
      (* This lemma says that m = 0, provided that m <= 0. If we do a rewrite,
         Coq will give us two subgoals: the result of the rewrite, and another
         subgoal where we need to prove the premise. *)
      rewrite less_than_equal_zero.
      * (* This is exactly the base case. *)
        apply HBase.
      * (* This we already knew. *)
        apply H.
    + intros.
      (* Make a case distinction based on m <= n. *)
      destruct (less_than_equal_succ m n).
      * (* The first subgoal has us prove the premise of less_than_equal_succ,
           which is m <= Succ n. Fortunately, we have this in context. *)
        exact H.
      * (* In this case, m = Succ n. We can use the "subst" tactic to
           substitute Succ n for m everywhere. *)
        subst.
        (* This is where the strong induction hypothesis comes in. *)
        apply HStep.
        (* Unfold the definition of our shorthand. *)
        unfold holds_up_to.
        (* We now have the (weak) induction hypothesis. *)
        apply IHn.
      * (* In this case, m <= n; we apply the induction hypothesis. *)
        apply IHn.
        apply H0.
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
  (* We can now use the strong induction principle we showed above. *)
  induction n using strong_induction.
  - apply HBaseZero.
  - unfold holds_up_to in H.
    (* Note how the generated induction hypothesis applies to all numbers m
       less than or equal to n. We distinguish based on whether n is zero,
       or the successor of some other number. *)
    destruct n.
    + (* When n is zero, we apply the premise about one. *)
      apply HBaseOne.
    + (* Otherwise, we prove the property about P (Succ (Succ n)) by applying
         the premise HStep, which gives us two subgoals. *)
      apply HStep.
      * (* To prove the claim for n, apply the strong induction hypothesis. *)
        apply H.
        apply LESucc.
        apply LERefl.
      * (* The strong induction hypothesis also applies to Succ n. *)
        apply H.
        apply LERefl.
Qed.

Lemma lucas_vs_fibonnaci (n: nat):
  lucas (Succ n) = fib n + fib (Succ (Succ n))
.
Proof.
  (* Using our second induction principle, we can now prove our property. *)
  induction n using pair_induction.
  - (* First base case goes through. *)
    simpl.
    reflexivity.
  - (* As does the second base case. *)
    simpl.
    reflexivity.
  - (* Note how we have *two* induction hypotheses now. *)
    rewrite lucas_plus_two.
    rewrite IHn, IHn0.
    (* Move the terms of the sum around. *)
    rewrite add_exchange.
    (* Prove equality of operands *)
    f_equal.
    + rewrite fib_plus_two.
      reflexivity.
    + rewrite fib_plus_two with (n := Succ (Succ n)).
      reflexivity.
Qed.

(* Homework --- Exercise 14, optional

   Here is the last induction principle mentioned in the lecture. Can you
   prove that it is sound? Hint: this is easiest using strong induction. *)
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
Admitted.

(* Sum of the first n Fibonacci numbers. *)
Fixpoint sum_fib (n: nat): nat :=
  match n with
  | 0 => 0
  | Succ n' => fib n + sum_fib n'
  end
.

(* These two lemmas are useful for the proof that follows. *)
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

(* Homework --- Exercise 15, optional.

   Another Fibonacci property. Can you prove it using skip_induction? *)
Lemma sum_fib_direct (n: nat):
  Succ (sum_fib n) = fib (Succ (Succ n))
.
Proof.
Admitted.
