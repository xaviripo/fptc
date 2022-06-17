(* Formalizing and Proving Theorems in Coq --- Homework 6
   curated by Tobias Kappé, May 2022.

   For these exercises, proceed as before: find the lemmas marked as homework,
   and solve them using the techniques we discussed in class. *)

(* We use our earlier formalization of "less than or equal". *)
Inductive less_than_equal: nat -> nat -> Prop :=
| LERefl: forall (n: nat), n <= n
| LESucc: forall (n m: nat), n <= m -> n <= S m
where "n <= m" := (less_than_equal n m).

(* Let's prove that zero is less than or equal to two. *)
Lemma zero_less_than_two: 0 <= 2.
Proof.
  apply LESucc.
  apply LESucc.
  apply LERefl.
Qed.

(* If proofs are programs, what is this program? *)
Print zero_less_than_two.

(* Let's do that again, and show the intermediate programs. *)
Lemma zero_less_than_two': 0 <= 2.
Proof.
  Show Proof.
  apply LESucc.
  Show Proof.
  apply LESucc.
  Show Proof.
  apply LERefl.
Qed.

(* Okay, can we do that in one go? It turns out we can! *)
Lemma zero_less_than_two'': 0 <= 2.
Proof.
  apply (LESucc 0 1 (LESucc 0 0 (LERefl 0))).
Qed.

(* Alternatively, we can just *define* our proof like this. *)
Definition zero_less_than_two''': 0 <= 2 :=
  LESucc 0 1 (LESucc 0 0 (LERefl 0))
.

(* Here is a function that takes a natural number and adds two. *)
Definition add_two (n: nat): nat :=
  S (S n)
.

Print add_two.

(* We can ask Coq to evaluate this function on some input. *)
Compute (add_two 0).

(* Another way to accomplish this is to write the term in proof mode! *)
Definition add_two' (n: nat): nat.
Proof.
  Show Proof.
  apply S.
  Show Proof.
  apply S.
  Show Proof.
  apply n.
Qed.

(* We can verify that the same program was built. *)
Print add_two'.

(* But something is off when we try to compute with it. *)
Compute (add_two' 0).

(* It turns out that proofs are opaque --- they do not unfold when computing.
   In this case, we should close the proof using "Defined" instead. *)
Definition add_two'' (n: nat): nat.
Proof.
  apply S.
  apply S.
  apply n.
Defined.

(* Now computation is possible. *)
Compute (add_two'' 0).

(* Okay, how about a lemma that has a premise? *)
Lemma shift_two (n m: nat):
  n <= m -> n <= S (S m)
.
Proof.
  intros.
  apply LESucc.
  apply LESucc.
  apply H.
Qed.

(* The associated is now a *function* transforming one proof into another. *)
Print shift_two.

(* We can also define it directly, like this. *)
Definition shift_two' (n m: nat) (H: n <= m): n <= S (S m) :=
  LESucc n (S m) (LESucc n m H)
.

(* Implications are truth transformers. For instance, the transitivity
   property can be "implemented" by returning a function that feeds evidence
   for the antecedent through both implications. *)
Definition impl_trans (P Q R: Prop) (H0: P -> Q) (H1: Q -> R): P -> R :=
  fun (H2: P) => H1 (H0 H2)
.

(* Indeed, this is the type one would expect. *)
Check impl_trans.

(* What about True? It's an inductive with one (constant) constructor. *)
Print True.

(* We can always obtain a proof of True using the constant I. *)
Definition true: True := I.

(* How about disjunction? That's an inductive with two constructors: one for
   the left disjunct, and one for the right; both require a proof. *)
Locate "\/".
Print or.

(* We can also construct proofs for disjunctions explicitly. *)
Definition true_or_false: True \/ False :=
  or_introl I
.

(* A conjunction is an inductive with one constructor, which takes proofs for
   both conjuncts as input. *)
Locate "/\".
Print and.

(* For instance, here is an explicit proof of a conjunction. *)
Definition true_and_true: True /\ True :=
  conj I I
.

(* We can also explicitly construct the commutativity of implication. *)
Definition and_comm (P Q: Prop) (H: P /\ Q): Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end
.

(* Notice how this definition has the same type as our earlier proof! *)
Check and_comm.

(* The "if and only if" operator is a conjunction of implications. *)
Locate "<->".
Print iff.

(* That means that we can state this form of commutativity as follows. *)
Definition and_comm_iff (P Q: Prop): P /\ Q <-> Q /\ P :=
  conj (and_comm P Q) (and_comm Q P)
.

(* Analogously, we can define commutativity of disjunction.

   Homework --- Exercise 1: Complete the following definition.

   Hint: Look at the definition of "or". It's an inductive with two
   constructors. That means you should be able to perform a "match" on it
   (analogous to and_comm above, but for different constructors). *)
Definition or_comm (P Q: Prop) (H: P \/ Q): Q \/ P :=
  match H with
  | or_introl HP => or_intror HP
  | or_intror HQ => or_introl HQ
  end
.

(* Again, the type of this object matches the earlier proof. *)
Check or_comm.

(* False is an inductive with *no* constructors. *)
Print False.

(* Here is one reason why Coq does not allow non-terminating programs: the
   program below may seem well-typed, because it promises to return an
   instance of False, and does so by calling *itself*. But this would mean
   that we could construct an instance of False by calling "falso 0" --- which
   would allow us to prove everything! *)
Fail Fixpoint falso (n: nat): False := falso n.

(* We can convert a proof of P /\ Q -> R into a proof of P -> Q -> R. The idea
   here is to return a function that takes proofs of P and Q, and returns a
   proof of R. This function "calls" the hypothesis H with a proof of P /\ Q,
   constructed by putting the proofs of P and Q together. *)
Definition curry (P Q R: Prop) (H: P /\ Q -> R): P -> Q -> R :=
  fun (HP: P) (HQ: Q) => H (conj HP HQ)
.

(* Conversely, we can construct a proof of P /\ Q -> R from a proof of
   P -> Q -> R, by returning a function that takes a proof of P /\ Q, and
   uses the proofs of P and Q contained therein to "call" the hypothesis H.

   Homework --- Exercise 2: complete the following definition.

   Hint: Remember that your function should be returning another function.
   You can use the "fun" syntax demonstrated above to accomplish this. *)
Definition uncurry (P Q R: Prop) (H: P -> Q -> R): P /\ Q -> R :=
  fun (Hand: P /\ Q) => match Hand with
  | conj HP HQ => H HP HQ
  end
.

(* Here is an object with a type that involves a "forall". It claims that for
   all n, it holds that 0 <= n; on a typing level, this means that it takes
   a number n, and returns a proof of 0 <= n. *)
Lemma zero_least: forall (n: nat), 0 <= n.
Proof.
  intros.
  induction n.
  - apply LERefl.
  - apply LESucc.
    apply IHn.
Qed.

(* What does this proof look like as a term? It turns out that it uses the
   induction principle nat_ind under the hood! *)
Print zero_least.
Check nat_ind.

(* The keyword "exists" is just notation for another inductive with just one
   constructor, which takes a value n and a proof of P(n). *)
Locate "exists".
Unset Printing Notations.
Print ex.
Set Printing Notations.

(* Here is an example of a term that involves an existential. *)
Lemma zero_least_ex: exists (n: nat), n <= 0.
Proof.
  exists 0.
  apply LERefl.
Qed.

Print zero_least_ex.

(* Homework --- Exercise 3: Complete the following definition.

   Hint: the input H that you get is a proof of (P \/ Q) \/ R. That means
   you can perform a match on it as before; the left branch will be a proof
   of P \/ Q, which requires a further match. Can you construct an
   appropriate proof of P \/ (Q \/ R) in each branch? *)
Definition disj_associative (P Q R: Prop) (H: (P \/ Q) \/ R): P \/ (Q \/ R) :=
  match H with
  | or_introl Hor => match Hor with
    | or_introl HP => or_introl HP
    | or_intror HQ => or_intror (or_introl HQ)
    end
  | or_intror HR => or_intror (or_intror HR)
  end
.

(* Homework --- Exercise 4: Complete the following definition. *)
Definition conj_distributes (P Q R: Prop) (H: (P /\ Q) \/ (P /\ R)): P /\ (Q \/ R) :=
  match H with
  | or_introl (conj HP HQ) => conj HP (or_introl HQ)
  | or_intror (conj HP HR) => conj HP (or_intror HR)
  end
.
