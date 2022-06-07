(* Formalizing and Proving Theorems in Coq --- Homework 1.
   curated by Tobias Kappé, May 2022.

   For today's exercises, you should complete all of the lemmas marked with
   "Homework" below.

   Note that this includes the lemma that we admitted during the lecture, and
   that this lemma does not appear at the end of the file. Your safest bet is
   to just search for "Homework" in this file, and complete the lemmas. Do
   not forget to close your lemma with "Qed." once Coq is happy.

   When proving these lemmas, you may use all of the tactics that we saw in
   the lecture (they also appear in this file). You may *not* use any of the
   other tactics, including in particular automation like "intuition". *)

Require Import Coq.Setoids.Setoid.

(* Conjunction is commutative *)
Lemma conj_commutes (P Q: Prop):
  P /\ Q -> Q /\ P
.
Proof.
  (* To prove an implication, assume the premise. *)
  intro.
  (* Break the conjunction in two premises. *)
  destruct H.
  (* Prove both parts of the conjunction goal. *)
  split.
  (* We have a premise matching this goal... *)
  exact H0.
  (* ... and another premise for the other. *)
  exact H.
  (* We can now close the proof. *)
Qed.

(* Nicer version of the last proof. *)
Lemma conj_commutes_alternative (P Q: Prop):
  P /\ Q -> Q /\ P
.
Proof.
  (* The first three steps are as before. *)
  intro.
  destruct H.
  split.
  (* Now, focus on either goal. *)
  - exact H0.
  - exact H.
Qed.

(* The dual: disjunction commutes *)
Lemma disj_commutes (P Q: Prop):
  P \/ Q -> Q \/ P
.
Proof.
  (* Take the premise in our context again. *)
  intro.
  (* A case distinction on the premise.
     Note how the tactic is the same as before. *)
  destruct H.
  (* We are now left with two possible cases. *)
  - (* In the first case, P holds. We can then
       prove the right disjunct of the goal. *)
    right.
    (* The goal is now a premise. *)
    exact H.
  - (* In the second case, Q holds, so we operate
       on the left disjunct of the goal. *)
    left.
    (* The goal is a premise again. *)
    exact H.
Qed.

(* Commutativity goes both ways. *)
Lemma conj_commutes_iff (P Q: Prop):
  P /\ Q <-> Q /\ P
.
Proof.
  (* To prove an if-and-only-if, we prove both directions. *)
  split.
  (* We now have two subgoals, one for each direction.*)
  - (* Pull the premise into the hypotheses. *)
    intro.
    (* Apply the lemma we wrote above. *)
    apply conj_commutes.
    (* We now have the goal as hypothesis. *)
    exact H.
  - (* Pull the premise into the hypotheses, again. *)
    intro.
    (* Apply the lemma above. Note how Coq matches
       P and Q to Q and P respectively! *)
    apply conj_commutes.
    (* Finally we have the goal as hypothesis. *)
    exact H.
Qed.

(* Distributivity of conjunction over disjunction. *)
Lemma conj_distributes (P Q R: Prop):
  (P /\ Q) \/ (P /\ R) -> P /\ (Q \/ R)
.
Proof.
  (* As always, start by pulling in the premise. *)
  intro.
  (* A case distinction on the hypothesis. *)
  destruct H.
  - (* Split up the hypothesis obtained from the case. *)
    destruct H.
    (* Prove each conjunct separately *)
    split.
    + (* This is part of our hypotheses. *)
      exact H.
    + (* The right disjunct is part of our premises. *)
      left.
      exact H0.
  - (* Symmetric to the other case. *)
    destruct H.
    split.
    + exact H.
    + right.
      exact H0.
Qed.

(* As above, but on the right instead of the left. *)
Lemma conj_distributes' (P Q R: Prop):
  (P /\ R) \/ (Q /\ R) -> (P \/ Q) /\ R
.
Proof.
  (* Pull the premise into the hypotheses. *)
  intro.
  (* Switch around the conjuncts using the earlier lemma. *)
  apply conj_commutes.
  (* Apply the other distributivity lemma from before. *)
  apply conj_distributes.
  (* A case analysis on the premise. *)
  destruct H.
  - (* Choose to prove the left disjunct. *)
    left.
    (* Apply the commutativity lemma from before. *)
    apply conj_commutes.
    (* The goal is now a premise. *)
    exact H.
  - (* Symmetric to the other case. *)
    right.
    apply conj_commutes.
    exact H.
Qed.

(* Complement to the above. *)
Lemma conj_distributes_compl (P Q R: Prop):
  P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R)
.
Proof.
  (* Start by pulling the premise in. *)
  intro.
  (* Break the conjunction in two. *)
  destruct H.
  (* A case distinction on the disjunction. *)
  destruct H0.
  - (* We choose the left disjunct. *)
    left.
    (* Prove each conjunct separately. *)
    split.
    (* Both cases are covered by a premise. *)
    + exact H.
    + exact H0.
  - (* Analogous to the other case. *)
    right.
    split.
    + exact H.
    + exact H0.
Qed.

(* As before, but on the right-hand side. *)
Lemma conj_distributes_compl' (P Q R: Prop):
  (Q \/ R) /\ P -> (Q /\ P) \/ (R /\ P)
.
Proof.
  (* The same pattern as before. *)
  intro.
  (* We cannot apply conj_commutes, because the goal is a disjunction.
     However, we *can* do a rewrite using the if-and-only-if version.
     This flips around the arguments of the conjunction on the left. *)
  rewrite conj_commutes_iff.
  (* Issuing the command above again will just flip the operands of the
     left conjunction, arriving back where we started -- not ideal.
     One thing we can do is guide the rewrite by specifying the argument.
     This flips the operands of the conjunction on the right. *)
  rewrite conj_commutes_iff with (P := R).
  (* Now we can apply the distributivity lemma as before. *)
  apply conj_distributes_compl.
  (* Flip the operands again to obtain a goal equal to a hypothesis. *)
  apply conj_commutes.
  exact H.
Qed.

(* Like the last proof, but a different approach. *)
Lemma conj_distributes_compl'_alternative (P Q R: Prop):
  (Q \/ R) /\ P -> (Q /\ P) \/ (R /\ P)
.
Proof.
  (* As before. *)
  intro.
  (* We can apply commutativity of conjunction *on the premise*. *)
  apply conj_commutes in H.
  (* Next apply distributivity *on the premise*. *)
  apply conj_distributes_compl in H.
  (* Now we can do a case analysis on H. *)
  destruct H.
  - (* Flip the conjuncts in the premise. *)
    apply conj_commutes in H.
    (* H is now the left disjunct. *)
    left.
    exact H.
  - (* Symmetric to the previous case. *)
    apply conj_commutes in H.
    right.
    exact H.
Qed.

(* Homework --- Exercise 1 *)
Lemma disj_commutes_iff (P Q: Prop):
  P \/ Q <-> Q \/ P
.
Proof.
  split.
  - apply disj_commutes.
  - apply disj_commutes with (P := Q).
Qed.

(* Homework --- Exercise 2 *)
Lemma disj_distributes (P Q R: Prop):
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R)
.
Proof.
  (* Start by pulling the premise in. *)
  intro.
  (* Break the conjunction in two. *)
  destruct H.
  (* A case distinction on the disjunction. *)
  - split.
    + left.
      exact H.
    + left.
      exact H.
  - destruct H.
    split.
    + right.
      exact H.
    + right.
      exact H0.
Qed.

(* Homework --- Exercise 3 *)
Lemma disj_distributes_compl (P Q R: Prop):
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R)
.
Proof.
  intro.
  destruct H.
  destruct H.
  - left.
    exact H.
  - destruct H0.
    + left.
      exact H0.
    + right.
      split.
      * exact H.
      * exact H0.
Qed.

(* Homework --- Exercise 4 *)
Lemma disj_associative (P Q R: Prop):
  (P \/ Q) \/ R -> P \/ (Q \/ R)
.
Proof.
  intro.
  destruct H.
  - destruct H.
    + left.
      exact H.
    + right.
      left.
      exact H.
  - right.
    right.
    exact H.
Qed.

(* Homework --- Exercise 5 *)
Lemma disj_associative_compl (P Q R: Prop):
  P \/ (Q \/ R) -> (P \/ Q) \/ R
.
Proof.
  intro.
  destruct H.
  - left.
    left.
    exact H.
  - destruct H.
    + left.
      right.
      exact H.
    + right.
      exact H.
Qed.

(* Homework --- Exercise 6 *)
Lemma conj_associative (P Q R: Prop):
  (P /\ Q) /\ R -> P /\ (Q /\ R)
.
Proof.
  intro.
  split.
  - destruct H.
    destruct H.
    exact H.
  - destruct H.
    destruct H.
    split.
    + exact H1.
    + exact H0.
Qed.

(* Homework --- Exercise 7 *)
Lemma conj_associative_compl (P Q R: Prop):
  P /\ (Q /\ R) -> (P /\ Q) /\ R
.
Proof.
  intro.
  split.
  - split.
    + destruct H.
      exact H.
    + destruct H.
      destruct H0.
      exact H0.
  - destruct H.
    destruct H0.
    exact H1.
Qed.

Lemma introduce_double_negation (P: Prop):
  P -> ~~P
.
Proof.
  (* Pull the premise into the hypotheses, as always. *)
  intro.
  (* Recall that "~~P" is just notation for "~P -> False". This means that
     we can pull "~P" into the hypotheses with another "intro", as follows. *)
  intro.
  (* To prove False, we can apply "~P", which is notation for "P -> False". *)
  apply H0.
  (* Now all that remains is to prove P, but that's a hypothesis! *)
  exact H.
Qed.

(* Hint for these next exercises: keep in mind that in Coq, "~P" is just
   notation for "P -> False". That means two things:
   (1) you can apply a hypothesis of the form "~P" to prove "False", and
   (2) if your goal is of the form "~P", then you can "intro" it. *)

(* Homework --- Exercise 8 *)
Lemma demorgan_first (P Q: Prop):
  ~(P \/ Q) -> ~P /\ ~Q
.
Proof.
  intro.
  split.
  - intro.
    apply H.
    left.
    exact H0.
  - intro.
    apply H.
    right.
    exact H0.
Qed.

(* Homework --- Exercise 9 *)
Lemma demorgan_first_compl (P Q: Prop):
  ~P /\ ~Q -> ~(P \/ Q)
.
Proof.
  intro.
  intro.
  destruct H.
  destruct H0.
  - apply H.
    exact H0.
  - apply H1.
    exact H0.
Qed.

(* Homework --- Exercise 10 *)
Lemma demorgan_second (P Q: Prop):
  ~P \/ ~Q -> ~(P /\ Q)
.
Proof.
  intro.
  intro.
  destruct H.
  - destruct H0.
    apply H.
    exact H0.
  - destruct H0.
    apply H.
    exact H1.
Qed.

(* For the last DeMorgan law, we need to use double negation elimination,
   i.e., that ~~P -> P. Because Coq's underlying logic is intuitionistic,
   this law does not need to hold. Luckily, we can import it using the
   following statement: *)

Require Import Coq.Logic.Classical.

(* We now have a lemma called "NNPP", which asserts that ~~P -> P for all
   propositions P. You can apply it just like we applied conj_commutes
   above to prove the final law.

   Challenge: prove the lemma below by working *on the goal exclusively*.
   This means that you cannot use "apply ... in ..." to operate on your
   hypotheses (using "apply" is fine, though). You also do not need any
   of the earlier DeMorgan laws proved above, but you *do* need NNPP. *)

(* Homework --- Exercise 11, optional *)
Lemma demorgan_second_compl (P Q: Prop):
  ~(P /\ Q) -> ~P \/ ~Q
.
Proof.
  intro.
  apply NNPP.
  intro.
  apply H.
  apply introduce_double_negation.
  split.
  - apply NNPP.
    intro.
    apply H1.
    destruct H0.
    left.
    exact H1.
  - apply NNPP.
    intro.
    apply H1.
    destruct H0.
    right.
    exact H1.
Qed.
