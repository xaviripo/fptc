(* Formalizing and Proving Theorems in Coq --- Homework 5, part c
   curated by Tobias Kappé, May 2022.

   There is one exercise in this file, in the form of a proof that you need
   to fill in. Remember that you may use all of the techniques we have seen. *)

(* Previously, we saw how to encode test-free PDL with proper negation. In
   this final demonstration, we will encode PDL proper, including tests. The
   challenge here is that not only can formulas contain programs, but programs
   can contain formulas as well. *)

(* We add variables P and A as before. *)
Variable (P: Type).
Variable (A: Type).

Record frame := {
  world: Type;
  val: P -> world -> Prop;
  acc: A -> world -> world -> Prop
}.

(* Our revised syntax for PDL, where we define formulas and programs in one
   fell swoop. Note the "with" directive, which allows the definition of a
   formula to refer to programs, and the definition of a program to refer in
   turn to formulas (in the PTest case). *)
Inductive formula :=
| FProp: P -> formula
| FDis: formula -> formula -> formula
| FNeg: formula -> formula
| FDiamond: program -> formula -> formula
with program :=
| PStep: A -> program
| PTest: formula -> program
| PSeq: program -> program -> program
| PChoice: program -> program -> program
| PStar: program -> program
.

Notation "# p" := (FProp p) (at level 35).
Notation "phi || psi" := (FDis phi psi) (at level 50, left associativity).
Notation "! phi" := (FNeg phi) (at level 40, no associativity).
Notation "'<<' pi '>>' phi" := (FDiamond pi phi) (at level 42, no associativity).

Notation "$ a" := (PStep a) (at level 40).
Notation "phi ?" := (PTest phi) (at level 40, left associativity).
Notation "pi ;; sigma" := (PSeq pi sigma) (at level 48, left associativity).
Notation "pi + sigma" := (PChoice pi sigma) (at level 50, left associativity).
Notation "pi *" := (PStar pi) (at level 40).

(* Let's also define conjunction as the dual to disjunction. *)
Definition FCon (phi psi: formula) := !(!phi || !psi).
Notation "phi && psi" := (FCon phi psi).

(* Because our syntax is now mutually recursive, we cannot use the previous
   trick of using an inductive to assign meaning to programs, while using a
   fixpoint to assign meaning to formulas. We really need a proper mutually
   recursive fixpoint to do this.

   The first attempt is given below. Unfortunately, we run into a problem. *)
Fail Fixpoint sat (f: frame) (phi: formula) (w: world f): Prop :=
  match phi with
  | #p =>
    val f p w
  | phi || psi =>
    sat f phi w \/ sat f psi w
  | ! phi =>
    ~ sat f phi w
  | << pi >> phi =>
    exists w', path f pi w w' /\ sat f phi w'
  end
with path (f: frame) (pi: program) (w1 w2: world f): Prop :=
  match pi with
  | $a =>
    acc f a w1 w2
  | phi ? =>
    w1 = w2 /\ sat f phi w1
  | pi ;; sigma =>
    exists w3, path f pi w1 w3 /\ path f sigma w3 w2
  | pi + sigma =>
    path f pi w1 w2 \/ path f sigma w1 w2
  | pi* =>
    (* Here is our problem: when defining the semantics of the star: we cannot
     * recurse on pi*, as that is not a strictly smaller term. *)
    w1 = w2 \/ exists w3, path f pi w1 w3 /\ path f (pi*) w3 w2
  end
.

(* We can get around this by defining an inductive that encodes the reflexive
   and transitive closure of a relation. Here, P is a relation encoded as a
   predicate on pairs, and the inductive below represents its closure. *)
Inductive closure {X: Type} (P: X -> X -> Prop): X -> X -> Prop :=
(* In the base case, every element of X is related to itself. *)
| CBase:
    forall x,
      closure P x x
(* In the inductive case, we note that if x is related to x', and x' is related
   by the transitive and reflexive closure of P to x'', then x is also related
   to x'' through the reflexive and transitive closure. *)
| CStep:
    forall x x' x'',
      P x x' ->
      closure P x' x'' ->
      closure P x x''
.

(* We can now use the closure inductive to properly define the semantics of
   formulas and programs by mutual recursion. Note now the definition of sat
   refers to that of path, and vice versa. *)
Fixpoint sat (f: frame) (phi: formula) (w: world f): Prop :=
  match phi with
  | #p =>
    val f p w
  | phi || psi =>
    sat f phi w \/ sat f psi w
  | ! phi =>
    ~ sat f phi w
  | << pi >> phi =>
    exists w', path f pi w w' /\ sat f phi w'
  end
with path (f: frame) (pi: program) (w1 w2: world f): Prop :=
  match pi with
  | $a =>
    acc f a w1 w2
  | phi ? =>
    w1 = w2 /\ sat f phi w1
  | pi ;; sigma =>
    exists w3, path f pi w1 w3 /\ path f sigma w3 w2
  | pi + sigma =>
    path f pi w1 w2 \/ path f sigma w1 w2
  | pi* =>
    closure (path f pi) w1 w2
  end
.

(* To prove the next lemma, we need to reason classically. *)
Require Import Coq.Logic.Classical.

(* Let's try and prove a property of the syntax that involves a test: if
   you have a test inside of a modality, then you can pull it out. Notice the
   use of our "syntactic sugar" for conjunction, defined above. *)
Lemma diamond_test (f: frame) (phi psi: formula) (w: world f):
  sat f (<<phi?>>psi) w <->
  sat f (phi && psi) w
.
Proof.
  (* We start by unrolling all of the definitions. *)
  simpl.
  (* Prove each of the implications separately. *)
  split; intros.
  - (* We have a world w' that is equal to w and satisfies phi. Use the
       destruct tactic to obtain this world and its properties. *)
    destruct H.
    (* Now we pull apart the hypotheses some more. *)
    destruct H.
    destruct H.
    (* This tactic finds H: w = x, and substitutes x for w everywhere. *)
    subst.
    (* The remainder can be proved intuitionistically. *)
    intuition.
  - (* We assert that we are already in a world satisfying phi. *)
    exists w.
    (* Use one of DeMorgan's law to simplify the hypothesis. *)
    apply not_or_and in H.
    destruct H.
    (* Split up the goal; Coq discharges the trivial w = w clause. *)
    repeat split.
    + (* We reason clasically here. *)
      now apply NNPP.
    + (* Analogous to the previous case. *)
      now apply NNPP.
Qed.

(* Homework --- Exercise 3, optional challenge: prove the diamond fixpoint
   lemma one last time, using the new semantics.

   Hint 1: Remember that you can prove properties by induction on inductive
   predicates, and that "closure" is an inductive predicate.

   Hint 2: Remember that you can destruct implications H: A -> B \/ C, which
   will give you goals to prove A, as well as two goals where you need to prove
   your current goal assuming B or C respectively. *)
Lemma diamond_fixpoint (f: frame) (pi: program) (phi: formula) (w: world f):
  sat f (<< pi* >> phi) w <-> sat f (phi || << pi ;; pi* >> phi) w
.
Proof.
  simpl.
  split; intro.
  - destruct H.
    destruct H.
    induction H.
    + now left.
    + right.
      destruct IHclosure.
      * easy.
      * exists x''.
        intuition.
        now exists x'.
      * (* Poor H2 *)
        destruct H2.
        destruct H2.
        destruct H2.
        destruct H2.
        exists x''.
        split; try easy.
        now exists x'.
  - induction H.
    + exists w.
      intuition.
      apply CBase.
    + destruct H.
      destruct H.
      destruct H.
      destruct H.
      exists x.
      split.
      * now apply CStep with (x' := x0).
      * easy.
Qed.
