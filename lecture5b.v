(* Formalizing and Proving Theorems in Coq --- Homework 5, part b
   curated by Tobias Kappé, May 2022.

   There is one exercise in this file, in the form of a proof that you need
   to fill in. Remember that you may use all of the techniques we have seen. *)

(* In the last demonstration, we encoded test-free PDL in negation normal form:
   with positive and negative propositions, disjunctions and conjunctions,
   and both the diamond and box modalities, but without a negation. In this
   file, we consider a more concise syntax, with only positive propositions,
   disjunction, and the diamond modality, that *does* include negation. *)

(* We add variables P and A as before. *)
Variable (P: Type).
Variable (A: Type).

(* The definition of models also stays the same. *)
Record frame := {
  world: Type;
  val: P -> world -> Prop;
  acc: A -> world -> world -> Prop
}.

(* As does the syntax and semantics for programs. *)
Inductive program :=
| PStep: A -> program
| PSeq: program -> program -> program
| PChoice: program -> program -> program
| PStar: program -> program
.

Notation "$ a" := (PStep a) (at level 40).
Notation "pi ;; sigma" := (PSeq pi sigma) (at level 48, left associativity).
Notation "pi + sigma" := (PChoice pi sigma) (at level 50, left associativity).
Notation "pi *" := (PStar pi) (at level 40).

Inductive path (f: frame): program -> world f -> world f -> Prop :=
| PathStep:
    forall (w1 w2: world f) (a: A),
      acc f a w1 w2 ->
      path f ($ a) w1 w2
| PathSeq:
    forall (w1 w2 w3: world f) (pi sigma: program),
      path f pi w1 w2 ->
      path f sigma w2 w3 ->
      path f (pi ;; sigma) w1 w3
| PathChoiceLeft:
    forall (w1 w2: world f) (pi sigma: program),
      path f pi w1 w2 ->
      path f (pi + sigma) w1 w2
| PathChoiceRight:
    forall (w1 w2: world f) (pi sigma: program),
      path f sigma w1 w2 ->
      path f (pi + sigma) w1 w2
| PathStarBase:
    forall (w1 w2: world f) (pi: program),
      w1 = w2 ->
      path f (pi*) w1 w2
| PathStarStep:
    forall (w1 w2 w3: world f) (pi: program),
      path f pi w1 w2 ->
      path f (pi*) w2 w3 ->
      path f (pi*) w1 w3
.

(* Here is our more compact syntax for test-free PDL. *)
Inductive formula :=
| FProp: P -> formula
| FDis: formula -> formula -> formula
| FNeg: formula -> formula
| FDiamond: program -> formula -> formula
.

Notation "# p" := (FProp p) (at level 35).
Notation "phi || psi" := (FDis phi psi) (at level 50, left associativity).
Notation "! phi" := (FNeg phi) (at level 40, no associativity).
Notation "'<<' pi '>>' phi" := (FDiamond pi phi) (at level 42, no associativity).

(* When we try to define its semantics using an inductive as before, we run
   into a problem: we are not allowed to have negated invocations of the
   inductive being built as the premise, due to the way Coq's logic is set
   up --- if this were allowed, problems would arise. *)
Fail Inductive sat (f: frame): formula -> world f -> Prop :=
| SatProp:
    forall (w: world f) (p: P),
      val f p w -> sat f (# p) w
| SatDisLeft:
    forall (w: world f) (phi psi: formula),
      sat f phi w ->
      sat f (phi || psi) w
| SatDisRight:
    forall (w: world f) (phi psi: formula),
      sat f psi w ->
      sat f (phi || psi) w
| SatNeg:
    forall (w: world f) (phi: formula),
      (* This is where the problem lies. *)
      ~sat f phi w ->
      sat f (!phi) w
| SatDiamond:
    forall (w1 w2: world f) (pi: program) (phi: formula),
      path f pi w1 w2 ->
      sat f phi w2 ->
      sat f (<< pi >> phi) w1
.

(* Fortunately, we can still define a sensible semantics using a fixpoint
   instead of an inductive. This circumvents Coq's limitations. *)
Fixpoint sat (f: frame) (phi: formula) (w: world f): Prop :=
  match phi with
  | #p =>
    val f p w
  | phi || psi =>
    sat f phi w \/ sat f psi w
  | ! phi =>
    (* This is fine --- we are recursing on a smaller formula. *)
    ~ sat f phi w
  | << pi >> phi =>
    (* Here, we explicitly have to specify that there exists a world w' that
       is reachable from w throgh pi. We will see how to reason using this
       "exists" quantifier in a moment. *)
    exists w', path f pi w w' /\ sat f phi w'
  end.

(* Let's re-prove the diamond-disjunction lemma from before, with respect to
   the new syntax. *)
Lemma diamond_disjunction
  (f: frame)
  (pi: program)
  (phi psi: formula)
  (w: world f)
:
  sat f (<< pi >>(phi || psi)) w <->
  sat f (<< pi >> phi || << pi >> psi) w
.
Proof.
  (* First, we let the semantics do its thing, and unfold the meaning of each
     of the formulas on both sides of the equivalence. *)
  simpl.
  (* We prove each side of the implication separately. *)
  split; intros.
  - (* We have an existential hypothesis, which we can now destruct to obtain
       a world an a hypothesis encoding the requirements. *)
    destruct H.
    (* Next we destruct the conjunction into two. *)
    destruct H.
    (* Do a case analysis on the disjunction here. *)
    destruct H0.
    + (* We have a world x that is reachable thorugh pi, satisfying phi. That
         means that we can try and prove the left disjunct. *)
      left.
      (* To prove an existential, you need to provide a witness using the
         "exists" tactic. Here, we provide the witness w. *)
      exists x.
      (* Finally, we should prove the constraint on the quantified variable.
         Notice how x was filled in for w' w.r.t. the previous step. Luckily,
         we have both of these conjuncts as a premise by this point. *)
      intuition.
    + (* In the case where we have a world w reachable through pi satisfying
         psi instead, we prove the right conjunct using the same strategy. *)
      right.
      exists x.
      intuition.
  - (* For the other implication, we consider each of the cases. *)
    destruct H.
    + (* In case there exist sa world w' that is reachable through pi from w,
         and also satisfies phi, we obtain this world by destructing. Notice
         how the world we obtain is called x after this. *)
      destruct H.
      (* Tear the disjunction into two. *)
      destruct H.
      (* We specify the world we just obtained as a witness. *)
      exists x.
      (* We still need to prove the restrictions on x. *)
      intuition.
    + (* This case is treated similarly to the one above. *)
      destruct H.
      destruct H.
      exists x.
      intuition.
Qed.

(* Homework --- Exercise 2: Complete a proof of the diamond_fixpoint lemma
   from the previous demonstration, but with respect to the new semantics.

   Hint: Remember the "destruct" and "exists" tactics that were used to deal
   with existentials in the previous proof, as well as the inversion_clear
   tactic that we have seen as well. *)
Lemma diamond_fixpoint (f: frame) (pi: program) (phi: formula) (w: world f):
  sat f (<< pi* >> phi) w <-> sat f (phi || << pi ;; pi* >> phi) w
.
Proof.
Admitted.
