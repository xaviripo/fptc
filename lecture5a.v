(* Formalizing and Proving Theorems in Coq --- Homework 5, part a
   curated by Tobias Kappé, May 2022.

   There is one exercise in this file, in the form of a proof that you need
   to fill in. Remember that you may use all of the techniques we have seen. *)

(* For this demonstration, we are going to formalize a version of propositional
   dynamic logic (PDL). As you may know, the language of PDL is parameterized
   over a set of propositions and actions. We use Coq's 'Variable' vernacular
   to say that P and A stand in for arbitrary types. *)
Variable (P: Type).
Variable (A: Type).

(* A frame is a triple (world, val, acc) where world is a set, val assigns to
   every proposition a set of worlds where it holds, and acc assigns to every
   action a relation on worlds.

   We encode this as a Coq record, where 'world' is a type holding the worlds,
   'val' is a function that assigns to every proposition a set of worlds (here
   modelled as a predicate on worlds), and 'acc' is a function that assigns to
   each action a relation on worlds (here modelled as a predicate on pairs of
   worlds) .*)
Record frame := {
  world: Type;
  val: P -> world -> Prop;
  acc: A -> world -> world -> Prop
}.

(* In this version of PDL, programs are built from primitive steps, sequential
   composition, choice, and Kleene star. Note that we omit tests (for now). *)
Inductive program :=
| PStep: A -> program
| PSeq: program -> program -> program
| PChoice: program -> program -> program
| PStar: program -> program
.

(* We introduce some notation to make our lives easier. We cannot have a bare
   symbol "a" stand in for an action, so we mark it with a dollar sign. *)
Notation "$ a" := (PStep a) (at level 40).
Notation "pi ;; sigma" := (PSeq pi sigma) (at level 48, left associativity).
Notation "pi + sigma" := (PChoice pi sigma) (at level 50, left associativity).
Notation "pi *" := (PStar pi) (at level 40).

(* Every program defines a relation between the worlds of a frame. To this end,
   we define an inductive relation that says when two worlds are connected by
   a given program. *)
Inductive path (f: frame): program -> world f -> world f -> Prop :=
(* In the base step, the program $a connects all of the worlds that are
   connected by the accessibility relation. *)
| PathStep:
    forall (w1 w2: world f) (a: A),
      acc f a w1 w2 ->
      path f ($ a) w1 w2
(* A sequentially composed path connects all worlds that are connected by first
   going through an intermediate world. *)
| PathSeq:
    forall (w1 w2 w3: world f) (pi sigma: program),
      path f pi w1 w2 ->
      path f sigma w2 w3 ->
      path f (pi ;; sigma) w1 w3
(* Program choice takes the union of paths allowed by either program. *)
| PathChoiceLeft:
    forall (w1 w2: world f) (pi sigma: program),
      path f pi w1 w2 ->
      path f (pi + sigma) w1 w2
| PathChoiceRight:
    forall (w1 w2: world f) (pi sigma: program),
      path f sigma w1 w2 ->
      path f (pi + sigma) w1 w2
(* A Kleene star allows you to take a unit step (not moving at all) or
   traverse the program below the star first, and then resume by traversing
   the starred program again. *)
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

(* Formulas are built from positive propositions, negative propositions,
   disjunctions, conjunctions, and the diamond and box modalities. The latter
   of these involve programs. The syntax is as follows: *)
Inductive formula :=
| FPropPos: P -> formula
| FPropNeg: P -> formula
| FDis: formula -> formula -> formula
| FCon: formula -> formula -> formula
| FDiamond: program -> formula -> formula
| FBox: program -> formula -> formula
.

(* As before, some syntax that should make reading easier. *)
Notation "+ p" := (FPropPos p) (at level 35).
Notation "- p" := (FPropNeg p).
Notation "phi || psi" := (FDis phi psi) (at level 50, left associativity).
Notation "phi && psi" := (FCon phi psi) (at level 40, left associativity).
Notation "'<<' pi '>>' phi" := (FDiamond pi phi) (at level 42, no associativity).
Notation "'[[' pi ']]' phi" := (FBox pi phi) (at level 42, no associativity).

(* We are now ready to define the semantics of our version of PDL, also as an
   inductive. In this case, it tells us when a formula is satisfied by a world
   inside a given frame. *)
Inductive sat (f: frame): formula -> world f -> Prop :=
(* Positive propositions hold if they are valued positively at this world. *)
| SatPropPos:
    forall (w: world f) (p: P),
      val f p w -> sat f (+ p) w
(* Negative propositions hold if they are valued negatively here. *)
| SatPropNeg:
    forall (w: world f) (p: P),
      ~val f p w -> sat f (- p) w
(* Disjunctions hold if either of their disjuncts hold. *)
| SatDisLeft:
    forall (w: world f) (phi psi: formula),
      sat f phi w ->
      sat f (phi || psi) w
| SatDisRight:
    forall (w: world f) (phi psi: formula),
      sat f psi w ->
      sat f (phi || psi) w
(* Conunctions hold if both of their conjuncts hold. *)
| SatCon:
    forall (w: world f) (phi psi: formula),
      sat f phi w ->
      sat f psi w ->
      sat f (phi && psi) w
(* The diamond modality asserts that for *some* world accessible from the
   current world through the program inside the diamond , the modulated
   formula also holds. *)
| SatDiamond:
    forall (w1 w2: world f) (pi: program) (phi: formula),
      path f pi w1 w2 ->
      sat f phi w2 ->
      sat f (<< pi >> phi) w1
(* The box modality asserts the dual: for *every* world accessible from the
   current world through the program inside the box, the modulated formula
   also holds. *)
| SatBox:
    forall (w: world f) (pi: program) (phi: formula),
      (forall w',
        path f pi w w' ->
        sat f phi w') ->
      sat f ([[ pi ]] phi) w
.

(* We can now write proofs about the semantics we gave. For instance,
   disjunction distributes over the diamond modality, or in other words, the
   formula <<pi>>(phi || psi) is equivalent to <<pi>phi || <<pi>>psi. *)
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
  (* We prove each of the implications separately. *)
  split; intros.
  - (* The inversion_clear tactic asks: what could have been the reason that
       sat f (<<pi>>(phi || psi)) w holds? By definition, there can only be
       one reason, namely that phi || psi is satisfied at some world reachable
       from w by executing pi. *)
    inversion_clear H.
    (* We ask a similar question again: why does sat f (phi || psi) w2 hold?
       In this case, there can be two reasons, namely either that
       sat f phi w2 or sat f psi w2 hold. This gives us two cases. *)
    inversion_clear H1.
    + (* In the first case, we prove the left disjunct. *)
      apply SatDisLeft.
      (* We have a world reachable from w by executing pi where phi holds,
         namely w2. This means we can apply the SatDiamond rule and be done. *)
      now apply SatDiamond with (w2 := w2).
    + (* The second case works analogously by proving the right disjunct. *)
      apply SatDisRight.
      now apply SatDiamond with (w2 := w2).
  - (* This time, we ask why sat f (<<pi>>phi || <<pi>>psi) holds. As before,
       there can be two reasons, depending on which disjunct holds. *)
    inversion_clear H.
    + (* We deconstruct sat f (<<pi>>phi) w to find the world reachaed after
         executing pi from w that also satisfies phi. *)
      inversion_clear H0.
      (* Now we can apply the diamond rule using this world. *)
      apply SatDiamond with (w2 := w2).
      * (* We need to show that w2 can be reached after executing pi *)
        apply H.
      * (* And that w2 satisfies phi || psi. *)
        now apply SatDisLeft.
    + (* Analogous to the case above, but for the right disjunct. *)
      inversion_clear H0.
      apply SatDiamond with (w2 := w2).
      * apply H.
      * now apply SatDisRight.
Qed.

(* Here we prove another well-known rule of PDL, namely that the Kleene star
   can be "unrolled" into a zero-step or at-least-one-step program. *)
Lemma diamond_fixpoint (f: frame) (pi: program) (phi: formula) (w: world f):
  sat f (<< pi* >> phi) w <-> sat f (phi || << pi ;; pi* >> phi) w
.
Proof.
  (* Prove each of the implications separately again. *)
  split; intro.
  - inversion_clear H.
    inversion_clear H0.
    + apply SatDisLeft.
      now rewrite H.
    + apply SatDisRight.
      apply SatDiamond with (w2 := w2).
      * now apply PathSeq with (w2 := w0).
      * apply H1.
  - inversion_clear H.
    + apply SatDiamond with (w2 := w).
      * now apply PathStarBase.
      * apply H0.
    + inversion_clear H0.
      inversion_clear H.
      apply SatDiamond with (w2 := w2).
      * now apply PathStarStep with (w2 := w0).
      * apply H1.
Qed.

(* Homework --- Exercise 1: Complete the proof of the dual property to the
   previous lemma, i.e., the unrolling property for the Kleene star as it
   appears in the box modality.

   Hint 1: the reference solution uses about 20 lines. Your solution may be
   longer than this, and that is okay, but do not overcomplicate.

   Hint 2: As before, working this out using pen and paper helps a lot! *)
Lemma box_fixpoint (f: frame) (pi: program) (phi: formula) (w: world f):
  sat f ([[ pi* ]] phi) w <-> sat f (phi && [[ pi ;; pi* ]] phi) w
.
Proof.
Admitted.
