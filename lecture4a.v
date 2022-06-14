(* Formalizing and Proving Theorems in Coq --- Homework 4, part a.
   curated by Tobias Kappé, May 2022.

   For these exercises, proceed as before: find the lemmas marked as homework,
   and solve them using the techniques we discussed in class. Don't hesitate
   to try and work these out on a piece of scrap paper first, and remember that
   you can also use all of the tactics discussed in previous lectures. *)

(* Here is how to build expressions in a group. *)
Inductive group_term (X: Type) :=
| GGenerator: X -> group_term X
| GUnit: group_term X
| GAdd: group_term X -> group_term X -> group_term X
| GInverse: group_term X -> group_term X
.

(* Let's make our life easier by using additive notation. *)
Notation "0" := (GUnit _).
Notation "u + v" := (GAdd _ u v) (at level 50, left associativity).
Notation "- u" := (GInverse _ u).

(* This is an encoding of the axioms of a group. *)
Inductive group_equivalence {X: Type}
  : group_term X -> group_term X -> Prop :=
(* Multiplication is associative. *)
| GAssoc:
    forall (u v w: group_term X),
      group_equivalence (u + (v + w)) ((u + v) + w)
(* The unit is neutral on the right. *)
| GUnitRight:
    forall (u: group_term X),
      group_equivalence (u + 0) u
(* The inverse cancels a term (on the right) *)
| GInverseRight:
    forall (u: group_term X),
      group_equivalence (u + -u) 0
(* Equivalence is reflexive. *)
| GRefl:
    forall (u: group_term X),
      group_equivalence u u
(* Equivalence is symmetric. *)
| GSymm:
    forall (u v: group_term X),
      group_equivalence u v ->
      group_equivalence v u
(* Equivalence is transitive. *)
| GTrans:
    forall (u v w: group_term X),
      group_equivalence u v ->
      group_equivalence v w ->
      group_equivalence u w
(* Equivalence is compatible with multiplication *)
| GCong:
    forall (u v u' v': group_term X),
      group_equivalence u v ->
      group_equivalence u' v' ->
      group_equivalence (u + u') (v + v')
.

(* Notation for equivalence will make things a bit easier to read. *)
Notation "u == v" := (group_equivalence u v) (at level 70, no associativity).

(* Everythipng that behaves like a unit *is* the unit. If you worked out this
   property using pen and paper, the reasoning could go as follows:

     e == e + 0              (unit)
       == e + (u + -u)       (inverse)
       == (e + u) + -u       (associativity)
       == u +- u             (premise)
       == 0                  (inverse)
*)
Lemma group_unit_unique {X: Type} (e u: group_term X):
  e + u == u ->
  e == 0
.
Proof.
  intros.
  (* We encode these steps in Coq. Try to follow along, and refer back to the
     derivation above if you get lost. For the first step, we need the
     intermediate expression "e + 0", so we apply the transitivity property. *)
  eapply GTrans.
  - (* This is where we fill out the evar for the intermediate property. *)
    apply GSymm.
    apply GUnitRight.
  - (* Notice how the evar ?v is now filled in by e + 0. The next intermediate
       form that we need is e + (u + -u), so transitivity is required again. *)
    eapply GTrans.
    + (* We need to fill out the evar again. This time, we use the congruence
         property to split it up in two parts, one equivalent to e and the
         other equivalent to 0. This gives us _two_ evars. *)
      apply GCong.
      * (* The e remains the same, so we apply reflexivity. *)
        apply GRefl.
      * (* The 0 turns into u + -u, so we use the inverse law. *)
        apply GSymm.
        apply GInverseRight.
    + (* Notice how we now have an evar for the thing being inverted; this will
         resolve itself in a moment. We need another intermediate.... *)
      eapply GTrans.
      * (* This time we just rearrange the brackets using associativity. *)
        apply GAssoc.
      * (* For our final intermediate expression, we substitute the e + ?u
           on the left with u, using H. This resolves the evar ?u. *)
        eapply GTrans.
        -- (* Match the  e + ?u with u, and leave -u untouched. *)
           apply GCong.
           ++ apply H.
           ++ apply GRefl.
        -- (* We are left with an instance of the inverse law --- the final
              step in the derivation above. *)
           apply GInverseRight.

  (* That was not a very nice proof. Let's abort this for now; we will give a
     nicer proof in a moment. *)
Abort.

(* Another standard group property: we can cancel addition on the right. On
   paper, the derivation looks as follows:

     u == u + 0           (unit)
       == u + (w + -w)    (inverse)
       == (u + w) + -w    (associativity)
       == (v + w) + -w    (premise)
       == v + (w + -w)    (associativity)
       == v + 0           (inverse)
       == v               (unit)
*)
Lemma group_cancellation {X: Type} (u v w: group_term X):
  u + w == v + w ->
  u == v
.
Proof.
  intro.
  (* Our first intermediate expression is u + 0. *)
  eapply GTrans.
  - apply GSymm.
    apply GUnitRight.
  - (* Next we move to u + (w + -w). *)
    eapply GTrans.
    + apply GCong.
      * (* Leave the u untouched. *)
        apply GRefl.
      * (* Replace the 0 with w + -w. *)
        apply GSymm.
        apply GInverseRight with (u := w).
    + (* We then reassociate the parentheses to the left. *)
      eapply GTrans.
      * apply GAssoc.
      * (* And now we are in a place to apply the premise. *)
        eapply GTrans.
        -- apply GCong.
           ++ (* Substitute u +w on the left with v + w. *)
              apply H.
           ++ apply GRefl.
        -- (* Reassociate brackets back to the right. *)
           eapply GTrans.
           ++ apply GSymm.
              apply GAssoc.
           ++ (* Substitute w + -w for 0 again. *)
              eapply GTrans.
              ** apply GCong.
                 --- apply GRefl.
                 --- apply GInverseRight.
              ** (* We are left with the unit law. *)
                 apply GUnitRight.

  (* Not a great proof again --- lots of ugly and deep nesting. Let's toss
     this for now and return to it later. *)
Abort.

(* The setoid library can help you do rewrites nicely. To use it, you first
   need to import it like this. *)
Require Import Coq.Setoids.Setoid.

(* Now we tell Coq that group_equivalence is a reflexive, symmetric and
   transitive relation. Note that we have to explicitly point it to the axioms
   that provide proofs of these properties. *)
Add Parametric Relation (X: Type) : (group_term X) group_equivalence
  reflexivity proved by GRefl
  symmetry proved by GSymm
  transitivity proved by GTrans
  as group_eq.

(* Another property is that if u == v and u' == v', then u + u' == v + v'. In
   technical terms, this makes the equivalence a *congruence* with respect to
   the group operation. This will be very useful in later rewrites. *)
Add Parametric Morphism (X: Type) : (GAdd X) with
  signature group_equivalence ==>
            group_equivalence ==>
            group_equivalence
  as group_mul_mor.
Proof.
  intros.
  (* Note the state of the proof obligation here. We know that x == y as well
     as x0 == y0, and need to prove that x + x0 == y + y0. *)
  now apply GCong.
Qed.

(* Let's now try to revisit the group cancellation lemma from before. *)
Lemma group_cancellation {X: Type} (u v w: group_term X):
  u + w == v + w -> u == v
.
Proof.
  intros.
  (* Becaues we registered group_equivalence (alias '==') as a reflexive,
     symmetric and transitive relation, we can now use it in rewrites. In
     this first step, we substitute u + 0 for u. *)
  rewrite <- GUnitRight.
  (* Now we replace 0 with w + -w). Notice how this rewrite happens *inside*
     the term. This is only allowed because == is a congruence w.r.t. +. *)
  rewrite <- GInverseRight with (u := w).
  (* Next we perform the associativity step. *)
  rewrite GAssoc.
  (* We can now rewrite u + w as v + w, again using congruence. *)
  rewrite H.
  (* We finally perform the initial steps in reverse. *)
  rewrite <- GAssoc.
  rewrite GInverseRight.
  rewrite GUnitRight.
  (* The proof goal is now reduced to a triviality. Note that the "reflexivity"
     tactic now works, becuase == has been declared to be reflexive. *)
  reflexivity.
Qed.

(* Another example: the 0 also behaves as a unit on the left-hand side. The
   pen-and-paper proof here is as follows:

     (0 + u) + -u == 0 + (u + -u)       (associativity)
                  == 0 + 0              (inverse)
                  == (u + -u) + 0       (inverse)
                  == u + (-u + 0)       (associativity)
                  == u + -u             (unit)

   and therefore 0 + u == u by the cancellation property above. *)
Lemma group_unit_left {X: Type} (u: group_term X):
  0 + u == u
.
Proof.
  (* To prove the goal, we need to reason backwards. That means that we apply
     the cancellation property first. By the above, we need to use -u for w. *)
  apply group_cancellation with (w := - u).
  (* Now we can reassociate the brackets. *)
  rewrite <- GAssoc.
  (* We rewrite both occurrences of u + -u in one step. *)
  rewrite GInverseRight.
  (* Merge the two zeroes. *)
  rewrite GUnitRight.
  (* And we're done. *)
  reflexivity.
Qed.

(* The inverse also behaves as an inverse on the left. On paper, the derivation
   goes as follows:

     (-u + u) + -u == -u + (u + -u)     (associativity)
                   == -u + 0            (inverse)
                   == -u                (unit)
                   == 0 + -u            (left unit, see above)

   Homework --- Exercise 1: formalize this proof below. *)
Lemma group_inverse_left {X: Type} (u: group_term X):
  -u + u == 0
.
Proof.
  apply group_cancellation with (w := -u).
  rewrite <- GAssoc.
  rewrite GInverseRight.
  rewrite GUnitRight.
  apply GSymm.
  apply group_unit_left.
Qed.

(* Let's revisit the unique group unit lemma from before. You can find a
   traditional derivation proof above.

   Homework --- Exercise 2: formalize the earlier proof using rewrites. *)
Lemma group_unit_unique {X: Type} (u e: group_term X)
:
  e + u == u ->
  e == 0
.
Proof.
  (* e == e + 0              (unit)
       == e + (u + -u)       (inverse)
       == (e + u) + -u       (associativity)
       == u +- u             (premise)
       == 0                  (inverse) *)
  intro.
  rewrite <- GUnitRight.
  rewrite <- GInverseRight with (u := u).
  rewrite GAssoc.
  rewrite H.
  reflexivity.
Qed.

(* Inverses are unique --- i.e., if something behaves like an inverse of an
   element, then it is *the* inverse of that element.

   Homework --- Exercise 3: Derive a pen-and-paper proof of this property
   first, then formalize it using rewrites. Note that you are allowed to use
   all of the properties that we proved above. *)
Lemma group_inverse_unique {X: Type} (u v: group_term X)
:
  u + v == 0 ->
  v == -u
.
Proof.
  (* v == 0 + v              (left unit)
       == (-u + u) + v       (left inverse)
       == -u + (u + v)       (associativity)
       == -u + 0             (premise)
       == -u                 (unit) *)
  intro.
  rewrite <- group_unit_left with (u := v).
  rewrite <- group_inverse_left with (u := u).
  rewrite <- GAssoc.
  rewrite H.
  apply GUnitRight.
Qed.

(* The inverse of a sum is the sum of inverses.

   Homework --- Exercise 4: Derive a pen-and-paper proof of this property
   first, then formalize it using rewrites.

   Hint: you can use the group_inverse_unique lemma given above. *)
Lemma group_reversal {X: Type} (u v: group_term X):
  -(u + v) == -v + -u
.
Proof.
  (* (-v + -u) + (u + v) == ((-v + -u) + u) + v (associativity)
                         == (-v + (-u + u)) + v (associativity)
                         == (-v + 0) + v        (left inverse)
                         == -v + v              (unit)
                         == 0                   (left inverse) *)
  apply group_cancellation with (w := (u + v)).
  rewrite group_inverse_left.
  rewrite GAssoc.
  rewrite <- GAssoc with (u := -v).
  rewrite group_inverse_left.
  rewrite GUnitRight.
  rewrite group_inverse_left.
  reflexivity.
Qed.

(* Group equivalence is a congruence w.r.t. inverses --- i.e., the inverse of
   two equivalent expressions is again equivalent.

   Homework --- Exercise 5: Derive a pen-and-paper proof of this property
   first, then formalize it using rewrites.

   As before, you may apply any of the lemmas proved above. *)


(* Same proof as group_cancellation but using left instead of right *)
Lemma group_cancellation_left {X: Type} (u v w: group_term X):
  w + u == w + v -> u == v
.
Proof.
  intros.
  rewrite <- group_unit_left.
  rewrite <- group_inverse_left with (u := w).
  rewrite <- GAssoc.
  rewrite H.
  rewrite GAssoc.
  rewrite group_inverse_left.
  rewrite group_unit_left.
  reflexivity.
Qed.

Lemma group_negate_cong {X: Type} (u v: group_term X):
  u == v ->
  -u == -v
.
Proof.
  (* This one seems easier by equational reasoning
  than by chains of equalities:
      v == u                 (premise)
      0 + v == u + 0         (left and right unit)
      (u + -u) + v == u + 0  (inverse)
      u + (-u + v) == u + 0  (associativity)
      -u + v == 0            (left cancellation)
      -u + v == -v + v       (left inverse)
      -u == - v              (cancellation)
       *)
  intro.
  apply group_cancellation with (w := v).
  rewrite group_inverse_left.
  apply group_cancellation_left with (w := u).
  rewrite GAssoc.
  rewrite GInverseRight.
  rewrite GUnitRight.
  rewrite group_unit_left.
  easy.
Qed.

(* Negation is an involution --- i.e., double negation is the identity.

   Homework --- Exercise 7: Derive a pen-and-paper proof of this property
   first, then formalize it using rewrites.

   As before, you may apply any of the lemmas proved above. *)
Lemma unit_inverse {X: Type}:
  GUnit X == -(GUnit X)
.
Proof.
  apply group_cancellation with (w := 0).
  rewrite GUnitRight.
  rewrite GUnitRight.
  apply group_inverse_unique.
  rewrite GUnitRight.
  reflexivity.
Qed.

Lemma group_negate_involutive {X: Type} (u: group_term X):
  u == --u
.
Proof.
  (* --u + -u == -(u + -u)
              == -0
              == 0 *)
  apply group_cancellation with (w := -u).
  rewrite GInverseRight.
  rewrite <- group_reversal.
  rewrite unit_inverse.
  (* Now that we have proven that -u == -v => u == v, how can I tell Coq
  that it's okay to f_equal? Seems like it should be possible. *)
  apply group_negate_cong.
  rewrite GInverseRight.
  reflexivity.
Qed.

(* Here is a little encore. Remember how we defined the group equivalence
   relation above, and then defined the notation afterwards? This has the
   disadvantage of not being able to use the notation when defining the
   relation, which makes it harder to read.

   Fortunately, Coq allows you to use undefined notation, as long as you define
   it strictly afterwards. The first thing you do is reserve a symbol. *)
Reserved Notation "u == v" (at level 70, no associativity).

(* Now we give the relation as before, but using the notation that was just
   reserved. Notice how the laws are a lot more readable this way. *)
Inductive group_equivalence' {X: Type}
  : group_term X -> group_term X -> Prop :=
| GAssoc':
    forall (u v w: group_term X), u + (v + w) == (u + v) + w
| GUnitRight':
    forall (u: group_term X), u + 0 == u
| GInverseRight':
    forall (u: group_term X), u + -u == 0
| GRefl':
    forall (u: group_term X), u == u
| GSymm':
    forall (u v: group_term X),
      u == v ->
      v == u
| GTrans':
    forall (u v w: group_term X),
      u == v ->
      v == w ->
      u == w
| GCong':
    forall (u v u' v': group_term X),
      u == v ->
      u' == v' ->
      u + u' == v + v'
(* Finally, we define the meaning of the == symbol. *)
where "u == v" := (group_equivalence' u v)
.

(* Homework --- Exercise 8 (optional challenge).

   Copy the syntax for group expressions as well as the definition of the
   equivalence relation on groups to a separate file, and extend it to define
   the syntax and equivalence relation for rings instead.

   Can you prove something interesting using these laws? *)
