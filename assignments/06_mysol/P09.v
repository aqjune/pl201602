Require Export P08.



(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The _pigeonhole principle_ states a basic fact about counting: if
   we distribute more than [n] items into [n] pigeonholes, some
   pigeonhole must contain at least two items.  As often happens, this
   apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)


Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
intros.
induction l.
- inversion H.
- inversion H.
  + rewrite H0 in *.
    exists [], l.
    reflexivity.
  + apply IHl in H0.
    inversion H0.
    inversion H1.
    exists (a::x0).
    exists x1.
    simpl.
    rewrite H2.
    reflexivity.
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
| rp_base: forall x l, In x l -> repeats (x::l)
| rp_next: forall x l, repeats l -> repeats (x::l)
.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
   { simpl. intros. inversion H1. }
   {
     intros l2.
     intros H_excluded.
     unfold excluded_middle in *.
     intros H1 H2.
     assert (H' := H_excluded (In x l1')).
     destruct H'.
     - apply rp_base. assumption.
     - 
   }
Qed.

