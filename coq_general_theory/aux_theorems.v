Require Import List.

Theorem In_map_theorem {X Y : Type} : forall (l : list X) (f g : X -> Y),
  (forall x : X, In x l -> f x = g x) -> map f l = map g l.
Proof.
  induction l.
  - intros. reflexivity.
  - intros. simpl. assert (H1 : In a (a::l)).
    simpl. left. reflexivity. apply H in H1. rewrite H1.
    assert (H2 : map f l = map g l). apply IHl. intros.
    apply H. right. apply H0. rewrite H2. reflexivity.
Qed.