Require Import Coq.Lists.List.

Fixpoint zip {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | h1 :: t1, h2 :: t2 => (h1,h2) :: (zip t1 t2)
  | _, _ => nil
  end.

Theorem zipnilr {X Y : Type} : forall (l : list X), zip l (@ nil Y) = nil.
Proof.
  intros. destruct l;simpl;unfold zip; reflexivity.
Qed.

Theorem zipLength {X Y : Type} : forall (l1 : list X) (l2 : list Y) (l3 : list (X * Y)),
  l3 = zip l1 l2 -> length l1 = length l2 -> length l1 = length l3.
Proof.
  induction l1;intros.
  - rewrite H. reflexivity.
  - destruct l2. discriminate H0. destruct l3. discriminate H.
    inversion H. simpl. rewrite <- H3. apply IHl1 in H3.
    rewrite H3. reflexivity. inversion H0. reflexivity.
Qed.
