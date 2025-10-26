Require Export P07.


Lemma fold_left_last : forall (A B : Type) (f : B -> A -> B) (z0 : B) (xs : list A) (x0 : A),
  fold_left f (xs ++ [x0]) z0 = f (fold_left f xs z0) x0.
Proof.
  intros A B f z0 xs x0.
  revert z0.
  induction xs as [| x xs' IHxs']; intros z0.
  - simpl. reflexivity.
  - simpl. rewrite IHxs' with (z0 := (f z0 x)). reflexivity.
Qed.
