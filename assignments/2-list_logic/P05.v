Require Export P04.


Lemma firstn_exact : forall A n (xs ys : list A), n = length xs -> firstn n (xs ++ ys) = xs.
Proof.
  intros A n.
  induction n as [| n' IHn']; intros.
  - simpl. destruct xs.
    + reflexivity.
    + simpl in H. inversion H.
  - destruct xs as [| x xs'] eqn:Dxs.
    + simpl in H. inversion H.
    + simpl. simpl in H. inversion H. apply IHn' with xs' ys in H1.
      inversion H. rewrite <- H2. rewrite H1. reflexivity.
Qed.
