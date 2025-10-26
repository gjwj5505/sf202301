Require Export P06.


Example mult_exercise :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n.
  - left. reflexivity.
  - simpl in H. destruct m.
    + right. reflexivity.
    + simpl in H. inversion H.
Qed.
