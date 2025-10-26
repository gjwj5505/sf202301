Require Export P02.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n. induction n as [| n']; intros X l.
  - destruct l as [| x l']. 
    + simpl. reflexivity.
    + intros H. simpl in H. inversion H.
  - destruct l as [| x l'].
    + simpl. reflexivity.
    + intros H. simpl in H. inversion H. apply IHn' in H1.
    simpl. inversion H. rewrite H2. apply H1.
Qed.
