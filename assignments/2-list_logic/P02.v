Require Export P01.


Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  assert (concat_nil : forall l : natlist, l ++ [] = l).
  {
    intros l.
    induction l as [| x l' IHl'].
    - reflexivity.
    - simpl. rewrite IHl'. reflexivity.
  }
  assert (concat_assoc : forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)).
  {
    intros l1. induction l1 as [| x l1' IHl1']; intros l2 l3.
    - simpl. reflexivity.
    - simpl. rewrite IHl1'. reflexivity.
  }
  intros l1.
  induction l1 as [| x l1' IHl1'];intros l2.
  - simpl. rewrite concat_nil. reflexivity.
  - simpl. rewrite IHl1'. rewrite concat_assoc. reflexivity.
Qed.
