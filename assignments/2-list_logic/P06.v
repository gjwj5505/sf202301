Require Export P05.


Theorem rev_removelast_rev_tl : forall l : natlist,
  rev (removelast (rev l)) = tl l.
Proof.
  assert (removelast_concat_on : forall l : natlist, forall x : nat, removelast (l ++ [x]) = l).
  {
    intros l x.
    induction l as [| h l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite IHl'. simpl. 
      destruct l' as [| l''] eqn:Dl'.
      + simpl. reflexivity.
      + simpl. reflexivity. 
  }
  intros l.
  destruct l as [| x l'] eqn:Dl.
  - simpl. reflexivity.
  - simpl. rewrite removelast_concat_on. rewrite rev_involutive. reflexivity.
Qed.
