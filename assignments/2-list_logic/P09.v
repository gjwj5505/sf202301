Require Export P08.

Lemma trim_head_last A (xs : list A) : 2 <=? length xs = true -> exists x ys y, xs = [x] ++ ys ++ [y].
Proof.
  assert (rev_involutive_anytype : forall {X: Type} (l : list X),
  rev ((rev l)) = l).
  {
    assert (concat_nil : forall {X: Type} (l : list X), l ++ nil = l).
    {
      intros X l. induction l as [| x l' IHl'].
      - simpl. reflexivity.
      - simpl. rewrite IHl'. reflexivity.
    }
    assert (concat_assoc : forall {X: Type} (l1 l2 l3 : list X), (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)).
    {
      intros X l1. induction l1 as [| x l1' IHl1']; intros l2 l3.
      - simpl. reflexivity.
      - simpl. rewrite IHl1'. reflexivity.
    }
    assert (rev_concat : forall {X: Type} (l1 l2 : list X), rev (l1 ++ l2) = (rev l2) ++ (rev l1)).
    {
      intros X l1. induction l1 as [| x l1' IHl1']; intros l2. 
      - simpl. rewrite concat_nil. reflexivity. 
      - simpl. rewrite IHl1'. rewrite concat_assoc. reflexivity.
    }
    intros X l.
    induction l as [| x l' IHl'].
    - reflexivity.
    - simpl. rewrite rev_concat. simpl. rewrite IHl'. reflexivity. 
  }


  assert (concat_not_nil : forall {B : Type} (l : list B) (x : B), l ++ [x] = [] -> False).
  {
    intros.
    induction l as [| h l' IHl'].
    - simpl in H. inversion H.
    - simpl in H. inversion H.
  }
  intros H.
  destruct xs as [| x xs'] eqn:Dxs'.
  - inversion H.
  - destruct (rev xs) as [| rx rxs'] eqn:Drxs'.
    + subst. simpl in Drxs'.
      destruct (rev xs').
      -- simpl in Drxs'. inversion Drxs'.
      -- simpl in Drxs'. inversion Drxs'. 
    + destruct (rev xs') eqn:Drxs''.
      -- subst. 
        destruct xs' eqn:Dxs''.
        ++ inversion H.
        ++ simpl in Drxs''. apply concat_not_nil with (B := A) (l := rev l) (x := x0) in Drxs''. inversion Drxs''.
      --  exists x. 
          exists (rev l).
          exists x0.
          simpl. f_equal. rewrite <- rev_involutive_anytype with (X:= A) (l := xs').
          rewrite Drxs''. simpl. reflexivity.
Qed.
