Inductive list : Type :=
|nil: list
|cons: nat -> list -> list.

Fixpoint length (l : list) : nat :=
match l with
|nil => O
|cons n l' => S (length l')
end.

Fixpoint sum (l : list) : nat :=
match l with
|nil => O
|cons n l' => n + (sum l')
end.

Fixpoint app (l1 l2 : list) : list :=
match l1 with
| nil    => l2
| cons h t => cons h (app t l2)
end.
  
Fixpoint elemgtone (l : list) : Prop :=
match l with
|nil => True
|cons n l' => n >= 2 \/ elemgtone l'
end.

Fixpoint sumgtlen (l : list) : Prop :=
match l with
|nil => True
|cons n l' => sum (cons n l') > length (cons n l') /\ sumgtlen l'
end.

Theorem pigeonhole : forall (l : list),
sumgtlen l -> elemgtone l.
Proof.
induction l. intros. assumption. intros. simpl. right. apply IHl. inversion H. apply H1.
Qed.

Theorem pigeonhole_contrapositive : forall (l : list),
~ (elemgtone l) -> ~ (sumgtlen l).
Proof.
intros. induction l. assumption.
simpl. unfold not. intros. apply IHl.
  unfold not. intros. apply H. simpl. right. assumption.
  inversion H0. assumption.
Qed.