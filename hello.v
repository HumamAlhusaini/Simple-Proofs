

Fixpoint equality (n m: nat) : bool :=
  match n with
  | 0 => match m with 
         | 0 => true
         | S m' => false
         end
  | S n' => match m with 
            | 0 => false
            | S m' => equality n' m'
            end
  end.

Fixpoint lessOrEqual (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => lessOrEqual n' m'
      end
  end.

Definition negb (n: bool) : bool :=
  match n with 
  | true => false
  | false => true
end.

Notation "x =? y" := (equality x y) (at level 70) : nat_scope.

Notation "x <=? y" := (lessOrEqual x y) (at level 70) : nat_scope.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Fixpoint is_even (n: nat) : bool := 
  match n with 
    | 0 => true
    | S n' => is_even n'
  end.

Definition is_odd (n:nat) : bool :=
negb (is_even n).

Definition andb (a b: bool) : bool :=
  match a with
  | true => b
  | false => false
  end.

Theorem andb_true_elim2 : forall b c : bool,
  andb  b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  intros H.
  rewrite <- H.
  simpl.
  reflexivity.
  intros H.
  destruct c.
  simpl.
  reflexivity.
  rewrite <- H.
  simpl.
  reflexivity.
Qed.
