Section Group.
  Variable G : Type.
  Variable e : G.
  Variable f : G -> G -> G.
  Variable i : G -> G.

  Infix "*" := f.

  Hypothesis Assoc : forall a b c, a * b * c = a * (b * c).
  Hypothesis RightIdent : forall a, a * e = a.
  Hypothesis RightInv : forall a, a * i a = e.
  
  Lemma assoc_rewrite : forall a b,
      a * b * i b = a * (b * i b).
  Proof.
    auto.
  Qed.
  
  Hint Rewrite RightInv RightIdent assoc_rewrite.

  Hint Rewrite RightIdent : aux. (* Just a declaration, CreateDb didn't work for rewrite dbs *)

  Hint Extern 50 => repeat rewrite <- Assoc in *; autorewrite with core aux in *.
  
  Lemma mult_both_right : forall x a b,
      a = b -> a * x = b * x.
  Proof.
    intros. rewrite H. reflexivity.
  Qed.

  Lemma mult_both_left: forall x a b,
      a = b -> x * a = x * b.
  Proof.
    intros. rewrite H. reflexivity.
  Qed.

  Hint Extern 200 => match goal with
                     | [H : _ * ?a = _ |- _] => apply (mult_both_right (i a)) in H
                     end.

  Hint Extern 250 => match goal with
                     | [H : ?a * _ = _ |- _] => apply (mult_both_left (i a)) in H
                     end.

  Theorem RightCancellation : forall x a b, a * x = b * x -> a = b.
  Proof.
    auto.
  Qed.

  Hint Extern 150 (_ * ?a = _) => apply (RightCancellation (i a)).
  
  Theorem LeftIdentity : forall a,
      e * a = a.
  Proof.
    auto.
  Qed.

  Hint Rewrite LeftIdentity : aux.

  Theorem LeftInverse : forall a,
      i a * a = e.
  Proof.
    auto.
  Qed.

  Hint Rewrite LeftInverse.

  Theorem LeftCancellation : forall x a b, x * a = x * b -> a = b.
  Proof.
    auto.
  Qed.

  Hint Extern 100 ( _ = i ?a ) => apply (LeftCancellation a).
  Hint Extern 100 ( i ?a = _ ) => apply (LeftCancellation a).

  Theorem LeftIdentityUnique : forall a p,
      p * a = a -> p = e.
  Proof.
    auto.
  Qed.
  
  Theorem CharacterizingIdentity : forall a,
      a * a = a -> a = e.
  Proof.
    auto.
  Qed.
  
  Theorem RightInverseUnique : forall a b,
      a * b = e -> b = i a.
  Proof.
    auto.
  Qed.
  
  Theorem LeftInverseUnique : forall a b,
      a * b = e -> a = i b.
  Proof.
    auto.
  Qed.

  Theorem InverseDistributivity : forall a b,
      i (a * b) = i b * i a.
  Proof.
    auto.
  Qed.
  
  Theorem DoubleInverse : forall a,
      i (i a) = a.
  Proof.
    auto.
  Qed.
  
  Theorem IdentityInverse :
    i e = e.
  Proof.
    auto.
  Qed.
End Group.
