Require Import Arith List Bool.
Require Import CpdtTactics DepList FunctionalExtensionality Eqdep.

Inductive type : Set :=
| Bool : type
| Lambda : type -> type -> type.

Inductive Exp (ts : list type) : type -> Type :=
| Var : forall T, member T ts -> Exp ts T
| Abs : forall T1 T2, Exp (T1 :: ts) T2 -> Exp ts (Lambda T1 T2)
| App : forall T1 T2, Exp ts (Lambda T1 T2) -> Exp ts T1 -> Exp ts T2
| Const : bool -> Exp ts Bool.

Fixpoint denote (t : type) : Set :=
  match t with
  | Bool => bool
  | Lambda a b => denote a -> denote b
  end.

Fixpoint eval {ts T} (e : Exp ts T) (G : hlist denote ts) : denote T :=
  match e with
  | Var _ x => hget G x
  | Abs _ _ e' => fun x => eval e' (x ::: G)
  | App _ _ f x => (eval f G) (eval x G)
  | Const b => b
  end.

Theorem lift {A} {x : A} a abs t : member x (abs ++ t) -> member x (abs ++ a :: t).
Proof.
  refine
    ((fix REC abs :=
        match abs return member x (abs ++ t) -> member x (abs ++ a :: t)
        with
        | nil => fun m => @HNext _ x a t m
        | cons b abs' =>
          fun m =>
            match m in member _ ls
                  return match ls with
                         | nil => unit
                         | cons b ls' => ls' = abs' ++ t -> member x (b :: abs' ++ a :: t)
                         end
            with
            | HFirst _ => fun _ => @HFirst _ x (abs' ++ a :: t)
            | HNext _ _ m' => fun pr =>
                                @HNext _ x _ (abs' ++ a :: t) (REC abs' _)
            end _
        end) abs).
  rewrite pr in m'; assumption.
  auto.
Defined.

Theorem lower {A x} (a : A) abs t : member x (abs ++ a :: t) -> member x (abs ++ t) + {a = x}.
Proof.
  refine (
      (fix REC abs :=
         match abs return member x (abs ++ a :: t) -> member x (abs ++ t) + {a = x}
         with
         | nil => fun m =>
                    match m with
                    | HFirst _ => inright _
                    | HNext _ _ m' => inleft m'
                    end
         | cons b abs' =>
           fun m =>
             match m in member _ ls
                   return match ls with
                          | nil => unit
                          | cons b ls' => ls' = abs' ++ a :: t ->
                                          member x (b :: abs' ++ t) + {a = x}
                          end
             with
             | HFirst _ => fun _ => inleft (@HFirst _ x (abs' ++ t))
             | HNext _ _ m' => fun pr => match REC abs' _ with
                                         | inleft m'' => inleft (@HNext _ x _ (abs' ++ t) m'')
                                         | inright proof => inright proof
                                         end
             end _
         end
      ) abs).
  reflexivity.
  rewrite pr in m'; auto.
  auto.
Defined.

Fixpoint lift' {A} {x : A} p abs t : member x (abs ++ t) -> member x (abs ++ p ++ t) :=
  match p with
  | nil => fun m => m
  | cons a p' => fun m => lift a abs (p' ++ t) (lift' p' abs t m)
  end.

Fixpoint liftExp {x} p abs t (e : Exp (abs ++ t) x) : Exp (abs ++ p ++ t) x :=
  match e with
  | Var _ m => Var _ _ (lift' p abs t m)
  | Abs b _ e' => Abs _ b _ (liftExp p (b :: abs) t e')
  | App _ _ f x => App _ _ _ (liftExp p abs t f) (liftExp p abs t x)
  | Const b => Const _ b
  end.

Fixpoint substitute {T} a abs t
         (e : Exp (abs ++ a :: t) T)
         (e' : Exp t a)
  : Exp (abs ++ t) T :=
  match e with
  | Var _ m => match lower a abs t m with
               | inleft m' => Var _ _ m'
               | inright proof => match proof with
                                  | eq_refl => liftExp abs nil t e'
                                  end
               end
  | Abs b _ e'' =>  Abs _ b _ (substitute a (b :: abs) t e'' e')
  | App _ _ f x => App _ _ _ (substitute a abs t f e') (substitute a abs t x e')
  | Const b => Const _ b
  end.

Definition subs {T a t} : Exp (a :: t) T -> Exp t a -> Exp t T :=
  substitute a nil t.

Lemma first_lifts_to_first :
  forall A a (p abs t : list A),
    lift' p (a :: abs) t HFirst = HFirst.
Proof.
  intros.
  induction p.
  reflexivity.
  simpl.
  rewrite IHp.
  reflexivity.
Qed.

Lemma next_lifts_to_next :
  forall A a b (p abs t : list A)
         (m : member b (abs ++ t)),
    lift' p (a :: abs) t (HNext m) = HNext (lift' p abs t m).
Proof.
  intros.
  induction p.
  reflexivity.
  simpl.
  rewrite IHp.
  reflexivity.
Qed.

Lemma lift_cons :
  forall p abs t
         (G : hlist denote (abs ++ t))
         (G' : hlist denote (abs ++ p ++ t)),
    (forall a (m : member a (abs ++ t)) (m' : member a (abs ++ p ++ t)),
        lift' p abs t m = m' -> hget G m = hget G' m')
    -> (forall a b x
               (m : member a (b :: abs ++ t))
               (m' : member a (b :: abs ++ p ++ t)),
           lift' p (b :: abs) t m = m' -> hget (x ::: G) m = hget (x ::: G') m').
Proof.
  intros; dep_destruct m; dep_destruct m';
  try reflexivity;
  try (rewrite first_lifts_to_first in H0; inversion H0);
  try (rewrite next_lifts_to_next in H0; inversion H0);
  crush.
Qed.

Lemma liftExp_ok :
  forall x ts (e : Exp ts x)
         abs t
         (Hts: abs ++ t = ts)
         p
         (G : hlist denote (abs ++ t))
         (G' : hlist denote (abs ++ p ++ t)),
    (forall a (m : member a (abs ++ t)) (m' : member a (abs ++ p ++ t)),
        lift' p abs t m = m' -> hget G m = hget G' m')
    ->  match Hts in (_ = ts) return Exp ts x -> Prop
        with
        | eq_refl => fun e => eval (liftExp p abs t e) G' = eval e G
        end e.
Proof.
  induction e; intros; destruct Hts; simpl.
  symmetry; crush.
  apply functional_extensionality; intros.
  apply (IHe (T1 :: abs) t (eq_refl (T1 :: abs ++ t))); intros.
  apply lift_cons; crush.
  replace (eval (liftExp p abs t e1) G') with (eval e1 G).
  replace (eval (liftExp p abs t e2) G') with (eval e2 G).
  reflexivity.
  symmetry.
  apply (IHe2 _ _ (eq_refl (abs ++ t))); crush.
  symmetry.
  apply (IHe1 _ _ (eq_refl (abs ++ t))); crush.
  reflexivity.
Qed.

Lemma lower_cons :
  forall abs a t
         (G : hlist denote (abs ++ a :: t))
         (G' : hlist denote (abs ++ t)),
    (forall b (m : member b (abs ++ a :: t)) (m' : member b (abs ++ t)),
        lower a abs t m = inleft m' -> hget G m = hget G' m')
    -> (forall x b T (m : member b (x :: abs ++ a :: t)) (m' : member b (x :: abs ++ t)),
           lower a (x :: abs) t m = inleft m' -> hget (T ::: G) m = hget (T ::: G') m').
Proof.
  intros.
  destruct abs; dep_destruct m; dep_destruct m'; try reflexivity.
  inversion H0.
  dep_destruct x2; inversion H0.
  apply H; dep_destruct x2; inversion H0; crush.
  inversion H0.
  dep_destruct x2; inversion H0.
  simpl in H0. destruct (lower a abs t); inversion H0.
  apply H.
  simpl in H0.
  dep_destruct x2. inversion H0; crush.
  simpl.
  replace (eq_rect (abs ++ a :: t) (fun ls : list type => member b ls) x4
                   (abs ++ a :: t) eq_refl) with x4 in H0.
  destruct (lower a abs t x4); inversion H0; crush.
  crush.
Qed.

Lemma substitute_ok :
  forall T ts
         (e : Exp ts T)
         a abs t
         (Hts : abs ++ a :: t = ts)
         (e' : Exp t a)
         (G : hlist denote (abs ++ a :: t))
         (G' : hlist denote (abs ++ t))
         (G'' : hlist denote t),
    (forall x (m : member x (abs ++ a :: t)) (m' : member x (abs ++ t)),
        lower a abs t m = inleft m' -> hget G m = hget G' m') ->
    (forall x (m : member x (abs ++ a :: t)) H,
        lower a abs t m = inright H -> match H in (_ = x)
                                       with
                                       | eq_refl => fun v => v = eval e' G''
                                       end (hget G m)) ->
    (forall x (m : member x t), hget G'' m = hget G' (lift' abs nil t m)) ->
    match Hts in (_ = ts) return Exp ts T -> Prop with
    | eq_refl => fun e => eval (substitute a abs t e e') G' = (eval e G)
    end e.
Proof.
  induction e; intros; destruct Hts; simpl.
  symmetry.
  destruct (lower a abs t m) eqn:Hl; crush.
  rewrite (H0 T m (eq_refl T)).
  symmetry.
  eapply (liftExp_ok _ _ _ _ _ (eq_refl (nil ++ t))); crush.
  crush.
  simpl.
  apply functional_extensionality; intros.
  eapply (IHe _ (T1 :: abs) t (eq_refl (T1 :: abs ++ a :: t))).
  intros.
  apply lower_cons; intros; crush.
  intros. destruct H2.
  dep_destruct m.
  inversion H3.
  simpl.
  apply (H0 _ _ (eq_refl a)).
  simpl in H3.
  destruct (lower a abs t x2); inversion H3.
  crush.
  crush.
  replace (eval (substitute a abs t e1 e') G') with (eval e1 G).
  replace (eval (substitute a abs t e2 e') G') with (eval e2 G).
  reflexivity.
  symmetry.
  apply (IHe2 _ _ _ (eq_refl (abs ++ a :: t)) _ G G' G''); crush.
  symmetry.
  apply (IHe1 _ _ _ (eq_refl (abs ++ a :: t)) _ G G' G''); crush.
  reflexivity.
Qed.

Theorem substitution_preserves_meaning :
  forall a t T (e : Exp (a :: t) T) (e' : Exp t a) (G : hlist denote t),
    eval (subs e e') G = eval e (eval e' G ::: G).
Proof.
  intros.
  unfold subs.
  eapply (substitute_ok _ _ _ _ nil t (eq_refl (a :: t))); intros.
  dep_destruct m; crush.
  destruct H.
  dep_destruct m; crush.
  crush.
Qed.
