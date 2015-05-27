Require Import  Arith List.
Require Import CpdtTactics.

Inductive plist {A: Set} (P : A -> Prop) : nat -> Set :=
| Nil : plist P 0
| T : forall n a, P a -> plist P n -> plist P (S n)
| F : forall n, A -> plist P n -> plist P n.

Arguments  T {A} {P} {n} _ _ _.
Arguments F {A} {P} {n} _ _.

Fixpoint concat {A : Set} {P} {n1} {n2}
         (l1 : plist P n1)
         (l2 : plist P n2)
  : plist P (n1 + n2) :=
  match l1 in plist _ n1 return @plist A _ (n1 + n2) with
  | Nil => l2
  | T _ a p t => T a p (concat t l2)
  | F _ a t => F a (concat t l2)
  end.

Fixpoint out {A : Set} {P} {n} (l : plist P n) : list A :=
  match l with
  | Nil => nil
  | T _ a _ t => a :: out t
  | F _ a t => a :: out t
  end.

Fixpoint matches {A : Set} {P : A -> Prop} (dec : forall a : A, {P a} + {~ P a}) (l : list A) :=
  match l with
  | nil => O
  | x :: t => if dec x then S (matches dec t) else matches dec t
  end.

Fixpoint to_plist {A : Set} {P : A -> Prop}
         (dec : forall a : A, {P a} + {~ P a})
         (l : list A)
  : plist P (matches dec l) :=
  match l return plist P (matches dec l) with
  | nil => Nil P
  | x :: t =>  match dec x as d return plist P (if d then
                                                  S (matches dec t)
                                                else
                                                  matches dec t)
               with
               | left p => T x p (to_plist dec t)
               | right _ => F x (to_plist dec t)
               end
  end.

Theorem in_out_invariant : forall (A : Set)
                                  (P : A -> Prop)
                                  (dec : forall a : A, {P a} + {~ P a})
                                  (l : list A),
    out (to_plist dec l) = l.
Proof.
  intros.
  induction l; simpl.
  reflexivity.
  destruct (dec a); crush.
Qed.

Fixpoint grab {A : Set} {P : A -> Prop} {n : nat} (l : plist P (S n)) : sig P :=
  match l in plist _ k return match k with
                              | O => unit
                              | S _ => sig P
                              end
  with
  | Nil => tt
  | T _ x p _ => exist P x p
  | F (S k) _ t => grab t
  | F O _ t => tt
  end.
