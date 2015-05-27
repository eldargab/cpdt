Require Import Arith List.
Require Import CpdtTactics.
Require Import MoreSpecif.

Local Open Scope specif.

Module P1.
  Definition compare : forall n m : nat, {n <= m} + {n > m}.
  Proof.
    refine (fix cmp (n m : nat) : {n <= m} + {n > m} :=
              match n with
              | O => Yes
              | S n' => match m with
                        | O => No
                        | S m' => Reduce (cmp n' m')
                        end
              end); omega.
  Defined.
End P1.

Module P2.
  Definition var := nat.

  Inductive prop : Set :=
  | Var : var -> prop
  | Not : prop -> prop
  | Conj : prop -> prop -> prop
  | Disj : prop -> prop -> prop.

  Fixpoint denote (U : var -> bool) (e : prop) : Prop :=
    match e with
    | Var x => if U x then True else False
    | Not p => ~ denote U p
    | Conj p1 p2 => denote U p1 /\ denote U p2
    | Disj p1 p2 => denote U p1 \/ denote U p2
    end.

  Definition bool_true_dec : forall b, {b = true} + {b = true -> False}.
  Proof.
    refine (fun b => match b with
                     | true => Yes
                     | false => No
                     end); crush.
  Defined.

  Definition decide : forall (U : var -> bool) (p : prop), {denote U p} + {~ denote U p}.
  Proof.
    induction p; crush.
    destruct (U v); crush.
  Defined.

  Definition negate : forall p, {p' | forall U, denote U p <-> ~ denote U p'}.
  Proof.
    refine (fix neg p : {p' | forall U, denote U p <-> ~ denote U p'} :=
              match p with
              | Var x => [Not (Var x)]
              | Not p' => [p']
              | Conj p1 p2 => (p1' <== neg p1;
                               p2' <== neg p2;
                               [Disj p1' p2'])
              | Disj p1 p2 => (p1' <== neg p1;
                               p2' <== neg p2;
                               [Conj p1' p2'])
              end); intros; simpl.
    destruct (U x); crush.
    crush.
    rewrite _H. rewrite _H0.
    intuition.
    rewrite _H. rewrite _H0.
    intuition.
    destruct (decide U p1'); intuition.
  Defined.
End P2.
