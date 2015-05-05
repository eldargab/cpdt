Require Import Arith List Bool.

Module P1.
  Ltac deSome :=
    repeat match goal with
           | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
           end;
    reflexivity.

  Theorem test : forall (a b c d e f g : nat),
      Some a = Some b
      -> Some b = Some c
      -> Some e = Some c
      -> Some f = Some g
      -> c = a.
  Proof.
    intros. deSome.
  Qed.

  Theorem test2 : forall (a x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : nat),
      Some x1 = Some y1
      -> Some x2 = Some y2
      -> Some x3 = Some y3
      -> Some x4 = Some y4
      -> Some x5 = Some y5
      -> Some x6 = Some y6
      -> Some a = Some a
      -> x1 = x2.
  Proof.
    intros.
    Time try deSome.
  Abort.
End P1.

Module P2.
  Ltac genlist n ls k :=
    match n with
    | O => k ls
    | S ?n' => solve[ k (true :: ls) |
                      k (false :: ls) |
                      genlist n' (true :: ls) k |
                      genlist n' (false :: ls) k
                    ]
    end.
  
  Ltac disprover H n :=
    match type of H with
    | forall _, _ => genlist n (@nil bool) ltac:(fun l =>
                                                   idtac l; specialize (H l); disprover H n)
    | _ = _ => discriminate
    end.

  Ltac disprove n :=
    match goal with
    | [|- ?G] => assert (G -> False) by (intros H; specialize (H bool); disprover H n)
    end.
  
  Theorem test1 : forall A (ls1 ls2 : list A), ls1 ++ ls2 = ls2 ++ ls1.
  Proof.
    disprove 1.
  Abort.
  
  Theorem test2 : forall A (ls1 ls2 : list A),
      length (ls1 ++ ls2) = length ls1 - length ls2.
  Proof.
    disprove 1.
  Abort.
  
  Theorem test3 : forall A (ls : list A),
      length (rev ls) - 3 = 0.                                 
  Proof.
    disprove 4.
  Abort.
End P2.
