Require Import Bool Arith List CpdtTactics.

Module P3.
  Inductive binop : Set := Plus | Times.

  Inductive var : Set :=
  | vi: nat -> var.

  Inductive exp : Set :=
  | Const : nat -> exp
  | Binop : binop -> exp -> exp -> exp
  | Var : var -> exp.

  Definition binopDenote (b : binop) : nat -> nat -> nat :=
    match b with
    | Plus => plus
    | Times => mult
    end.

  Fixpoint expDenote (G : var -> nat) (e : exp) : nat :=
    match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote G e1) (expDenote G e2)
    | Var x => G x
    end.

  Fixpoint fold (e : exp) : exp :=
    match e with
    | Const n => Const n
    | Binop b e1 e2 => let e1' := fold e1 in
                       let e2' := fold e2 in
                       match e1' with
                       | Const n1 => match e2' with
                                     | Const n2 => Const ((binopDenote b) n1 n2)
                                     | _ => Binop b e1' e2'
                                     end
                       | _ => Binop b e1' e2'
                       end
    | Var x => Var x
    end.

  (* Eval simpl in fold (Binop Plus (Var (vi 1)) (Binop Times (Const 1) (Const 2))). *)

  Theorem fold_is_correct :
    forall G e,
      expDenote G (fold e) = expDenote G e.
  Proof.
    induction e; crush.
    destruct (fold e1); destruct (fold e2); crush.
  Qed.
End P3.

Module P4.
  Inductive var : Set :=
  | vi: nat -> var.

  Inductive nat_exp : Set :=
  | nconst : nat -> nat_exp
  | nplus : nat_exp -> nat_exp -> nat_exp
  | ntimes : nat_exp -> nat_exp -> nat_exp
  | nvar : var -> nat_exp
  | nif : bool_exp -> nat_exp -> nat_exp -> nat_exp

  with bool_exp : Set :=
       | bconst : bool -> bool_exp
       | beq : nat_exp -> nat_exp -> bool_exp
       | blt : nat_exp -> nat_exp -> bool_exp.

  Fixpoint eval (G : var -> nat) (e : nat_exp) : nat :=
    match e with
    | nconst n => n
    | nplus e1 e2 => (eval G e1) + (eval G e2)
    | ntimes e1 e2 => (eval G e1) * (eval G e2)
    | nvar v => G v
    | nif t e1 e2 => if eval_bool G t then eval G e1 else eval G e2
    end
  with eval_bool (G : var -> nat) (e : bool_exp) : bool :=
         match e with
         | bconst b => b
         | beq e1 e2 => beq_nat (eval G e1) (eval G e2)
         | blt e1 e2 => leb (eval G e1) (eval G e2)
         end.

  Fixpoint opt
           {T Texp: Set}
           (e1 e2 : nat_exp)
           (constant : T -> Texp)
           (c: nat_exp -> nat_exp -> Texp)
           (op : nat -> nat -> T)
    : Texp :=
    match e1 with
    | nconst n1 => match e2 with
                   | nconst n2 => constant (op n1 n2)
                   | _ => c e1 e2
                   end
    | _ => c e1 e2
    end.

  Fixpoint fold (e : nat_exp) : nat_exp :=
    match e with
    | nconst n => nconst n
    | nplus e1 e2 => opt (fold e1) (fold e2) nconst nplus plus
    | ntimes e1 e2 => opt (fold e1) (fold e2) nconst ntimes mult
    | nvar v => nvar v
    | nif t e1 e2 => match fold_bool t with
                     | bconst b => if b then fold e1 else fold e2
                     | _ => nif (fold_bool t) (fold e1) (fold e2)
                     end
    end

  with fold_bool (e : bool_exp) : bool_exp :=
         match e with
         | bconst b => bconst b
         | beq e1 e2 => opt (fold e1) (fold e2) bconst beq beq_nat
         | blt e1 e2 => opt (fold e1) (fold e2) bconst blt leb
         end.

  Scheme nat_exp_mut := Induction for nat_exp Sort Prop
                        with bool_exp_mut := Induction for bool_exp Sort Prop.


  Theorem folding_correct: forall G e,
      eval G (fold e) = eval G e.
  Proof.
    intros G.
    apply (nat_exp_mut
             (fun e => eval G (fold e) = eval G e)
             (fun e => eval_bool G (fold_bool e) = eval_bool G e)); crush.
    destruct (fold n); destruct (fold n0); crush.
    destruct (fold n); destruct (fold n0); crush.
    destruct (fold_bool b); crush; destruct (eval_bool G b); crush.
    destruct (fold n); destruct (fold n0); crush.
    destruct (fold n); destruct (fold n0); crush.
  Qed.
End P4.

Module P5.
  Inductive even : Set :=
  | Z : even
  | So : odd -> even
  with odd : Set :=
       | Se : even -> odd.

  Fixpoint sum (n1 n2: even) : even :=
    match n1 with
    | Z => n2
    | So o => So (sum_odd_even o n2)
    end
  with sum_odd_even o e : odd :=
         match o with
         | Se n => Se (sum n e)
         end.

  Fixpoint even_induction
           (P : even -> Prop)
           (pz : P Z)
           (ps : forall n : even, P n -> P (So (Se n)))
           (n : even)
    : P n :=
    match n with
    | Z => pz
    | So o => match o with
              | Se n => ps n (even_induction P pz ps n)
              end
    end.

  Lemma zero_commutative : forall n, n = sum n Z.
  Proof.
    apply (even_induction (fun n => n = sum n Z)); crush.
  Qed.

  Lemma sum_S : forall n1 n2, sum n1 (So (Se n2)) = So (Se (sum n1 n2)).
  Proof.
    intros.
    apply (even_induction (fun n1 => sum n1 (So (Se n2)) = So (Se (sum n1 n2)))); crush.
  Qed.

  Theorem sum_is_commutative: forall n1 n2,
      sum n1 n2 = sum n2 n1.
  Proof.
    intros.
    apply (even_induction (fun n1 =>sum n1 n2 = sum n2 n1)).
    simpl; apply zero_commutative.
    intros.
    simpl; rewrite sum_S; crush.
  Qed.
End P5.

Module P6.
  Inductive tree : Set :=
  | Leaf : nat -> tree
  | Node : (nat -> tree) -> tree.

  Fixpoint increment (t : tree) : tree :=
    match t with
    | Leaf n => Leaf (n + 1)
    | Node f => Node (fun i => increment (f i))
    end.

  Fixpoint leapfrog (i : nat) (t : tree) : nat :=
    match t with
    | Leaf n => n
    | Node f => leapfrog (i + 1) (f i)
    end.

  Theorem incremented: forall t i,
      leapfrog i (increment t) = leapfrog i t + 1.
  Proof.
    induction t; crush.
  Qed.
End P6.

Module P7.
  Inductive btree (T : Set) : Set :=
  | Leaf : T -> btree T
  | Node : btree T -> btree T -> btree T.

  Arguments Leaf {T} _.
  Arguments Node {T} _ _.

  Inductive tree : Set :=
  | L : nat -> tree
  | N : btree tree -> tree.

  Fixpoint total (t : tree) : nat :=
    match t with
    | L n => n
    | N bt =>(fix btotal (bt : btree tree) : nat :=
                match bt with
                | Leaf t => total t
                | Node l r => btotal l + btotal r
                end
             ) bt
    end.

  Fixpoint increment (t : tree) : tree :=
    match t with
    | L n => L (n + 1)
    | N bt => N ((fix inc (bt : btree tree) : btree tree :=
                    match bt with
                    | Leaf t => Leaf (increment t)
                    | Node l r => Node (inc l) (inc r)
                    end)
                   bt)
    end.

  Fixpoint tree_induction
           (P : tree -> Prop)
           (p1 : forall n, P (L n))
           (p2 : forall t, P t -> P (N (Leaf t)))
           (p3 : forall l r, P (N l) -> P (N r) -> P (N (Node l r)))
           (t : tree)
    : P t :=
    match t with
    | L n => p1 n
    | N bt => (fix bt_ind (bt : btree tree) : P (N bt) :=
                 match bt with
                 | Leaf t => p2 t (tree_induction P p1 p2 p3 t)
                 | Node l r => p3 l r (bt_ind l) (bt_ind r)
                 end) bt
    end.

  Theorem increment_increments : forall t,
      total (increment t) > total t.
  Proof.
    apply (tree_induction (fun t => total (increment t) > total t)); crush.
  Qed.
End P7.

Module P8.
  Inductive tree : Set :=
  | Leaf : nat -> tree
  | Node : nat -> tree -> tree -> tree.

  Definition getnum (t : tree) : nat :=
    match t with
    | Leaf n => n
    | Node n _ _ => n
    end.

  Theorem injectivity:
    forall n1 n2,
      Leaf n1 = Leaf n2 -> n1 = n2.
  Proof.
    intros n1 n2 Eq.
    change (getnum (Leaf n1) = getnum (Leaf n2)).
    rewrite Eq.
    reflexivity.
  Qed.

  Theorem discrimination:
    forall k n l r, Leaf k = Node n l r -> False.
  Proof.
    intros.
    change ((fun t => match t with
                      | Leaf _ => False
                      | Node _ _ _ => True
                      end)
              (Leaf k)).
    rewrite H.
    trivial.
  Qed.
End P8.
