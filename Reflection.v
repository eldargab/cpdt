Require Import QArith Quote List.
Require Import CpdtTactics.

Local Open Scope Q_scope.

Inductive Exp : Set :=
| Const : Q -> Exp
| Plus : Exp -> Exp -> Exp
| Minus : Exp -> Exp -> Exp
| Mult : Exp -> Exp -> Exp
| Var : index -> Exp.

Definition bindings := varmap Q.

Fixpoint denote (G : bindings) (e : Exp) : Q :=
  match e with
  | Const x => x
  | Plus x y => denote G x + denote G y
  | Minus x y => denote G x - denote G y
  | Mult x y => denote G x * denote G y
  | Var idx => varmap_find 0 idx G
  end.

Definition Coefficients := list (index * Q).

Fixpoint denoteCo (G : bindings) (ks : Coefficients) : Q :=
  match ks with
  | nil => 0
  | (var, k) :: ks' => varmap_find 0 var G * k + denoteCo G ks'
  end.

Fixpoint addCo (ks : Coefficients) var k : Coefficients :=
  match ks with
  | nil => (var, k) :: nil
  | (var', k') :: ks' => if index_eq var var' then
                           (var, k + k') :: ks'
                         else
                           (var', k') :: addCo ks' var k
  end.

Definition Equation := prod Coefficients Q.

Notation "x <- e1 ; e2" :=
  match e1 with
  | Some x => e2
  | None => None
  end
    (right associativity, at level 60).

Fixpoint toQ (e : Exp) : option Q :=
  match e with
  | Const x => Some x
  | Plus x y => x' <- toQ x ; y' <- toQ y ; Some (x' + y')
  | Minus x y => x' <- toQ x ; y' <- toQ y ; Some (x' - y')
  | Mult x y => x' <- toQ x ; y' <- toQ y ; Some (x' * y')
  | _ => None
  end.

Fixpoint add (eq : Equation) (e : Exp) (sign : Q) : option Equation :=
  match eq with
  | (l, r) =>  match e with
               | Const x => Some (l, r + sign * x)
               | Var idx => Some (addCo l idx sign, r)
               | Plus x y => eq' <- add eq x sign ; add eq' y sign
               | Minus x y => eq' <- add eq x sign; add eq' y (- sign)
               | Mult x y => let eq1 := x' <- toQ x ; add eq y (x' * sign) in
                             let eq2 := y' <- toQ y ; add eq x (y' * sign)
                             in
                             if eq1 then eq1 else eq2
               end
  end.

Definition denoteEquation (G : bindings) (eq : Equation) :=
  match eq with
  | (l, r) => denoteCo G l + r
  end.

Definition normalize (e : Exp) : option Equation :=
  add (nil, 0) e 1.

Ltac letpairs :=
  repeat
    match goal with
    | [|- context[let (_, _) := ?p in _]] => rewrite (surjective_pairing p); simpl;
                                             try rewrite <- (surjective_pairing p)
    end;
  repeat
    match goal with
    | [H : context[let (_, _) := ?p in _] |- _] => rewrite (surjective_pairing p) in H; simpl in H;
                                                   try rewrite <- (surjective_pairing p) in H
    end.

Ltac do_notation_case :=
  match goal with
  | [H : context[_ <- ?x ; _] |- _] => let Heq := fresh in
                                       destruct x eqn:Heq; try solve [inversion H]
  end.

Ltac if_case :=
  match goal with
  | [H : context[if ?x then _ else _] |- _] => let Heq := fresh in destruct x eqn:Heq
  | [|- context[if ?x then _ else _]] => let Heq := fresh in destruct x eqn:Heq
  end.
     
Ltac newvar T k :=
  let x := fresh in
  evar (x : T); let y := eval unfold x in x
                  in clear x; k y.

Ltac inst_hyp H :=
  match type of H with
  | forall (_ : _ = _), _ => match goal with
                             | [x : _ = _ |- _] => specialize (H x)
                             end || specialize (H (eq_refl _)) || fail 1
  | forall (_ : ?T), _ => newvar T ltac:(fun x => specialize (H x)); inst_hyp H
  | _ => fail
  end.

Ltac inst_hyps :=
  repeat match goal with
         | [H : forall _, _ |- _] => inst_hyp H
         end.

Ltac some_inversion :=
  repeat match goal with
         | [H : Some _ = Some _ |- _] => injection H; clear H; intro
         end.

Ltac rewrite_with_hyps :=
  repeat match goal with
         | [ H : _ |- _ ] => rewrite H
         end.

Lemma toQ_correct : forall e q G,
    toQ e = Some q -> denote G e = q.
Proof.
  induction e;
  simpl;
  intros;
  repeat do_notation_case;
  inversion H; 
  solve [reflexivity | inst_hyps; crush].
Qed.

Lemma add_correct : forall e eq eq' sign G,
    add eq e sign = Some eq' ->
    denoteEquation G eq' == denoteEquation G eq + sign * denote G e.
Proof.
  unfold denoteEquation.
  
  induction e; simpl; intros; letpairs.

  (* Const *)
  inversion H; simpl; ring.

  (* Plus *)
  do_notation_case. inst_hyps. letpairs. rewrite_with_hyps. ring.

  (* Minus *)
  do_notation_case. inst_hyps. letpairs. rewrite_with_hyps. ring.
  
  (* Mult *)
  do_notation_case;
    try if_case;
    try some_inversion;
    try do_notation_case;
    inst_hyps;
    letpairs;
    subst;
    match goal with
    | [H : toQ _ = Some _ |- _] =>  apply (toQ_correct _ _ G) in H
    end;
    rewrite_with_hyps;
    ring.

  (* Variable *)
  some_inversion.
  subst.
  simpl.
  induction (fst eq); simpl.
  ring.
  letpairs.
  if_case; simpl.
  apply index_eq_prop in H.
  subst.
  ring.
  letpairs.
  rewrite <- Qplus_assoc.
  rewrite_with_hyps.
  ring.
Qed.

Theorem normalize_correct : forall e eq,
    normalize e = Some eq -> forall G, denote G e == denoteEquation G eq.
Proof.
  unfold normalize.
  intros.
  assert (L := add_correct e (nil, 0) eq 1 G H).
  simpl in L.
  ring_simplify in L.
  symmetry.
  assumption.
Qed.
  
Lemma equation_addition : forall a b c d,
    a == b -> c == d -> a + c == b + d.
Proof.
  crush.
Qed.

Lemma left_constant : forall G ks q r,
    denoteEquation G (ks, q) == r <-> denoteCo G ks == r - q.
Proof.
  split; intros; unfold denoteEquation in *;
  first [rewrite H | rewrite <- H];
  ring.
Qed.

Ltac add_together :=
  assert (H_sum : 0 == 0) by reflexivity;
  repeat
    match goal with
    | [H_sum : _ |- _] => fail
    | [H : ?l == ?r |- _] => match goal with
                             | [_ : done H |- _] => fail 1
                             | _ => assert (done H) by constructor;
                                 apply (equation_addition l r _ _ H) in H_sum
                             end
    end;
  un_done.

Ltac someOut e :=
  match eval compute in e with
  | Some ?x => x
  end.

Ltac reify :=
  add_together;
  repeat match goal with
         | [H : ?l == ?r |- _] =>
           match l with
           | denoteCo _ _ => fail 1
           | _ => 
             quote denote [Qmake xI xO xH Z0 Zpos Zneg]
               in l using (fun d =>
                             match d with
                             | denote _ ?e =>
                               change (d == r) in H;
                             let eq := (someOut (normalize e))
                             in rewrite (normalize_correct e eq) in H;
                             auto;
                             rewrite left_constant in H
                             end)
           end
         end;
  repeat match goal with
         | [H : denoteCo _ _ == _ |- _] => simpl in H; ring_simplify in H
         end;
  match goal with
  | [|- ?l == ?r ] =>
    quote denote [Qmake xI xO xH Z0 Zpos Zneg]
      in l using (fun d =>
                    match d with
                    | denote _ ?e =>
                      change (d == r);
                    let eq := (someOut (normalize e))
                    in rewrite (normalize_correct e eq);
                    auto;
                    rewrite left_constant;
                    simpl;
                    ring_simplify 
                    end)
  end.

Ltac finish :=
  match goal with
  | [H : _ == ?r |- _ == ?r] => rewrite <- H; ring
  end.

Theorem test : forall x y z,
    (2 # 1) * (x - (3 # 2) * y) == 15 # 1 ->
    z + (8 # 1) * x == 20 # 1 ->
    (-6 # 2) * y + (10 # 1) * x + z == 35 # 1.
Proof.
  intros.
  reify.
  finish.
Qed.
