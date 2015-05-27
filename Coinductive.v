Require Import Arith List CpdtTactics.

CoInductive tree (A : Type) : Type :=
| Node : A -> tree A -> tree A -> tree A.

Arguments Node {A} _ _ _.

CoFixpoint everywhere {A : Type} (v : A) : tree A :=
  Node v (everywhere v) (everywhere v).

CoFixpoint map {A B C: Type} (f : A -> B -> C) (t1 : tree A) (t2 : tree B) : tree C :=
  match t1, t2 with
  | Node v1 l1 r1, Node v2 l2 r2 => Node (f v1 v2) (map f l1 l2) (map f r1 r2)
  end.

Definition falses := everywhere false.

CoFixpoint true_falses := Node true
                               (Node false true_falses true_falses)
                               (Node false true_falses true_falses).

CoInductive tree_eq {A : Type} : tree A -> tree A -> Prop :=
| teqi : forall l1 l2 r1 r2 v1 v2,
    v1 = v2 -> tree_eq l1 l2 -> tree_eq r1 r2 -> tree_eq (Node v1 l1 r1) (Node v2 l2 r2).


Definition run {A : Type} (t : tree A) : tree A :=
  match t with
  | Node v l r => Node v l r
  end.

Lemma run_is_dummy : forall A (t : tree A),
    t = run t.
Proof.
  intros.
  destruct t.
  reflexivity.
Qed.

Theorem or_mapping :
  tree_eq (map orb true_falses falses) true_falses.
Proof.
  cofix.
  rewrite (run_is_dummy bool (map orb true_falses falses)).
  rewrite (run_is_dummy bool true_falses).
  simpl.
  constructor.
  reflexivity.
  rewrite (run_is_dummy bool (map orb (Node false true_falses true_falses) (everywhere false))).
  rewrite (run_is_dummy bool (Node false true_falses true_falses)).
  simpl.
  constructor; crush.
  rewrite (run_is_dummy bool (map orb (Node false true_falses true_falses) (everywhere false))).
  rewrite (run_is_dummy bool (Node false true_falses true_falses)).
  simpl.
  constructor; crush.
Qed.
