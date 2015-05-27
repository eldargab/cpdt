Require Import Arith Bool List DepList.

Module Tree_Idx.
  Inductive tree (A : Type) : Type :=
  | Leaf : A -> tree A
  | Node : tree A -> tree A -> tree A.

  Arguments Leaf {A} _.
  Arguments Node {A} _ _.

  Inductive Path {A} (a : A) : tree A -> Type :=
  | Empty : Path a (Leaf a)
  | Left : forall l r, Path a l -> Path a (Node l r)
  | Right : forall l r, Path a r -> Path a (Node l r).

  Inductive htree {A} B idx : Type :=
  | Tf : (forall (a : A), Path a idx -> B a) -> htree B idx.

  Definition map {A B C D idx}
             (f : forall a, B a -> C a -> D a)
             (t1 : htree B idx)
             (t2 : htree C idx)
    : htree D idx :=
    match t1, t2 with
    | Tf f1, Tf f2 => @Tf A D idx (fun a p => f a (f1 a p) (f2 a p))
    end.
End Tree_Idx.

Module Tree_Rec.
  Inductive tree (A : Type) : Type :=
  | Leaf : A -> tree A
  | Node : tree A -> tree A -> tree A.

  Arguments Leaf {A} _.
  Arguments Node {A} _ _.

  Fixpoint htree {A} (B : A -> Type) (idx : tree A) : Type :=
    match idx with
    | Leaf a => B a
    | Node l r => htree B l * htree B r
    end%type.

  Fixpoint Path {A : Type} a (idx : tree A) : Type :=
    match idx with
    | Leaf a' => a' = a
    | Node l r => Path a l + Path a r
    end%type.

  Fixpoint get {A} B idx (t : htree B idx) {a : A} (p : Path a idx) : B a :=
    match idx return htree B idx -> Path a idx -> B a with
    | Node li ri => fun t p =>
                      match t with
                      | pair l r => match p with
                                    | inl p' => get B li l p'
                                    | inr p' => get B ri r p'
                                    end
                      end
    | Leaf _ => fun t p =>
                  match p with
                  | eq_refl => t
                  end
    end t p.

  Fixpoint map {A B C D} {idx : tree A}
           (f : forall a, B a -> C a -> D a)
           (t1 : htree B idx)
           (t2 : htree C idx)
    : htree D idx :=
    match idx return htree B idx -> htree C idx -> htree D idx
    with
    | Leaf a => fun t1 t2 => f a t1 t2
    | Node l r => fun t1 t2 => (map f (fst t1) (fst t2), map f (snd t1) (snd t2))
    end t1 t2.
End Tree_Rec.

Module Tree_Ind.
  Inductive tree (A : Type) : Type :=
  | Leaf : A -> tree A
  | Node : tree A -> tree A -> tree A.

  Arguments Leaf {A} _.
  Arguments Node {A} _ _.

  Inductive htree {A : Type} (B : A -> Type) : tree A -> Type :=
  | L : forall (a : A) (x : B a), htree B (Leaf a)
  | N : forall (T1 T2 : tree A) (t1 : htree B T1) (t2 : htree B T2), htree B (Node T1 T2).

  Arguments L {A} {B} {a}  _.
  Arguments N {A} {B} {T1} {T2} _ _.

  Inductive Path {A} (a : A) : tree A -> Type :=
  | Empty : Path a (Leaf a)
  | Left : forall l r, Path a l -> Path a (Node l r)
  | Right : forall l r, Path a r -> Path a (Node l r).

  Fixpoint get {A B idx a} (t : htree B idx) (p : Path a idx) : B a :=
    match p in Path _ idx return @htree A B idx -> B a
    with
    | Empty => fun t =>
                 match t in htree _ idx return match idx with
                                               | Leaf a => B a
                                               | Node _ _ => unit
                                               end
                 with
                 | L _ x => x
                 | N _ _ _ _ => tt
                 end
    | Left tl _ p' => fun t =>
                        match t in htree _ idx return match idx with
                                                      | Leaf _ => unit
                                                      | Node tl _ => Path a tl -> B a
                                                      end
                        with
                        | L _ _ => tt
                        | N _ _ l _ => fun p' => get l p'
                        end p'
    | Right _ _ p' => fun t =>
                        match t in htree _ idx return match idx with
                                                      | Leaf _ => unit
                                                      | Node _ tr => Path a tr -> B a
                                                      end
                        with
                        | L _ _ => tt
                        | N _ _ _ r => fun p' => get r p'
                        end p'
    end t.

  Fixpoint map {A B C D} {idx : tree A}
           (f : forall a, B a -> C a -> D a)
           (t1 : htree B idx)
           (t2 : htree C idx)
    : htree D idx :=
    match t1 in htree _ idx return htree C idx -> htree D idx
    with
    | L _ x => fun t2 =>
                 match t2 in htree _ idx return match idx with
                                                | Leaf a => B a -> htree D idx
                                                | _ => unit
                                                end
                 with
                 | L a y => fun x => L (f a x y)
                 | _ => tt
                 end x
    | N tl tr l r => fun t2 =>
                       match t2 in htree _ idx return match idx with
                                                      | Leaf _ => unit
                                                      | Node tl tr => htree B tl -> htree B tr -> htree D idx
                                                      end
                       with
                       | L _ _ => tt
                       | N _ _ l' r' => fun l r => N (map f l l') (map f r r')
                       end l r
    end t2.
End Tree_Ind.

Module Interpreter.
  Inductive ty : Set :=
  | Bool : ty
  | Sum : ty -> ty -> ty.

  Fixpoint denote (t : ty) : Set :=
    match t with
    | Bool => bool
    | Sum t1 t2 => denote t1 + denote t2
    end%type.

  Definition var := nat.

  Definition binding := prod var ty.

  Definition bindings := list binding.

  Inductive P : bindings -> ty -> Set :=
  | PVar : forall T x, P (pair x T :: nil) T
  | PConst : bool -> P nil Bool
  | PLeft : forall bs T1 T2, P bs T1 -> P bs (Sum T1 T2)
  | PRight : forall bs T1 T2, P bs T2 -> P bs (Sum T1 T2).

  Definition Patterns (bs : list bindings) (T : ty) :=
    hlist (fun b => P b T) bs.

  Inductive Exp : bindings -> ty -> Set :=
  | Var : forall bs T v, member (v, T) bs -> Exp bs T
  | Const : forall bs, bool -> Exp bs Bool
  | Left : forall bs T1 T2, Exp bs T1 -> Exp bs (Sum T1 T2)
  | Right : forall bs T1 T2, Exp bs T2 -> Exp bs (Sum T1 T2)
  | Case : forall bs T1 T2
                  (pbs : list bindings)
                  (patterns : Patterns pbs T1),
      (forall b, member b pbs -> Exp (b ++ bs) T2)
      -> Exp bs T2
      -> Exp bs T1
      -> Exp bs T2.

  Definition PExps (bs : bindings) (pbs : list bindings) (T : ty) :=
    hlist (fun b => Exp (b ++ bs) T) pbs.

  Definition bindingType (b : binding) : Set :=
    denote (snd b).

  Definition Env (bs : bindings):=
    hlist bindingType bs.

  Fixpoint patternMatch {pbs T} (p : P pbs T) (v : denote T) {bs} (G : Env bs)
    : option (Env (pbs ++ bs)) :=
    match p in P pbs T return denote T -> Env bs -> option (Env (pbs ++ bs))
    with
    | PVar T x => fun v G => Some (@HCons binding bindingType (x, T) bs v G)
    | PConst b => fun v G => if bool_dec b v then Some G else None
    | PLeft _ _ _ p' => fun v G => match v with
                                   | inl x => patternMatch p' x G
                                   | _ => None
                                   end
    | PRight _ _ _ p' => fun v G => match v with
                                    | inr x => patternMatch p' x G
                                    | _ => None
                                    end
    end v G.

  Definition Matched (bs : bindings) (pbs : list bindings) :=
    fun b => prod (member b pbs) (Env (b ++ bs)).

  Fixpoint matched {bs pbs T}
           (patterns : Patterns pbs T)
           (G : Env bs)
           (v : denote T)
    : option (sigT (Matched bs pbs)) :=
    match patterns with
    | HCons b pbs' p patterns' =>
      match patternMatch p v G with
      | Some G' => Some (existT _ b (@HFirst bindings b pbs', G'))
      | None => match matched patterns' G v with
                | Some (existT b (m, G'))
                  => Some (existT _ b (HNext m, G'))
                | None => None
                end
      end
    | _ => None
    end.

  Fixpoint eval {T bs} (e : Exp bs T) (G : Env bs) {struct e} : denote T :=
    match e in Exp bs T return Env bs -> denote T
    with
    | Var _ _ v m => fun G => hget G m
    | Const _ b => fun _ => b
    | Left _ _ _ e' => fun G => inl (eval e' G)
    | Right _ _ _ e' => fun G => inr (eval e' G)
    | Case bs T1 T2 pbs patterns exps def e' =>
      fun G =>
        match matched patterns G (eval e' G) with
        | Some (existT b (m, G')) => eval (exps b m) G'
        | None => eval def G
        end
    end G.
End Interpreter.
