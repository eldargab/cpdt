Require Import  Bool Arith List.
Require Import CpdtTactics.
Require Import MoreSpecif.

Module EQ.
  Require Import DepList.
  Require Import FunctionalExtensionality.
  Require Import Eqdep.
  
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
End EQ.

Module DS2.
  Require Import DepList.
  
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
End DS2.

Module DS1_idx.
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
End DS1_idx.

Module DS1_Rec.
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
End DS1_Rec.

Module DS1_Ind.
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

  (* Fixpoint get {A B idx a} (t : htree B idx) (p : Path a idx) : B a := *)
  (*   match t, p with *)
  (*   | L _ x, Empty  => x *)
  (*   | L _ _, _ => tt *)
  (*   | N _ _ l r, Left _ _ p' => get l p' *)
  (*   | N _ _ l r, Right _ _ p' => get r p' *)
  (*   | N _ _ l r, _ => tt *)
  (*   end. *)

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
  
End DS1_Ind.

Module Dep1.
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
End Dep.

Local Open Scope specif.

(* Module Sub3. *)
(*   Definition var := nat. *)

(*   Definition universe := var -> bool. *)

(*   Inductive val : Set := *)
(*   | T : var -> val *)
(*   | F : var -> val. *)

(*   Definition variable (v : val) : var := *)
(*     match v with *)
(*     | T x => x *)
(*     | F x => x *)
(*     end. *)

(*   Definition sign (v : val) : bool := *)
(*     if v then true else false. *)

(*   Definition clause := list val. *)

(*   Definition formula := list clause. *)

(*   Definition checkVal (U : universe) (v : val) : bool := *)
(*     match v with *)
(*     | T x => U x *)
(*     | F x => negb (U x) *)
(*     end. *)

(*   Definition checkClause (U : universe) (c : clause) : bool := *)
(*     fold_left orb (map (checkVal U) c) false. *)

(*   Definition check (U : universe) (f : formula) : bool := *)
(*     fold_left andb (map (checkClause U) f) true. *)

(*   Definition falses : universe := fun _ => false. *)

(*   Definition set (U : universe) (x : var) (b : bool) := *)
(*     fun y => if eq_nat_dec x y then b else U y. *)

(*   Definition assign_clause : forall x b c, {c' | forall U, U x = b -> checkClause U c' = checkClause U c} + *)
(*                                            {forall U, U x = b -> checkClause U c = true}. *)
(*   Proof. *)
(*     intros. *)
(*     refine ((fix rec c : {c' | forall U, U x = b -> checkClause U c' = checkClause U c} + *)
(*                          {forall U, U x = b -> checkClause U c = true} *)
(*              := *)
(*                match c with *)
(*                | nil => [|| nil ||] *)
(*                | v :: vs => if eq_nat_dec (variable v) x then  *)
(*                               if bool_dec (sign v) b then *)
(*                                 !! *)
(*                               else *)
(*                                 vs' <-- rec vs ; [|| vs' ||] *)
(*                             else *)
(*                               vs' <-- rec vs ; [|| v :: vs' ||] *)
(*                end) c); intros; simpl. *)
(*     reflexivity. *)
(*   Abort. *)


(*   Definition assign : forall f x b, {f' | forall U, U x = b -> check U f' = check U f} + *)
(*                                     {forall U, U x = b -> check U f = false}. *)
(*   Proof. *)
(*     refine (fix F f := *)
(*               match f with *)
(*               | Nil => [|| Nil ||] *)
(*               | c :: t => fold_left orb *)
(*                                     (map (fun v => match v with *)
(*                                                        | T y => if eq_nat_dec x y then b else false *)
(*                                                        | N y => if eq_nat_dec x y then negb b else false *)
(*                                                    end) *)
(*                                          c) *)
(*                                     false). *)

(*   Definition dpll: forall f, {U | check U f = true} + {forall U, check U f = false}. *)
(*   Proof. *)
(*     refine ((fix solve U f => *)
(*              match f with *)
(*              | Nil => [|| U ||] *)
(*              | c :: t => (fix try c : {U | check U (c :: t) = true} + {forall U, check U f = false} := *)
(*                             match c with *)
(*                             | Nil => !! *)
(*                             | v :: vs => let b := if v then true else false in *)
(*                                          f' <-- assign t (variable v) b ; solve (set U (variable v) b) f' ;;; try vs *)
(*                             end) c *)
(*              end) falses f). *)
(*   Admitted. *)

(* End Sub3. *)

Module Sub2.
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
End Sub2.

Module Sub1.
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
End Sub1.

Local Close Scope specif.

Module Co.
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
  
End Co.

Module P3.
  Inductive fits : nat -> Prop :=
  | f6 : fits 6
  | f10 : fits 10
  | fp : forall n k, fits k -> fits (n * k).

  Theorem fitted_is_even : forall n,
      fits n -> exists k, 2 * k = n.
  Proof.
    induction 1.
    exists 3; reflexivity.
    exists 5; reflexivity.
    inversion IHfits as [k' Hk].
    exists (n * k').
    rewrite mult_comm.
    rewrite <- mult_assoc.
    rewrite mult_comm in Hk.
    rewrite Hk.
    reflexivity.
  Qed.

  Theorem odd_doesnt_fit: forall n,
      fits (2 * n + 1) -> False.
  Proof.
    intros.
    apply fitted_is_even in H.
    inversion H.
    eapply odd_even_lem.
    symmetry.
    eassumption.
  Qed.
  
  Theorem doesnt_fit_13 :
    fits 13 -> False.
  Proof.
    change (fits 13) with (fits (2 * 6 + 1)).
    apply odd_doesnt_fit.
  Qed.
End P3.


Module IT8.
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
End IT8.


Module IT7.
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
End IT7.

Module IT6.
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
End IT6.

Module IT5.
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
End IT5.

Module IT4.
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
End IT4.

Module IT3.
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
    forallall G e,
      expDenote G (fold e) = expDenote G e.
  Proof.
    induction e; crush.
    destruct (fold e1); destruct (fold e2); crush.
  Qed.
End IT3.
