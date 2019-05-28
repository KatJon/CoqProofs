Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

Module Tree83.

Inductive Tree a :=
  | L : a -> Tree a
  | B : Tree a -> Tree a -> Tree a
.

Class Functor (F: Type -> Type) := {
  fmap : forall {A B}, (A -> B) -> (F A -> F B);
  fmap_pres_comp : forall (A B C: Type) (f: A->B) (g: B->C),
    fmap (compose g f) = compose (fmap g) (fmap f);
  fmap_pres_id : forall A, fmap (@id A) = @id (F A);
}.

Instance Functor_tree : Functor Tree := {
  fmap := fix rec A X f t :=
    match t with
    | L _ a => L X (f a)
    | B _ l r => B X (rec A X f l) (rec A X f r)
    end
}.
Proof.
  - intros.
    extensionality l.
    induction l.
    + trivial.
    + simpl.
      rewrite IHl1.
      rewrite IHl2.
      trivial.
  - intros.
    extensionality l.
    induction l.
    + trivial.
    + simpl.
      rewrite IHl1.
      rewrite IHl2.
      trivial.
Defined.

Class Applicative (F: Type -> Type) := {
  applicative_functor: Functor F;
  pure : forall {A}, A -> F A;
  ap : forall {A B}, F (A -> B) -> F A -> F B;
  pure_id : forall A (v: F A), 
    ap (pure (@id A)) v = v;
  pure_compose : forall A B C 
    (u:F (B->C)) (v: F (A->B)) (w: F A),
    ap (ap (ap (pure compose) u) v) w = ap u (ap v w);
  pure_homo : forall A B (f:A->B) (x:A),
    ap (pure f) (pure x) = pure (f x);
  pure_int : forall A B (u : F (A->B)) (y: A),  
    ap u (pure y) = ap (pure (fun x => x y)) u;
}.


Fixpoint ap_tree {A X} (ff: Tree (A->X)) (fa: Tree A) :=
  match ff with
  | L _ f => fmap f fa
  | B _ l r => B X (ap_tree l fa) (ap_tree r fa)
  end.

Instance Applicative_Tree : Applicative Tree := {
  applicative_functor := Functor_tree;
  pure := L;
  ap := @ap_tree;
}.
Proof.
  - intros.
    induction v.
    + trivial.
    + unfold ap_tree.
      rewrite fmap_pres_id. 
      unfold id. 
      trivial.
  - intros A B C u v w.
    induction u; induction v; induction w.
    + trivial.
    + simpl in *.
      rewrite IHw1.
      rewrite IHw2.
      trivial.
    + simpl in *.
      rewrite IHv1.
      rewrite IHv2.
      trivial.
    + simpl in *.
      rewrite IHv1.
      rewrite IHv2.
      trivial.
    + simpl in *.
      rewrite IHu1.
      rewrite IHu2.
      trivial.
    + simpl in *.
      rewrite IHu1.
      rewrite IHu2.
      trivial.
    + simpl in *.
      rewrite IHu1.
      rewrite IHu2.
      trivial.
    + simpl in *.
      rewrite IHu1.
      rewrite IHu2.
      trivial.
  - intros.
    simpl in *.
    trivial.
  - intros.
    induction u.
    + trivial.
    + simpl in *.
      rewrite IHu1.
      rewrite IHu2.
      trivial.
Defined.