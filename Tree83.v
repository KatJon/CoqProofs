Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

(* Zadanie 83. *)

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

Definition Natural F G {FunF : Functor F} {FunG : Functor G} := forall A, F A -> G A.

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

Class Monad (F: Type -> Type) := {
  monad_applicative : Applicative F;
  ret : forall {A}, A -> F A;
  bind : forall {A X}, F A -> (A -> F X) -> F X;
  monad_left_id : forall A X (a: A) (f: A -> F X),
    bind (ret a) f = f a;
  monad_right_id : forall A (m: F A), bind m ret = m;
  monad_assoc : forall A X Y (m : F A) (f: A -> F X) (g: X -> F Y),
    bind (bind m f) g = bind m (fun x => bind (f x) g);
}.

Fixpoint Tree_bind {A X} (fa: Tree A) (f: A -> Tree X) : Tree X :=
  match fa with
  | L _ a => f a
  | B _ l r => B X (Tree_bind l f) (Tree_bind r f)
  end.

Instance Monad_Tree : Monad Tree := {
  monad_applicative := Applicative_Tree;
  ret := L;
  bind := @Tree_bind;
}.
Proof.
  - trivial.
  - intros.
    induction m.
    + trivial.
    + simpl in *.
      rewrite IHm1.
      rewrite IHm2.
      trivial.
  - intros.
    induction m.
    + trivial.
    + simpl in *.
      rewrite IHm1.
      rewrite IHm2.
      trivial.
Defined.

Class MonadJoin (F: Type -> Type) := {
  monadjoin_applicative : Applicative F;
  monadjoin_functor : Functor F := applicative_functor;
  eta : forall {A}, A -> F A;
  mu : forall {A}, F (F A) -> F A;
  monadjoin_left_id : forall A (fa: F A), mu (eta fa) = fa;
  monadjoin_right_id : forall A (fa: F A), 
    mu (fmap eta fa) = fa;
  monadjoin_assoc : forall A (ma : F (F (F A))),
    mu (mu ma) = mu (fmap mu ma);
}.

Fixpoint Tree_mu {A} (ma: Tree (Tree A)) : Tree A := 
  match ma with
  | L _ t => t
  | B _ l r => B A (Tree_mu l) (Tree_mu r)
  end.

Instance MonadJoin_Tree : MonadJoin Tree := {
  eta := L;
  mu := @Tree_mu;
}.
Proof.
  - trivial.
  - intros.
    induction fa.
    + trivial.
    + simpl in *.
      rewrite IHfa1.
      rewrite IHfa2.
      trivial.
  - intros.
    induction ma.
    + trivial.
    + simpl in *.
      rewrite IHma1.
      rewrite IHma2.
      trivial.
Defined.