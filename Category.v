Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

Module Category.

Class Functor (F: Type -> Type) := {
  fmap : forall {A B}, (A -> B) -> (F A -> F B);
  fmap_pres_comp : forall (A B C: Type) (f: A->B) (g: B->C),
    fmap (compose g f) = compose (fmap g) (fmap f);
  fmap_pres_id : forall A, fmap (@id A) = @id (F A);
}.

Fixpoint fmap_list {A B} (f: A -> B) (l: list A) : list B :=
  match l with
  | nil => nil
  | cons h t => cons (f h) (fmap_list f t)
  end.

Instance Functor_list : Functor list := {
  fmap := @fmap_list
}.
Proof.
  - intros.
    extensionality l.
    induction l.
    + trivial.
    + simpl.
      rewrite IHl.
      trivial.
  - intros.
    extensionality l.
    induction l.
    + trivial.
    + simpl.
      rewrite IHl.
      trivial.
Defined.

Definition fmap_option {A B} (f: A->B) (o: option A) : option B :=
  match o with
  | None => None
  | Some a => Some (f a)
  end.
  
Instance Functor_option : Functor option := {
  fmap := @fmap_option
}.
Proof.
  - intros.
    extensionality o.
    destruct o; trivial.
  - intros.
    extensionality o.
    destruct o; trivial.
Defined.

Inductive tree A :=
| leaf : tree A
| node : A -> tree A -> tree A -> tree A
.

Fixpoint fmap_tree {A B} (f: A->B) (t: tree A) : tree B :=
  match t with
  | leaf _ => leaf _
  | node _ e l r => node _ (f e) (fmap_tree f l) (fmap_tree f r)
  end.

Instance Functor_tree : Functor tree := {
  fmap := @fmap_tree
}.
Proof.
  - intros.
    extensionality t.
    induction t.
    + trivial.
    + simpl.
      rewrite IHt1, IHt2.
      trivial.
  - intros.
    extensionality t.
    induction t.
    + trivial.
    + simpl.
      rewrite IHt1, IHt2.
      trivial.
Defined.
