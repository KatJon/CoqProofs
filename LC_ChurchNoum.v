Definition church {A: Type} := (A->A) -> A -> A.

Definition Zero {A: Type} : church := fun  (f: A->A) (x: A) => x.
Definition One {A: Type} := fun (f: A->A) (x: A) => f x.
Definition Two {A: Type} := fun (f: A->A) (x: A) => f (f x).
Definition Three {A: Type} := fun (f: A->A) (x: A) => f (f (f x)).
Definition Four {A: Type} := fun (f: A->A) (x: A) => f (f (f (f x))).

Definition Plus {A: Type} : church -> church -> church := 
  fun (a b: church) (f: A->A) (x: A) => a f (b f x).

Example Plus_01 : forall (A: Type) (f: A->A) (x: A),
  (Plus Zero One) f x = One f x.
Proof. reflexivity. Qed.

Example Plus_22 : forall (A: Type) (f: A->A) (x: A),
  (Plus Two Two) f x = Four f x.
Proof. reflexivity. Qed.

Definition Mult {A: Type} : church -> church -> church :=
  fun (a b: church) (f: A->A) (x: A) => a (b f) x.

Example Mult_01 : forall (A: Type) (f: A->A) (x: A),
  (Mult Zero One) f x = Zero f x.
Proof. reflexivity. Qed.

Example Mult_22 : forall (A: Type) (f: A->A) (x: A),
  (Mult Two Two) f x = Four f x.
Proof. reflexivity. Qed.

Definition Pow {A: Type} : church -> church -> church :=
  fun (a b: church) (f: A->A) (x: A) => (b a) f x.

Example Pow_20 : forall (A: Type) (f: A->A) (x:A),
  (Pow Two Two) f x = Four f x.
Proof. reflexivity. Qed.

Fixpoint iterate {A: Type} (n: nat) (f: A->A) (x: A) : A := 
  match n with
    | O => x
    | S m => f (iterate m f x)
  end.

Theorem nat_church_corr : forall (A: Type) (f: A->A) (x: A) (n: nat), 
  