Definition boolean {A: Type} := A->A->A.
Definition True {A: Type} : boolean := fun (T F:A) => T.

Example true_gen1 : forall (A: Type) (a b: A), True a b = a.
Proof. reflexivity. Qed.

Definition False {A: Type} : boolean := fun (T F:A) => F.

Example false_gen1 : forall (A: Type) (a b: A), False a b = b.
Proof. reflexivity. Qed.

Definition Not {A: Type} : boolean -> boolean := fun (f: boolean) (T F:A) =>
f F T.

Example not_gen1 : forall (A: Type) (a b:A), (Not True) a b = b.
Proof. reflexivity. Qed.

Example not_gen2 : forall (A: Type) (a b:A), (Not False) a b = a.
Proof. reflexivity. Qed.

Definition And {A: Type} : boolean -> boolean -> boolean :=
  fun (f: boolean) (g: boolean) (T F: A) => f (g T F) F.

Example and_ex1 : forall (A: Type) (a b:A), (And True True) a b = a.
Proof. reflexivity. Qed.

Example and_ex2 : forall (A: Type) (a b:A), (And True False) a b = b.
Proof. reflexivity. Qed.

Example and_ex3 : forall (A: Type) (a b:A), (And False True) a b = b.
Proof. reflexivity. Qed.

Example and_ex4 : forall (A: Type) (a b:A), (And False False) a b = b.
Proof. reflexivity. Qed.

Definition Or {A: Type} : boolean -> boolean -> boolean :=
  fun (f: boolean) (g: boolean) (T F: A) => f T (g T F).

Example or_ex1 : forall (A: Type) (a b:A), (Or True True) a b = a.
Proof. reflexivity. Qed.

Example or_ex2 : forall (A: Type) (a b:A), (Or True False) a b = a.
Proof. reflexivity. Qed.

Example or_ex3 : forall (A: Type) (a b:A), (Or False True) a b = a.
Proof. reflexivity. Qed.

Example or_ex4 : forall (A: Type) (a b:A), (Or False False) a b = b.
Proof. reflexivity. Qed.