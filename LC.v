Set Printing Universes.
Set Universe Polymorphism.

Module LC.

Definition boolean := forall A, A -> A -> A.
Definition true : boolean := fun A t f => t.
Definition false : boolean := fun A t f => f.

Definition not : boolean -> boolean :=
  fun b => fun A t f => b A f t.

Definition and : boolean -> boolean -> boolean :=
  fun l r => fun A t f => l A (r A t f) f.

Definition or : boolean -> boolean -> boolean :=
  fun l r => fun A t f => l A t (r A t f).

Section boolean_examples.
  Variables (A: Type) (t f:A).
  Example true_ex : true A t f = t.
  Proof. trivial. Qed.

  Example false_ex : false A t f = f.
  Proof. trivial. Qed.

  Example not_t : not false = true.
  Proof. trivial. Qed.

  Example not_f : not true = false.
  Proof. trivial. Qed.

  Example and_t_t : and true true = true.
  Proof. trivial. Qed.

  Example and_t_f : and true false = false.
  Proof. trivial. Qed.

  Example and_f_t : and false true = false.
  Proof. trivial. Qed.

  Example and_f_f : and false false = false.
  Proof. trivial. Qed.

  Example or_t_t : or true true = true.
  Proof. trivial. Qed.
  
  Example or_t_f : or true false = true.
  Proof. trivial. Qed.
  
  Example or_f_t : or false true = true.
  Proof. trivial. Qed.
  
  Example or_f_f : or false false = false.
  Proof. trivial. Qed.
End boolean_examples.

Definition church := forall A, (A -> A) -> A -> A.

Definition zero : church := fun A (f:A->A) (x:A) => x.
Definition one : church := fun A (f:A->A) (x:A) => f x.
Definition two : church := fun A (f:A->A) (x:A) => f (f x).
Definition three : church := fun A (f:A->A) (x:A) => f (f (f x)).
Definition four : church := fun A (f:A->A) (x:A) => f (f (f (f x))).
Definition five : church := fun A (f:A->A) (x:A) => f (f (f (f (f x)))).

Definition succ : church -> church :=
  fun (n: church) => fun A (f: A->A) (x: A) => f (n A f x).

Definition plus : church -> church -> church :=
  fun m n => fun A (f: A->A) (x: A) => m A f (n A f x).

Definition plus' : church -> church -> church :=
  fun m n => m church succ n.

Definition mult : church -> church -> church :=
  fun m n => fun A (f: A->A) (x: A) => m A (n A f) x.
  
Definition iszero : church -> boolean :=
  fun n: church => n boolean (fun _ => false) true.

Fixpoint nat_to_church (n: nat): church :=
  match n with
    | 0 => zero
    | S x => succ (nat_to_church x)
  end.

Notation "<| n |>" := (nat_to_church n).

Section church_examples.
  Example succ_0 : succ zero = one.
  Proof. trivial. Qed.

  Example succ_1 : succ one = two.
  Proof. trivial. Qed.

  Example succ_2 : succ two = three.
  Proof. trivial. Qed.

  Example succ_3 : succ three = four.
  Proof. trivial. Qed.

  Example plus_0_N : forall (n: church), plus zero n = n.
  Proof. trivial. Qed.

  Example plus_N_0 : forall (n: church), plus n zero = n.
  Proof. trivial. Qed.

  Example plus_1_1 : plus one one = two.
  Proof. trivial. Qed.

  Example plus_2_2 : plus two two = four.
  Proof. trivial. Qed.

  Example mult_0_N : forall (n: church), mult zero n = zero.
  Proof. trivial. Qed.

  Example mult_N_0 : forall (n: church), mult n zero = zero.
  Proof. 
  (* type of n is too weak *)
  Admitted.

  Example mult_1_N : forall (n: church), mult one n = n.
  Proof. trivial. Qed.

  Example mult_N_1 : forall (n: church), mult n one = n.
  Proof. trivial. Qed.

  Example mult2_plus : forall (n: church), mult two n = plus n n.
  Proof. trivial. Qed.

  Example mult_n2_plus : forall (n: church), mult n two = plus n n.
  Proof.
  (* type of n is too weak *)
  Admitted.

  Example zero_iszero : iszero zero = true.
  Proof. trivial. Qed.

  Example one_iszero : iszero one = false.
  Proof. trivial. Qed.

  Example two_iszero : iszero two = false.
  Proof. trivial. Qed.
  
  Lemma nat_succ : forall n:nat, <|S n|> = succ <|n|>.
  Proof. trivial. Qed.

  Lemma nat_plus : forall n m: nat, plus <|n|> <|m|> = <|n+m|>.
  Proof.
    intros n.
    induction n.
    + trivial.
    + intros.
      simpl.
      rewrite <- IHn.
      trivial.
  Qed.
  
  Lemma nat_mult : forall n m: nat, mult <|n|> <|m|> = <|n*m|>.
  Proof.
    intros n.
    induction n.
    + trivial.
    + intros.
      simpl.
      rewrite <- nat_plus.
      rewrite <- IHn.
      trivial.
  Qed.
End church_examples.

Definition pair A B := forall C, (A -> B -> C) -> C.

Definition make_pair {A B} : A -> B -> pair A B :=
  fun (a:A) (b:B) => fun C p => p a b.

Definition fst {A B} : pair A B -> A := 
  fun p => p A (fun a b => a).

Definition snd {A B} : pair A B -> B := 
  fun p => p B (fun a b => b).

Section pair_examples.
  Example good_fst : forall A B, forall (a:A) (b:B),
    fst (make_pair a b) = a.
  Proof. trivial. Qed.

  Example good_snd : forall A B, forall (a:A) (b:B),
    snd (make_pair a b) = b.
  Proof. trivial. Qed.
End pair_examples.

Definition pred_step : pair church church -> pair church church :=
  fun p => make_pair (snd p) (succ (snd p)).

Section pred_step_examples.
  Example pred_step_0 : pred_step (make_pair zero zero) = make_pair zero one.
  Proof. trivial. Qed.
  Example pred_step_1 : pred_step (make_pair zero one) = make_pair one two.
  Proof. trivial. Qed.
  
  Example pred_step_2 : pred_step (make_pair one two) = make_pair two three.
  Proof. trivial. Qed.
  
  Example pred_step_3 : pred_step (make_pair two three) = make_pair three four.
  Proof. trivial. Qed.
End pred_step_examples.
  
Definition pred : church -> church :=
  fun (n: church) => fst (n (pair church church) pred_step (make_pair zero zero)).
  
Section pred_examples.
  Example pred_0 : pred zero = zero.
  Proof. trivial. Qed.
  
  Example pred_1 : pred one = zero.
  Proof. trivial. Qed.
  
  Example pred_2 : pred two = one.
  Proof. trivial. Qed.
  
  Example pred_3 : pred three = two.
  Proof. trivial. Qed.
  
  Example pred_4 : pred four = three.
  Proof. trivial. Qed.
End pred_examples.

Fail Definition sub_ch : church -> church -> church := 
  fun n m => m church pred n.

Fail Definition leq_ch : church -> church -> boolean :=
  fun n m => iszero (sub_ch n m).
  
Fail Definition le_ch : church -> church -> boolean :=
  fun n m => leq_ch (succ n) m.
  
Fail Definition iseq_ch : church -> church -> boolean :=
  fun n m => and (leq_ch n m) (leq_ch m n).
  
Definition fib_step : pair church church -> pair church church :=
  fun p => make_pair (snd p) (plus (fst p) (snd p)).
  
Section fib_step_examples.
  Example fib_step_0 : fib_step (make_pair zero one) = make_pair one one.
  Proof. trivial. Qed.
  
  Example fib_step_1 : fib_step (make_pair one one) = make_pair one two.
  Proof. trivial. Qed.
  
  Example fib_step_2 : fib_step (make_pair one two) = make_pair two three.
  Proof. trivial. Qed.
  
  Example fib_step_3 : fib_step (make_pair two three) = make_pair three five.
  Proof. trivial. Qed.
End fib_step_examples.

Definition fib : church -> church :=
  fun n => fst (n (pair church church) fib_step (make_pair zero one)).
  
Section fib_examples.
  Example fib_0 : fib zero = zero.
  Proof. trivial. Qed.
  
  Example fib_1 : fib one = one.
  Proof. trivial. Qed.
  
  Example fib_2 : fib two = one.
  Proof. trivial. Qed.
  
  Example fib_3 : fib three = two.
  Proof. trivial. Qed.
  
  Example fib_4 : fib four = three.
  Proof. trivial. Qed.
  
  Example fib_5 : fib five = five.
  Proof. trivial. Qed.
End fib_examples.

End LC.

Recursive Extraction LC.