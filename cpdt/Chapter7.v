Require Import Coq.Lists.List.
Require Import Arith List Omega Program.

Require Import Cpdt.CpdtTactics Cpdt.Coinductive.

Require Extraction.


Lemma refl_n : forall (n : nat), n = n.
Proof.
  reflexivity.
Defined.

Fixpoint for_example (n: nat) : n = n :=
  let _ := for_example (S n) in (refl_n n).

Lemma refl_n' : forall (n : nat), n = n.
Proof.
  intro.
  apply (for_example n).
Defined.

(* Eval compute in refl_n' 1. *)

CoInductive infiniteDecreasingChain A (R : A -> A -> Prop) :
    stream A -> Prop := 
| ChainCons : forall x y s, infiniteDecreasingChain A R (Cons y s) 
    -> R y x
    -> infiniteDecreasingChain A R (Cons x (Cons y s)).

Check Acc_ind.
Check Acc_rec.

(* Inductive Acc' (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
| Acc_intro' : forall y : A, R y x -> Acc' A R x.

Check Acc'_ind. *)

Lemma noBadChains' : forall A (R : A -> A -> Prop) x, Acc R x
    -> forall s, ~ infiniteDecreasingChain A R (Cons x s).
Proof.
    intros. generalize dependent s. unfold not. 
    induction H. clear H. intros. 
    inversion H. subst.
    apply H0 in H3; auto.
Qed.

Check nat_ind.

Definition lengthOrder A (ls1 ls2 : list A) :=
    length ls1 < length ls2.

Lemma lengthOrder_wf' : forall A len ls, length ls <= len -> Acc (lengthOrder A) ls.
Proof.
    unfold lengthOrder.
    induction len; intros; apply Acc_intro; intros; try apply IHlen; omega.
Defined.

Lemma lengthOrder_wf : forall A, well_founded (lengthOrder A).
Proof.
    unfold well_founded. intros.
    eapply lengthOrder_wf'. auto.
Defined.


Fixpoint insert' A (le : A -> A -> bool) (x : A) (ls : list A) : list A :=
  match ls with
  | nil => x :: nil
  | h :: ls' =>
    if le x h then x :: ls else h :: insert' _ le x ls'
  end.

Fixpoint merge' A (le : A -> A -> bool) (ls1 ls2 : list A) : list A :=
  match ls1 with
  | nil => ls2
  | h :: ls' => insert' _ le h (merge' _ le ls' ls2)
  end.

Fixpoint split' A (ls : list A) : list A * list A :=
  match ls with
  | nil => (nil, nil)
  | h :: nil => (h :: nil, nil)
  | h1 :: h2 :: ls' =>
    let (ls1, ls2) := split' _ ls' in
    (h1 :: ls1 , h2 :: ls2 )
  end.

(* Fixpoint mergeSort A (le : A -> A -> bool) (ls : list A) {struct ls}: list A :=
  if leb (length ls) 1
  then ls
  else 
    let lss := split' A ls in
      merge' A le (mergeSort A le (fst lss)) (mergeSort A le (snd lss)). *)


Lemma split_wf : forall A len ls, 2 <= length ls <= len
  -> let (ls1, ls2) := split' A ls in
  lengthOrder A ls1 ls /\ lengthOrder A ls2 ls.
unfold lengthOrder. induction len; intros.
- (* len = 0 *) omega.
- destruct ls; simpl in H.
  + (* length ls = 0 *) omega.
  + destruct ls; simpl in H.
    * (* length ls = 1*) omega.
    * destruct (le_lt_dec 2 (length ls)); simpl.
      -- specialize (IHlen ls); destruct (split' A ls). assert (2 <= length ls <= len). { omega. } apply IHlen in H0. simpl. split; omega.
      -- destruct ls. 
         ++ simpl. omega.
         ++ destruct ls.
            ** simpl. omega.
            ** simpl in l. omega. 
Defined.




Lemma split_wf1 : forall A  ls, 2 <= length ls
 -> lengthOrder A (fst (split' A ls)) ls.
Proof.
 intros A ls.
 intros.
 generalize (split_wf A (length ls) ls). destruct (split' A ls). destruct 1. omega. auto. 
 Defined.

 
Lemma split_wf2 : forall A  ls, 2 <= length ls
 -> lengthOrder A (snd (split' A ls)) ls.
Proof.
 intros A ls.
 intros.
 specialize (split_wf A (length ls) ls). destruct (split' A ls). destruct 1. omega. auto. 
Defined.


Program Fixpoint mergeSort A (le : A -> A -> bool) (ls : list A) {measure (length ls)}: list A :=
  match ls with 
  | nil => nil
  | h :: nil => h :: nil 
  | h1 :: h2 :: ls' =>
    let lss := split' A ls in
      merge' A le (mergeSort A le (fst lss)) (mergeSort A le (snd lss))
  end. 
  Next Obligation.
  (* generalize (split_wf A (length (h1 :: h2 :: ls')) (h1 :: h2 :: ls')). destruct (split' A (h1 :: h2 :: ls')). destruct 1. simpl. omega. 
  simpl. assumption. *)
  apply split_wf1. simpl. omega.
  Qed.
  Next Obligation.
  apply split_wf2. simpl. omega.
  Qed.


Require Import FunInd.
Functional Scheme mergeSort_ind := Induction for mergeSort Sort Prop.
(* Check mergeSort_ind.
Check mergeSort_func. *)

(* Extraction mergeSort. *)
Eval compute in mergeSort nat leb (1 :: 3 :: 2 :: nil). 




(* Program Fixpoint interleave (A : Type) (l1 l2 : list A) {measure (length l1 + length l2)} : list A :=
match l1 with
| nil => l2
| cons h1 t1 => cons h1 (interleave A l2 t1)
end. *)

Check Fix. 

Hint Resolve split_wf1 split_wf2.

Definition mergeSort' : forall (A: Type), (A -> A -> bool) -> list A -> list A.
  refine 
    (fun A => fun le => 
      Fix (lengthOrder_wf A) (fun _ => list A) (fun (ls : list A)
          (mergeSort' : forall (ls' : list A), 
              lengthOrder A ls' ls -> list A) =>
            if le_lt_dec 2 (length ls)
            then 
              let lss := split' A ls in 
                merge' A le (mergeSort' (fst lss) _) (mergeSort' (snd lss) _ )
            else ls)); subst lss; auto.
Defined.

Require Import Init.Wf.
Check Init.Wf.Fix_F_inv.

Program Fixpoint once_or_twice (b : bool) {measure (if b then 1 else 2)} : bool :=
  match b with 
  | true => true
  | false => once_or_twice (negb b)
  end.

Check once_or_twice.

Eval compute in once_or_twice false.

Check Fix.

Eval compute in mergeSort' nat leb (1 :: 2 :: 3 :: nil).

Check Init.Wf.Fix_eq.

Check f_equal.
Theorem mergeSort_eq : forall A (le : A -> A -> bool) ls,
  mergeSort' A le ls = if le_lt_dec 2 (length ls)
    then let lss := split' A ls in
      merge' A le (mergeSort' A le (fst lss)) (mergeSort' A le (snd lss))
    else ls.
  intros. apply (Init.Wf.Fix_eq (lengthOrder_wf A) (fun _ => list A)). intros.
  destruct (le_lt_dec 2 (length x)).
  - simpl. f_equal; apply H.
  - auto. 
Qed.


Theorem mergeSort_eq_length : forall len (ls : list nat), (length ls <= len) -> length ls = length (mergeSort' nat leb ls). 
  intros.
  specialize (mergeSort_eq nat leb ls) as Heqmerge. intros. rewrite Heqmerge.
  induction len.
  - inversion H. admit.
  - simpl in *. admit.
Admitted. 

Check nat_ind.
Check option.

Definition computation A :=  
  { f : nat -> option A | 
    forall (n : nat) (v : A), 
      f n = Some v -> forall (n' : nat), n' >= n -> f n' = Some v}.

Definition runTo A (m : computation A) (n : nat) (v : A) := 
  proj1_sig m n = Some v.

Definition run A (m : computation A) (v : A) := 
  exists n, runTo A m n v.

Definition Bottom A : computation A.
Proof.
  intros. exists (fun _ : nat => None). intros. discriminate.
Defined.

Theorem run_Bottom A: forall v, ~ run A (Bottom A) v.
Proof.
  unfold not. intros. inversion H.
  inversion H0.  
Qed.

Definition Return A : A -> computation A.
  intro v. exists (fun _ : nat => Some v). intros. auto.
Defined.

Definition Bind A B : computation A -> (A -> computation B) -> computation B.
  intros m1 m2. 
  exists (fun n => let (f1, _) := m1 in 
            match f1 n with 
            | None => None 
            | Some v => let (f2, _) := m2 v in f2 n
            end    
  ). intros n v H n' Hngen'. destruct m1. destruct (x n) eqn:Hf1n. 
  - destruct (x n') eqn:Hf1n'. 
    + specialize (e n a Hf1n n' Hngen'). rewrite e in Hf1n'. inversion Hf1n'. subst. 
      destruct (m2 a0). specialize (e0 n v H n' Hngen'). auto. 
    + specialize (e n a Hf1n n' Hngen'). rewrite e in Hf1n'. discriminate.
  - discriminate.
Defined.

Definition meq A (m1 m2 : computation A) := forall n, proj1_sig m1 n = proj1_sig m2 n.

Notation "x <- m1 ; m2" :=
  (Bind _ _ m1 (fun x => m2)) (right associativity, at level 70).


Theorem left_identity : forall A B (a : A) (f : A -> computation B), 
  meq _ (Bind _ _ (Return _ a) f) (f a).
Proof.
  red (* OR unfold meq *). simpl. intros. destruct (f a). simpl. auto.
Qed.

Theorem right_identity : forall A (m : computation A), meq _ (Bind _ _ m (Return _)) m.
Proof.
  red. simpl. intros. destruct m. simpl. destruct (x n); auto.
Qed.

Theorem associativity : forall A B C (m : computation A) (g : A -> computation B) (h : B -> computation C),
  meq _ (Bind _ _ (Bind _ _ m g) h) (Bind _ _ m (fun x => Bind _ _ (g x) h)).
Proof.
  red. simpl. intros. destruct m. destruct (x n) eqn:Heqxn. 
  - destruct (g a); auto. 
  - auto. 
Qed.

Definition leq A (x y : option A) := forall v, x = Some v -> y = Some v.


Section Fix.

    Variable A B : Type.
    Variable f : (A -> computation B) -> (A -> computation B).

    Hypothesis f_continuous : forall n v v1 x,
        runTo _ (f v1 x) n v -> forall (v2 : A -> computation B), (forall x, leq _ (proj1_sig (v1 x) n) (proj1_sig (v2 x) n)) -> runTo _ (f v2 x) n v.

    Fixpoint Fix' (n : nat) (x : A) : computation B :=
      match n with 
      | O => Bottom _ 
      | S n' => f (Fix' n') x
      end.

    Lemma Fix'_ok : forall steps n x v, 
        proj1_sig (Fix' n x) steps = Some v ->
        forall n', n' >= n -> proj1_sig (Fix' n' x) steps = Some v .
    Proof.
      unfold runTo in *. induction n; simpl; intros.
      - discriminate.
      - inversion H0. 
        + simpl. assumption. 
        + simpl. apply f_continuous with (v1:=(Fix' n)). 
          * assumption. 
          * unfold leq. intros. apply IHn.
            -- assumption.
            -- omega.
    Qed.
    
    Definition Fix : A -> computation B.
      intro x. unfold runTo in *. 
      exists (fun n => proj1_sig (Fix' n x) n). intros. 
      apply Fix'_ok with (n:=n). destruct (Fix' n x). 
      - simpl. simpl in H. eapply e. apply H. assumption.
      - assumption. 
    Defined. 


    (* Understand this *)
    Theorem run_Fix : forall x v,
    run B (f Fix x) v -> run B (Fix x) v.
    Proof.
      unfold run. unfold runTo in *. intros. destruct H as [n' Happroxn']. exists (S n'). simpl. apply (proj2_sig (f (Fix' n') x)) with (n:=n').
      - apply f_continuous with (v1:=Fix). assumption. unfold leq. intros. assumption. 
      - omega. 
    Qed.


End Fix.


Definition mergeSort'' : forall A, (A -> A -> bool) -> list A -> computation (list A).
refine (
  fun A => fun le => Fix (list A) (list A) 
    (fun (mergeSort : list A -> computation (list A))
         (ls : list A) =>
      if le_lt_dec 2 (length ls)
      then 
        let lss := split' A ls in 
          ls1 <- mergeSort (fst lss);
          ls2 <- mergeSort (snd lss);
          Return _ (merge' A le ls1 ls2)
       else
        Return _ ls    
  ) _
). 
unfold runTo. unfold leq. intros. destruct (le_lt_dec 2 (length x)).
- simpl. simpl in H. 
  specialize (H0 (fst (split' A x))) as Hls1.
  destruct ((v2 (fst (split' A x)))). destruct ((v1 (fst (split' A x)))). simpl in *.
  destruct (x0 n). 
  + specialize (H0 (snd (split' A x))) as Hls2.
    destruct ((v2 (snd (split' A x)))). destruct ((v1 (snd (split' A x)))). simpl in *.
    destruct (x2 n).
    * destruct (x1 n). destruct (x3 n).
      -- specialize (Hls1 l2). assert (Some l2 = Some l2). {auto. } apply Hls1 in H1. inversion H1.
         specialize (Hls2 l3). assert (Some l3 = Some l3). {auto. } apply Hls2 in H2. inversion H2.
         assumption.
      -- discriminate.
      -- discriminate.
    * destruct (x1 n). destruct (x3 n).
      -- specialize (Hls2 l2). assert (Some l2 = Some l2). {auto. } apply Hls2 in H1. discriminate.
      -- discriminate. 
      -- discriminate.
  + destruct (x1 n).
    * specialize (Hls1 l0). assert (Some l0 = Some l0). {auto. } apply Hls1 in H1. discriminate.
    * discriminate.
- assumption.
Qed.




Check Fix.


Definition looper : bool -> computation unit.
  refine (
    Fix _ _ 
      (fun looper (b : bool) =>
        if b then Return unit tt else looper b) _ ).
    unfold runTo. unfold leq. intros. 
    specialize (H0 true) as Heqtt. specialize (H0 false) as Heqff.
    destruct x.
    - assumption. 
    - apply Heqff. assumption. 
  Defined.

Lemma test_looper : run _ (looper true) tt.
  exists 1; reflexivity.
Qed.


Fixpoint map A B (f : A -> computation B) (ls : list A) : computation (list B) :=
  match ls with
  | nil => Return _ nil
  | x :: ls' => Bind _ _ (f x) (fun x' =>
    Bind _ _ (map _ _ f ls') (fun ls'' =>
      Return _ (x' :: ls'')))
  end.


  

Theorem test_map : run _ (map _ _ (fun x => Return _ (S x)) (1 :: 2 :: 3 :: nil)) (2 :: 3 :: 4 :: nil).
exists 1; reflexivity.
Qed.

CoInductive thunk (A : Type) : Type :=
| Answer : A -> thunk A
| Think : thunk A -> thunk A.

CoFixpoint TBind A B (m1 : thunk A) (m2 : A -> thunk B) : thunk B :=
  match m1 with
  | Answer _ x => m2 x
  | Think _ m1' => Think _ (TBind _  _ m1' m2)
  end.

Definition frob A (m : thunk A) : thunk A := 
  match m with 
  | Answer _ x => Answer _ x
  | Think _ m1 => Think _ m1
  end.

Theorem frob_eq : forall A (m : thunk A), frob A m = m.
Proof.
  destruct m; auto.
Qed.

CoFixpoint fact (n acc : nat) : thunk nat :=
  match n with
  | O => Answer _ acc
  | S n' => Think _ (fact n' (S n' * acc))
  end. 

Inductive eval A : thunk A -> A -> Prop :=
| EvalAnswer : forall x, eval A (Answer _ x) x
| EvalThink : forall m x, eval A m x -> eval A (Think _ m) x.

Hint Rewrite frob_eq.

Lemma eval_frob : forall A (c : thunk A) x,
    eval A (frob A c) x -> eval A c x.
Proof.
  intros. rewrite frob_eq in H. auto.
Defined.

Theorem eval_fact : eval _ (fact 5 1) 120.
Proof.
  repeat (apply eval_frob; simpl; constructor).
Defined.

CoFixpoint fact' (n acc : nat) : thunk nat :=
  match n with
  | O => Answer _ acc
  | S n' => Think _ (fact' (S n') (S n' * acc))
  end. 

(* Theorem eval_fact' : eval _ (fact' 2 1) 2.
Proof.
  repeat (apply eval_frob; simpl; constructor).
Defined. *)

Notation "x <- m1 ; m2" :=
(TBind _ _  m1 (fun x => m2)) (right associativity, at level 70).

Definition curriedAdd (n : nat) := Answer (nat -> thunk nat) 
    (fun m : nat => Answer _ (n + m)).

Definition testCurriedAdd := TBind _  _ (curriedAdd 2) (fun f => f 3).

Eval compute in testCurriedAdd.

(* CoFixpoint mergeSort''' A (le : A -> A -> bool) (ls : list A) : thunk (list A) :=
  if le_lt_dec 2 (length ls)
  then 
    let lss := split' _ ls in
      ls1 <- mergeSort''' _ le (fst lss);
      ls2 <- mergeSort''' _ le (snd lss);
      Answer _ (merge' _ le ls1 ls2 )
  else Answer _ ls. *)

(* CoFixpoint fib (n : nat) : thunk nat :=
match n with
| 0 => Answer _ 1
| 1 => Answer _ 1
| _ => n1 <- fib (pred n);
       n2 <- fib (pred (pred n));
       Answer _ (n1 + n2 )
end. *)

CoInductive comp (A : Type) : Type :=
| Ret : A -> comp A 
| Bnd : forall B, comp B -> (B -> comp A) -> comp A.

Inductive exec A : comp A -> A -> Prop :=
| ExecRet : forall x, exec A (Ret _ x) x
| ExecBnd : forall B (c : comp B) (f : B -> comp A) x1 x2, exec B c x1 -> exec A (f x1 ) x2
-> exec A (Bnd _ _ c f ) x2.

Definition frob' A (c : comp A) :=
  match c with
  | Ret _ x => Ret _ x
  | Bnd _ _ c' f => Bnd _ _ c' f
  end.

Lemma exec_frob : forall A (c : comp A) x,
    exec _ (frob' _ c) x -> exec _ c x.
  destruct c; crush.
Qed.

Notation "x <- m1 ; m2" := (Bnd _ _ m1 (fun x => m2)) (right associativity, at level 70).

CoFixpoint mergeSort''' A (le : A -> A -> bool) (ls : list A) : comp (list A) :=
  if le_lt_dec 2 (length ls)
  then let lss := split' _ ls in
    ls1 <- mergeSort''' _ le (fst lss);
    ls2 <- mergeSort''' _ le (snd lss);
    Ret _ (merge' _ le ls1 ls2 )
  else Ret _ ls.

Lemma test_mergeSort''' : exec _ (mergeSort''' _ leb (1 :: 2 :: 36 :: 8 :: 19 :: nil)) (1 :: 2 :: 8 :: 19 :: 36 :: nil).
repeat (apply exec_frob; simpl; econstructor).
Qed.

(* Definition curriedAdd (n : nat) := Ret (nat -> comp nat) (fun m : nat => Ret _ (n + m)). *)
Fixpoint map' A B (f : A -> thunk B) (ls : list A) : thunk (list B) :=
  match ls with
  | nil => Answer _ nil
  | x :: ls' => TBind _ _ (f x) (fun x' =>
    TBind _ _ (map' _ _ f ls') (fun ls'' =>
      Answer _ (x' :: ls'')))
  end.


Theorem eval_map' : eval _ (map' _ _ (fun x => Answer _ (S x)) (1 :: 2 :: 3 :: nil)) (2 :: 3 :: 4 :: nil).
Proof.
  (* once is enough *) apply eval_frob. simpl. constructor.
Defined.

Check curriedAdd.



