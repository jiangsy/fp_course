(* coq 8.14 *)
Require Import Coq.Lists.List.
Require Import Arith List Lia Program.

Require Import Cpdt.CpdtTactics Cpdt.MoreSpecif.

Set Implicit Arguments.


Section ilist.

  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 with
    | Nil => ls2
    | Cons x ls1' => Cons x (app ls1' ls2)
    end.

  Fixpoint app' n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
    | Nil => ls2
    | Cons x ls1' => Cons x (app' ls1' ls2)
    end.

  Fixpoint inject (ls : list A) : ilist (length ls) :=
    match ls with
    | nil => Nil
    | h :: t => Cons h (inject t)
    end.

  Fixpoint unject n (ls : ilist n) : list A :=
    match ls with
    | Nil => nil
    | Cons h t => h :: unject t
    end.

  Theorem inject_inverse : forall ls, unject (inject ls) = ls.
  Proof.
    induction ls; simpl; try rewrite IHls; auto.
  Qed.

  Definition hd n (ls : ilist (S n)) : A :=
    match ls with
    | Cons h _ => h
    end.

  Print hd.
  (* match ls in (ilist n0) return match n0 with
                            | 0 => IDProp
                            | S _ => A
                            end with
  | Nil => idProp
  | @Cons n0 h _ => h
  end *)
End ilist.

Inductive type : Set :=
| Nat : type
| Bool : type
| Prod : type -> type -> type.

Inductive exp : type -> Set :=
| NConst : nat -> exp Nat
| Plus : exp Nat -> exp Nat -> exp Nat
| Eq : exp Nat -> exp Nat -> exp Bool

| BConst : bool -> exp Bool
| And : exp Bool -> exp Bool -> exp Bool
| If : forall t, exp Bool -> exp t -> exp t -> exp t

| Pair : forall t1 t2, exp t1 -> exp t2 -> exp (Prod t1 t2)
| Fst : forall t1 t2, exp (Prod t1 t2) -> exp t1
| Snd : forall t1 t2, exp (Prod t1 t2) -> exp t2
.

Fixpoint typeDenote (t : type) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  | Prod t1 t2 => typeDenote t1 * typeDenote t2
  end.

Eval cbv in typeDenote (Prod Nat Nat).

Fixpoint expDenote t (e : exp t) : typeDenote t :=
  match e with
  | NConst n => n
  | Plus e1 e2 => expDenote e1 + expDenote e2
  | Eq e1 e2 => if eq_nat_dec (expDenote e1) (expDenote e2) then true else false

  | BConst b => b
  | And e1 e2 => andb (expDenote e1) (expDenote e2)
  | If e' e1 e2 => if expDenote e' then expDenote e1 else expDenote e2

  | Pair e1 e2 => (expDenote e1, expDenote e2)
  | Fst e' => fst (expDenote e')
  | Snd e' => snd (expDenote e')
  end.

Fail Definition pairOut t1 t2 (e : exp (Prod t1 t2)) : exp t1 * exp t2 :=
  match e with
  | Pair e1 e2 => (e1, e2)
  end.

Definition pairOutType (t : type) := option (
  match t with
  | Prod t1 t2 => exp t1 * exp t2
  | _ => unit
  end
).

Definition pairOut t (e : exp t) :=
  match e in (exp t) return (pairOutType t) with
  | Pair e1 e2 => Some (e1, e2)
  | _ => None
  end.

Fixpoint cfold t (e : exp t) : exp t :=
  match e with
  | NConst n => NConst n
  | Plus e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
      | NConst n1, NConst n2 => NConst (n1 + n2)
      | _, _ => Plus e1' e2'
      end
  | Eq e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
      | NConst n1, NConst n2 => BConst (if eq_nat_dec n1 n2 then true else false)
      | _, _ => Eq e1' e2'
      end

  | BConst b => BConst b
  | And e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
      | BConst b1, BConst b2 => BConst (andb b1 b2)
      | _, _ => And e1' e2'
      end
  | If e e1 e2 =>
      let e' := cfold e in
      match e' with
      | BConst true => cfold e1
      | BConst false => cfold e2
      | _ => If e' (cfold e1) (cfold e2)
      end

  | Pair e1 e2 => Pair (cfold e1) (cfold e2)
  | Fst e =>
      let e' := cfold e in
      match pairOut e' with
      | Some p => fst p
      | _ => Fst e'
      end
  | Snd e =>
      let e' := cfold e in
      match pairOut e' with
      | Some p => snd p
      | _ => Snd e'
      end
  end.

Theorem cfold_correct : forall t (e : exp t), expDenote e = expDenote (cfold e).
Proof.
  induction e; crush;
  repeat (match goal with
  | [ |- context[match cfold ?E with NConst _ => _ | _ => _ end] ] => dep_destruct (cfold E)
  | [ |- context[match pairOut (cfold ?E) with Some _ => _ | None => _ end] ] =>
  dep_destruct (cfold E)
  | [ |- (if ?E then _ else _) = _ ] => destruct E
  end; crush).
Qed.

Inductive color : Set := Red | Black.

Inductive rbtree : color -> nat -> Set :=
| Leaf : rbtree Black 0
| RedNode : forall n, rbtree Black n -> nat -> rbtree Black n -> rbtree Red n
| BlackNode : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rbtree Black (S n).

Require Import Max Min.

Section depth.

  Fixpoint depth c n f (t : rbtree c n) : nat :=
    match t with
    | Leaf => 0
    | RedNode t1 _ t2 => S (f (depth f t1) (depth f t2))
    | BlackNode t1 _ t2 => S (f (depth f t1) (depth f t2))
    end.

  Theorem depth_min : forall c n (t : rbtree c n), depth min t >= n.
  Proof.
    induction t; simpl; lia.
  Qed.

  Theorem depth_max : forall c n (t : rbtree c n), depth max t <= 2 * n + 1.
    induction t; simpl; try lia.
  Abort.

  Theorem depth_max' : forall c n (t : rbtree c n), match c with
                                                    | Red => depth max t <= 2 * n + 1
                                                    | Black => depth max t <= 2 * n
                                                    end.
  Proof.
    induction t; simpl; try lia.
    destruct c1; destruct c2; destruct (max_dec (depth max t1) (depth max t2)); lia.
  Qed.

  Theorem depth_max : forall c n (t : rbtree c n), depth max t <= 2 * n + 1.
    intros.
    specialize (depth_max' t).
    intros.
    destruct c; lia.
  Qed.

End depth.


Theorem balanced : forall c n (t : rbtree c n), 2 * depth min t + 1 >= depth max t.
Proof.
  intros.
  specialize (depth_min t). specialize (depth_max t). intros.
  lia.
Qed.


Inductive rtree : nat -> Set :=
| RedNode' : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rtree n.


Section present.
  Variable x : nat.

  Fixpoint present c n (t : rbtree c n) : Prop :=
    match t with
    | Leaf => False
    | RedNode a y b => present a \/ x = y \/ present b
    | BlackNode a y b => present a \/ x = y \/ present b
    end.

  Definition rpresent n (t : rtree n) : Prop :=
    match t with
    | RedNode' a y b => present a \/ x = y \/ present b
    end.
End present.

Notation "{< x >}" := (existT _ _ x).

Definition balance1 n (a : rtree n) (data : nat) c2 :=
  match a in rtree n return rbtree c2 n
    -> { c : color & rbtree c (S n) } with
    | @RedNode' _ c0 _ t1 y t2 =>
      match t1 in rbtree c n return rbtree c0 n -> rbtree c2 n
        -> { c : color & rbtree c (S n) } with
        | RedNode a x b => fun c d =>
          {<RedNode (BlackNode a x b) y (BlackNode c data d)>}
        | t1' => fun t2 =>
          match t2 in rbtree c n return rbtree Black n -> rbtree c2 n
            -> { c : color & rbtree c (S n) } with
            | RedNode b x c => fun a d =>
              {<RedNode (BlackNode a y b) x (BlackNode c data d)>}
            | b => fun a t => {<BlackNode (RedNode a y b) data t>}
          end t1'
      end t2
  end.

Definition balance2 n (a : rtree n) (data : nat) c2 :=
  match a in rtree n return rbtree c2 n
    -> { c : color & rbtree c (S n) } with
    | @RedNode' _ c0 _ t1 z t2 =>
      match t1 in rbtree c n return rbtree c0 n -> rbtree c2 n
        -> { c : color & rbtree c (S n) } with
        | RedNode b y c => fun d a =>
          {<RedNode (BlackNode a data b) y (BlackNode c z d)>}
        | t1' => fun t2 =>
          match t2 in rbtree c n return rbtree Black n -> rbtree c2 n
            -> { c : color & rbtree c (S n) } with
            | RedNode c z' d => fun b a =>
              {<RedNode (BlackNode a data b) z (BlackNode c z' d)>}
            | b => fun a t => {<BlackNode t data (RedNode a z b)>}
          end t1'
      end t2
  end.

Section insert.
  Variable x : nat.

  Definition insResult c n := 
    match c with
    | Red => rtree n
    | Black => {c' : color & rbtree c' n}
    end.

  Fail Fixpoint ins1 c n (t : rbtree c n) : insResult c n :=
    match t in (rbtree c n) return insResult c n with
    | Leaf => {< RedNode Leaf x Leaf >}
    | RedNode a y b => 
        if le_lt_dec x y
          then RedNode' (projT2 (ins1 a)) y b
          else RedNode' a y (projT2 (ins1 b))
    | @BlackNode c1 c2 _ a y b =>
        if le_lt_dec x y 
          then 
            match c1 with
            | Red => balance1 (ins1 a) y b
            | _ => {<BlackNode (projT2 (ins1 a)) y b>}
            end
          else 
            match c2 with
            | Red => balance2 (ins1 a) y a
            | _ => {<BlackNode a y (projT2 (ins1 b))>}
            end 
    end.  

  Fixpoint ins2 c n (t : rbtree c n) : insResult c n :=
    match t in (rbtree c n) return insResult c n with
    | Leaf => {< RedNode Leaf x Leaf >}
    | RedNode a y b => 
        if le_lt_dec x y
          then RedNode' (projT2 (ins2 a)) y b
          else RedNode' a y (projT2 (ins2 b))
    | @BlackNode c1 c2 _ a y b =>
        if le_lt_dec x y 
          then 
            match c1 return rbtree c1 _ -> _ with
            | Red => fun a => balance1 (ins2 a) y b
            | _ => fun a => {<BlackNode (projT2 (ins2 a)) y b>}
            end a
          else 
            match c2 return rbtree c2 _ -> _ with
            | Red => fun b => balance2 (ins2 b) y a
            | _ => fun b => {<BlackNode a y (projT2 (ins2 b))>}
            end b
    end.  

  Fixpoint ins c n (t : rbtree c n) : insResult c n :=
    match t in (rbtree c n) return insResult c n with
    | Leaf => {< RedNode Leaf x Leaf >}
    | RedNode a y b => 
        if le_lt_dec x y
          then RedNode' (projT2 (ins a)) y b
          else RedNode' a y (projT2 (ins b))
    | @BlackNode c1 c2 _ a y b =>
        if le_lt_dec x y 
          then 
            match c1 return insResult c1 _ -> _ with
            | Red => fun ins_a => balance1 ins_a y b
            | _ => fun ins_a => {<BlackNode (projT2 ins_a) y b>}
            end (ins a)
          else 
            match c2 return insResult c2 _ -> _ with
            | Red => fun ins_b => balance2 ins_b y a
            | _ => fun ins_b => {<BlackNode a y (projT2 ins_b)>}
            end (ins b)
    end.  

  Definition insertResult c n := 
    match c with 
    | Red => rbtree Black (S n)
    | Black => {c' : color & rbtree c' n}
    end.

  Definition makeRbtree c n : insResult c n -> insertResult c n :=
    match c with
    | Red => fun r =>
      match r with
      | RedNode' a x b => BlackNode a x b
      end
    | Black => fun r => r
    end.

  Arguments makeRbtree [c n] _.

  Definition insert c n (t : rbtree c n) : insertResult c n :=
    makeRbtree (ins t).

  
  Section present.
    Variable z : nat.

    Lemma present_balance1 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n),
        present z (projT2 (balance1 a y b)) <->
        rpresent z a \/ z = y \/ present z b.
      destruct a. intros. split; intros.
      - destruct r; dep_destruct r0; simpl in *; crush.
      - destruct r; dep_destruct r0; simpl in *; crush.
    Qed.

    Lemma present_balance2 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n),
        present z (projT2 (balance2 a y b)) <->
        rpresent z a \/ z = y \/ present z b.
      destruct a. intros. split; intros.
      - destruct r; dep_destruct r0; simpl in *; crush.
      - destruct r; dep_destruct r0; simpl in *; crush.
    Qed.

    Definition present_insResult c n := 
      match c return (rbtree c n -> insResult c n -> Prop) with
      | Red => fun t r => rpresent z r <-> z = x \/ present z t
      | Black => fun t r => present z (projT2 r) <-> z = x \/ present z t
      end.
    
    Theorem present_ins : forall c n (t : rbtree c n),
      present_insResult t (ins t).
    Proof.
      induction t; crush.
      1-12: try destruct (le_lt_dec x n0); crush.
      all: try destruct (le_lt_dec x n0).
      - destruct c1; crush. simpl in H.
        specialize (present_balance1 (ins t1) n0 t2). intros.
        crush.
      - destruct c2; crush. simpl in H.
        specialize (present_balance2 (ins t2) n0 t1). intros.
        crush.
      - destruct c1; crush.
        1-2: specialize (present_balance1 (ins t1) n0 t2); crush.
        + rewrite H in *. clear H. crush.
        + rewrite H0 in H2. crush.
      - destruct c1; destruct c2. 
        + specialize (present_balance2 (ins t2) n0 t1). crush.
        + crush.
        + specialize (present_balance2 (ins t2) n0 t1); crush.
        + crush.
      - destruct c1; crush.
        all : specialize (present_balance1 (ins t1) n0 t2); crush.
      - destruct c2; crush.
        specialize (present_balance2 (ins t2) n0 t1). crush.
      - destruct (le_lt_dec x z). 
        + destruct c1. 
          * specialize (present_balance1 (ins t1) z t2); crush. 
          * crush.
        + destruct c2.  
          * specialize (present_balance2 (ins t2) z t1); crush. 
          * crush.
      - destruct c1.
        + specialize (present_balance1 (ins t1) n0 t2); crush.
        + crush.
      - destruct c2.  
        + specialize (present_balance2 (ins t2) n0 t1); crush. 
        + crush.
    Qed.
    
    Theorem present_insert_Red : forall n (t : rbtree Red n),
      present z (insert t) <-> (z = x \/ present z t).
    Proof.
      unfold insert. intros. inversion t.
      generalize (present_ins t). destruct (ins t); simpl.
      tauto.      
    Qed.

    Theorem present_insert_Black : forall n (t : rbtree Black n),
      present z (projT2 (insert t)) <-> (z = x \/ present z t).
    Proof.
      unfold insert. intros. inversion t;
      generalize (present_ins t); destruct (ins t); simpl;
      tauto.      
    Qed.
    
  End present.
End insert.

Require Import Ascii String.
Open Scope string_scope.

Section star.
  Variable P : string -> Prop.

  Inductive star : string -> Prop :=
  | Empty : star ""
  | Iter : forall s1 s2,
      P s1 -> star s2 -> star (s1 ++ s2).
  
End star.

Inductive regexp : (string -> Prop) -> Type :=
| Char : forall ch : ascii,
    regexp (fun s => s = String ch "")
| Concat : forall (P1 P2 : string -> Prop) (r1 : regexp P1) (r2 : regexp P2), 
    regexp (fun s => exists s1, exists s2, s = s1 ++ s2 /\ P1 s1 /\ P2 s2)
| Or : forall P1 P2 (r1 : regexp P1) (r2 : regexp P2), regexp (fun s => P1 s \/ P2 s)
| Star : forall P (r : regexp P),
    regexp (star P)
.

Local Open Scope specif_scope.
Delimit Scope specif_scope with specif.

Notation "'Yes'" := (left _ _) : specif_scope.
Notation "'No'" := (right _ _) : specif_scope.
Notation "'Reduce' x" := (if x then Yes else No) (at level 50) : specif_scope.

Ltac split_all := repeat (try split).

Open Scope specif_scope.

Lemma length_emp : length "" <= 0.
  crush.
Qed.

Lemma append_emp : forall s, s = "" ++ s.
  crush.
Qed.

Ltac substring :=
  crush;
  repeat match goal with
          | [ |- context[match ?N with O => _ | S _ => _ end] ] => destruct N; crush
        end.



Lemma substring_le : forall s n m,
    length (substring n m s) <= m.
  induction s; substring.
Qed.

Lemma substring_all : forall s,
    substring 0 (length s) s = s.
  induction s; substring.
Qed.

Lemma substring_none : forall s n,
  substring n 0 s = "".
  induction s; substring.
Qed.

Hint Rewrite substring_all substring_none.

Lemma substring_split : forall s m,
  substring 0 m s ++ substring m (length s - m) s = s.
  induction s; substring.
Qed.

Lemma length_app1 : forall s1 s2,
  length s1 <= length (s1 ++ s2).
  induction s1; crush.
Qed.

#[local]
Hint Resolve length_emp append_emp substring_le substring_split length_app1 : core.

Lemma substring_app_fst : forall s2 s1 n,
  length s1 = n
  -> substring 0 n (s1 ++ s2) = s1.
  induction s1; crush.
Qed.

Lemma substring_app_snd : forall s2 s1 n,
  length s1 = n
  -> substring n (length (s1 ++ s2) - n) (s1 ++ s2) = s2.
  Hint Rewrite <- minus_n_O.
  induction s1; crush.
Qed.

Lemma app_empty_end : forall s, s ++ "" = s.
  induction s; crush.
Qed.

Section split.
  Variables P1 P2 : string -> Prop.
  Variable P1_dec : forall s, {P1 s} + {~ P1 s}.
  Variable P2_dec : forall s, {P2 s} + {~ P2 s}.

  Variable s : string.

  Definition split'2 : forall n : nat, n <= length s -> {exists s1, exists s2, length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2} + {forall s1, forall s2, length s1 <= n -> s1 ++ s2 = s -> ~ P1 s1 \/ ~ P2 s2}.
    refine (fix F (n : nat) : n <= length s ->
    {exists s1, exists s2, length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2} + 
    {forall s1, forall s2, length s1 <= n -> s1 ++ s2 = s -> ~ P1 s1 \/ ~ P2 s2} := 
    match n with
          | O => fun _ => Reduce (P1_dec "" && P2_dec s)
          | S n' => fun _ => _
        end).
  Fail Defined.
  Admitted.


  Definition split' : forall n : 
      nat, n <= length s -> 
      {exists s1, exists s2, length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2} +
      {forall s1, forall s2, length s1 <= n -> s1 ++ s2 = s -> ~ P1 s1 \/ ~ P2 s2}.
    refine (fix F (n : nat) : n <= length s ->
    {exists s1, exists s2, length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2} + 
    {forall s1, forall s2, length s1 <= n -> s1 ++ s2 = s -> ~ P1 s1 \/ ~ P2 s2} := 
    match n with
          | O => fun _ => Reduce (P1_dec "" && P2_dec s)
          | S n' => fun _ => (P1_dec (substring 0 (S n') s)
              && P2_dec (substring (S n') (length s - S n') s))
            || F n' _
        end).
    - exists "", s; auto.
    - intros. inversion o; destruct s1.
      + left. auto.
      + inversion H.
      + right. simpl in H0. rewrite H0. auto.
      + inversion H.
    - inversion a. exists (substring 0 (S n') s), (substring (S n') (length s - S n') s).
      all : split_all; auto.
    - lia.
    - destruct e as [s1 [s2 [Hlens1 [Heqs [Hp1s1 Hp2s2]]]]].
      exists s1, s2. all : split_all; auto.
    - intros. inversion H.
      + specialize (substring_app_fst s2 s1 H2).
        specialize (substring_app_snd s2 s1 H2).
        intros.
        rewrite H0 in H1, H3. rewrite H1 in o. rewrite H3 in o.
        auto.
      + apply o0; auto.
  Qed.

  Definition split : {exists s1, exists s2, s = s1 ++ s2 /\ P1 s1 /\ P2 s2 } +
                     {forall s1 s2, s = s1 ++ s2 -> ~ P1 s1 \/ ~ P2 s2 }.
  refine (Reduce (split' (n := length s)_  )); crush; eauto.
  Defined.
End split.


Lemma minus_minus : forall n m1 m2,
  m1 + m2 <= n
  -> n - m1 - m2 = n - (m1 + m2).
  intros; lia.
Qed.

Section dec_star.
  Variable P : string -> Prop.
  Variable P_dec : forall s, {P s} + {~ P s}.

  Hint Constructors star : core.

  Lemma star_empty : forall s,
    length s = 0
    -> star P s.
    destruct s; auto. intros. inversion H.
  Qed.

  Lemma star_singleton : forall s, P s -> star P s.
    intros. rewrite <- (app_empty_end s).
    auto. 
  Qed.

  Hint Resolve star_empty star_singleton : core.

  Lemma star_app : forall s n m,
    P (substring n m s)
    -> star P (substring (n + m) (length s - (n + m)) s)
    -> star P (substring n (length s - n) s).
  Proof.
    induction s.
    - crush. destruct n; auto.
    - simpl. intros. destruct n; destruct m; crush.
      + rewrite <- (substring_split s m).
        assert (String a (substring 0 m s ++ substring m (length s - m) s) = String a (substring 0 m s) ++ substring m (length s - m) s). { crush. }
        rewrite H1. constructor; auto.
      + rewrite append_emp. constructor; auto.
        rewrite plus_0_r in H0. auto.
      + eapply IHs; eauto.
  Qed.

  Lemma star_inv : forall s,
    star P s
    -> s = ""
    \/ exists i, i < length s
      /\ P (substring 0 (S i) s)
      /\ star P (substring (S i) (length s - S i) s).
  Proof. 
    intros.
    induction H.
    - auto.
    - destruct s1; destruct s2; auto.
      + right. exists (length s1). simpl. crush.
        * rewrite app_empty_end. rewrite substring_all. auto.
        * rewrite app_empty_end. replace (length s1 - length s1) with 0. rewrite substring_none.  auto. lia.
      + right. exists (length s1). simpl. crush.
        * rewrite substring_app_fst; auto.
        * rewrite substring_app_snd; auto.
  Qed.

  Lemma substring_stack : forall s n2 m1 m2,
    m1 <= m2
    -> substring 0 m1 (substring n2 m2 s)
    = substring n2 m1 s.
  Proof.
    induction s; crush; destruct n2; destruct m1; destruct m2; crush.
  Qed.

  Lemma substring_stack' : forall s n1 n2 m1 m2,
    n1 + m1 <= m2
    -> substring n1 m1 (substring n2 m2 s)
    = substring (n1 + n2) m1 s.
    induction s; crush; destruct n2; destruct m2; destruct m1; destruct n1; crush.
    replace (S (n1+n2)) with (n1 + S n2). auto. lia.
  Qed.

  Lemma substring_suffix : forall s n,
    n <= length s
    -> length (substring n (length s - n) s) = length s - n.
    induction s; crush; destruct n; auto.
    - rewrite substring_all. auto.
    - apply IHs. lia.
  Qed.

  Lemma substring_suffix_emp' : forall s n m,
    substring n (S m) s = ""
    -> n >= length s.
    induction s; crush.
      destruct n; crush.
      assert (n >= (length s) -> S n >= S (length s)). { lia. }
      apply H0. eauto.
  Qed.

  Lemma substring_suffix_emp : forall s n m,
    substring n m s = ""
    -> m > 0
    -> n >= length s.
    destruct m as [ | m]; [crush | intros; apply substring_suffix_emp' with m; assumption].
  Qed.
  
  Variable s : string.

  Lemma star_substring_inv : forall n,
    n <= length s
    -> star P (substring n (length s - n) s)
    -> substring n (length s - n) s = ""
    \/ exists l, l < length s - n
      /\ P (substring n (S l) s)
      /\ star P (substring (n + S l) (length s - (n + S l)) s).
  Proof.
    Hint Rewrite plus_n_Sm.
    intros.
    generalize (star_inv H0). crush.
    right. exists x.
    rewrite (substring_suffix s H) in H2, H4.
    assert (S x <= length s - n). { lia. }
    rewrite (substring_stack s n H3) in H1.
    assert (S x + (length s - n - S x) <= length s - n). { lia. }
    rewrite (substring_stack' s (S x) n (length s - n - S x) H5) in H4.
    assert (length s - n - S x = length s - (n + S x)). { lia. }
    assert (S x + n = n + S x). { lia. }
    rewrite <- H6. rewrite <- H7.    
    crush.
  Qed.

  Section dec_star''.

    Notation "'Yes'" := (left _ _) : specif_scope.
    Notation "'No'" := (right _ _) : specif_scope.
    Notation "'Reduce' x" := (if x then Yes else No) (at level 50) : specif_scope.
    Variable n : nat.

    Variable P' : string -> Prop.
    Variable P'_dec : forall n', n' > n 
      -> {P' (substring n' (length s - n') s)} + {~ P' (substring n' (length s - n') s)}.

    Definition dec_star'' : forall l : nat,
      {exists l', S l' <= l /\ P (substring n (S l') s) /\ P' (substring (n + S l') (length s - (n + S l')) s)} + 
      {forall l', S l' <= l -> ~P (substring n (S l') s) \/ ~ P' (substring (n + S l') (length s - (n + S l')) s)}.
    Proof.
      refine (fix F (l : nat) : 
        {exists l', S l' <= l /\ P (substring n (S l') s) /\ P' (substring (n + S l') (length s - (n + S l')) s)} + 
        {forall l', S l' <= l -> ~P (substring n (S l') s) \/ ~ P' (substring (n + S l') (length s - (n + S l')) s)} :=
        match l with 
        | O => _ 
        | S l' => (P_dec (substring n (S l') s) && P'_dec (n' := n + S l') _) || F l'
        end); clear F; crush; eauto.
        - right. intros. inversion H.
        - inversion H0.
          + left. auto.
          + apply o0. auto.
        - inversion H0.
          + right. auto.
          + apply o0. auto.
    Defined. 

    End dec_star''.

  Lemma star_length_contra : forall n,
    length s > n
    -> n >= length s
    -> False.
    crush.
  Qed.

  Lemma star_length_flip : forall n n',
    length s - n <= S n'
    -> length s > n
    -> length s - n > 0.
    crush.
  Qed.

    (* Hint Resolve star_length_contra star_length_flip substring_suffix_emp. *)

  Definition dec_star' : forall n n', length s - n' <= n ->
    {star P (substring n' (length s - n') s)} +
    {~ star P (substring n' (length s - n') s)}.
    refine(
      fix F (n n' : nat) : length s - n' <= n ->
        {star P (substring n' (length s - n') s)} +
        {~ star P (substring n' (length s - n') s)} :=
      match n with 
      | O => fun _ => Yes
      | S n'' => fun _ => 
        le_gt_dec (length s) n' || 
        dec_star'' (n:=n') (star P) (fun n0 _ => Reduce (F n'' n0 _)) (length s - n')
      end); clear F; crush; eauto.
      - assert (length s - n' = 0). { lia. } rewrite H. rewrite substring_none. auto.
      - assert (length s - n' = 0). { lia. } rewrite H. rewrite substring_none. auto.
      - apply star_substring_inv in H2; crush; eauto. 
        + eapply star_app; eauto. rewrite H1. auto. 
        + eapply star_app; eauto. eapply star_app; eauto.
      - apply star_substring_inv in H; crush; eauto.
        + specialize (substring_suffix_emp s n' H0 (star_length_flip l g)). intros.
          specialize (star_length_contra g H). auto.
        + assert (S x <= length s - n'). { lia. } specialize (o x H1). crush. 
  Defined.

  Definition dec_star : {star P s} + {~ star P s}.
    refine (Reduce (dec_star' (n:=length s) 0 _)).
    - lia.
    - assert ((length s - 0) = length s). { lia. }
      rewrite H in s0. rewrite substring_all in s0. auto.
    - assert ((length s - 0) = length s). { lia. }
      rewrite H in n. rewrite substring_all in n. auto.
  Defined.
    
End dec_star.

Definition matches : forall P (r : regexp P) s, {P s} + {~ P s}.
  refine (fix F P (r : regexp P) s: {P s} + {~ P s} :=
    match r with 
    | Char ch => string_dec s (String ch "")
    | Concat r1 r2 => Reduce (split _ _ (F _ r1) (F _ r2) s)
    | Or r1 r2 => F _ r1 s || F _ r2 s
    | Star r => dec_star _ _ _
    end); crush.
    - specialize (o x x0 (eq_refl (x ++ x0))); crush.
  Defined.

Example a_star := Star (Char "a"%char).
Eval hnf in matches a_star "".
Eval hnf in matches a_star "a".
Eval hnf in matches a_star "b".
Eval hnf in matches a_star "aa".