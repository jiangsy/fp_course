(** * IndProp: Inductively Defined Propositions *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lia.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.  In this chapter, we bring yet another new tool
    into the mix: _inductively defined propositions_.

    _Note_: For the sake of simplicity, most of this chapter uses an
    inductive definition of "evenness" as a running example.  This is
    arguably a bit confusing, since we already have a perfectly good
    way of defining evenness as a proposition ("[n] is even if it is
    equal to the result of doubling some number").  Rest assured that
    we will see many more compelling examples of inductively defined
    propositions toward the end of this chapter and in future
    chapters. *)

(** We've already seen two ways of stating a proposition that a number
    [n] is even: We can say

      (1) [even n = true], or

      (2) [exists k, n = double k].

    A third possibility that we'll explore here is to say that [n] is
    even if we can _establish_ its evenness from the following rules:

       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even. *)

(** To illustrate how this new definition of evenness works,
    let's imagine using it to show that [4] is even. By rule [ev_SS],
    it suffices to show that [2] is even. This, in turn, is again
    guaranteed by rule [ev_SS], as long as we can show that [0] is
    even. But this last fact follows directly from the [ev_0] rule. *)

(** We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation.  (We'll
    use [ev] for the name of this property, since [even] is already
    used.)

                              ------------             (ev_0)
                                 ev 0

                                 ev n
                            ----------------          (ev_SS)
                             ev (S (S n))
*)

(** Each of the textual rules that we started with is
    reformatted here as an inference rule; the intended reading is
    that, if the _premises_ above the line all hold, then the
    _conclusion_ below the line follows.  For example, the rule
    [ev_SS] says that, if [n] satisfies [ev], then [S (S n)] also
    does.  If a rule has no premises above the line, then its
    conclusion holds unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even:

                             --------  (ev_0)
                              ev 0
                             -------- (ev_SS)
                              ev 2
                             -------- (ev_SS)
                              ev 4
*)

(** (Why call this a "tree", rather than a "stack", for example?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this shortly.) *)

(* ================================================================= *)
(** ** Inductive Definition of Evenness *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** This definition is interestingly different from previous uses of
    [Inductive].  For one thing, we are defining not a [Type] (like
    [nat]) or a function yielding a [Type] (like [list]), but rather a
    function from [nat] to [Prop] -- that is, a property of numbers.
    But what is really new is that, because the [nat] argument of
    [ev] appears to the _right_ of the colon on the first line, it
    is allowed to take different values in the types of different
    constructors: [0] in the type of [ev_0] and [S (S n)] in the type
    of [ev_SS].  Accordingly, the type of each constructor must be
    specified explicitly (after a colon), and each constructor's type
    must have the form [ev n] for some natural number [n].

    In contrast, recall the definition of [list]:

    Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).

   This definition introduces the [X] parameter _globally_, to the
   _left_ of the colon, forcing the result of [nil] and [cons] to be
   the same (i.e., [list X]).  Had we tried to bring [nat] to the left
   of the colon in defining [ev], we would have seen an error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]"
        as 1st argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type constructor
    on the left of the colon is called a "parameter", whereas an
    argument on the right is called an "index" or "annotation."

    For example, in [Inductive list (X : Type) := ...], the [X] is a
    parameter; in [Inductive ev : nat -> Prop := ...], the unnamed
    [nat] argument is an index. *)

(** We can think of this as defining a Coq property [ev : nat ->
    Prop], together with "evidence constructors" [ev_0 : ev 0]
    and [ev_SS : forall n, ev n -> ev (S (S n))]. *)

(** These evidence constructors can be thought of as "primitive
    evidence of evenness", and they can be used just like proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    constructor names to obtain evidence for [ev] of particular
    numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax to combine several
    constructors: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** In this way, we can also prove theorems that have hypotheses
    involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double) *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros. induction n.
  - simpl. constructor.
  - simpl. constructor. assumption.
Qed.
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _destruct_ such evidence, which amounts to reasoning about how it
    could have been built.

    Introducing [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is [ev], but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are [ev]. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must be one of two things:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [ev n] much as we do inductively defined
    data structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [ev n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence for [ev n] _directly_. As
    a tool, we can prove our characterization of evidence for
    [ev n], using [destruct]. *)

Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** Facts like this are often called "inversion lemmas" because they
    allow us to "invert" some given information to reason about all
    the different ways it could have been derived.

    Here, there are two ways to prove that a number is [ev], and
    the inversion lemma makes this explicit. *)

(** The following theorem can easily be proved using [destruct] on
    evidence. *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** However, this variation cannot easily be handled with just
    [destruct]. *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
(** Intuitively, we know that evidence for the hypothesis cannot
    consist just of the [ev_0] constructor, since [O] and [S] are
    different constructors of the type [nat]; hence, [ev_SS] is the
    only case that applies.  Unfortunately, [destruct] is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.  *)
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** What happened, exactly?  Calling [destruct] has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of [ev_minus2] because that argument [n] is mentioned directly
    in the final goal. However, it doesn't help in the case of
    [evSS_ev] since the term that gets replaced ([S (S n)]) is not
    mentioned anywhere. *)

(** If we [remember] that term [S (S n)], the proof goes
    through.  (We'll discuss [remember] in more detail below.) *)

Theorem evSS_ev_remember : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. remember (S (S n)) as k eqn:Hk.
  destruct E as [|n' E'] eqn:EE.
  - (* E = ev_0 *)
    (* Now we do have an assumption, in which [k = S (S n)] has been
       rewritten as [0 = S (S n)] by [destruct]. That assumption
       gives us a contradiction. *)
    discriminate Hk.
  - (* E = ev_S n' E' *)
    (* This time [k = S (S n)] has been rewritten as [S (S n') = S (S n)]. *)
    injection Hk as Heq. rewrite <- Heq. apply E'.
Qed.

(** Alternatively, the proof is straightforward using the inversion
    lemma that we proved above. *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. apply ev_inversion in H.
  destruct H as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq.
    rewrite Heq. apply Hev.
Qed.

(** Note how both proofs produce two subgoals, which correspond
    to the two ways of proving [ev].  The first subgoal is a
    contradiction that is discharged with [discriminate].  The second
    subgoal makes use of [injection] and [rewrite].  Coq provides a
    handy tactic called [inversion] that factors out that common
    pattern.

    The [inversion] tactic can detect (1) that the first case ([n =
    0]) does not apply and (2) that the [n'] that appears in the
    [ev_SS] case must be the same as [n].  It has an "[as]" variant
    similar to [destruct], allowing us to assign names rather than
    have Coq choose them. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E' Heq].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
    - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice)

    Prove the following result using [inversion].  (For extra practice,
    you can also prove it using the inversion lemma.) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H. inversion H1.
  auto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (ev5_nonsense)

    Prove the following result using [inversion]. *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.
(** [] *)

(** The [inversion] tactic does quite a bit of work. For
    example, when applied to an equality assumption, it does the work
    of both [discriminate] and [injection]. In addition, it carries
    out the [intros] and [rewrite]s that are typically necessary in
    the case of [injection]. It can also be applied, more generally,
    to analyze evidence for inductively defined propositions.  As
    examples, we'll use it to re-prove some theorems from chapter
    [Tactics].  (Here we are being a bit lazy by omitting the [as]
    clause from [inversion], thereby asking Coq to choose names for
    the variables and hypotheses that it introduces.) *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.  Suppose the name
    [H] refers to an assumption [P] in the current context, where [P]
    has been defined by an [Inductive] declaration.  Then, for each of
    the constructors of [P], [inversion H] generates a subgoal in which
    [H] has been replaced by the exact, specific conditions under
    which this constructor could have been used to prove [P].  Some of
    these subgoals will be self-contradictory; [inversion] throws
    these away.  The ones that are left represent the cases that must
    be proved to establish the original goal.  For those, [inversion]
    adds all equations into the proof context that must hold of the
    arguments given to [P] (e.g., [S (S n') = n] in the proof of
    [evSS_ev]). *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop] in chapter [Logic], we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma. *)

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  (* WORKED IN CLASS *)
  unfold Even.

(** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy would
    probably lead to a dead end, because (as we've noted before) the
    induction hypothesis will talk about n-1 (which is _not_ even!).
    Thus, it seems better to first try [inversion] on the evidence for
    [ev].  Indeed, the first case can be solved trivially. And we can
    seemingly make progress on the second case with a helper lemma. *)

  intros n E. inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *)

(** Unfortunately, the second case is harder.  We need to show [exists
    n0, S (S n') = double n0], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't
    directly useful, it seems that we are stuck and that performing
    case analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to a similar
    one that involves a _different_ piece of evidence for [ev]:
    namely [E'].  More formally, we can finish our proof by showing
    that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result suffices. *)

    assert (H: (exists k', n' = double k') -> (exists n0, S (S n') = double n0)).
    { intros [k' EQ'']. exists (S k'). simpl. rewrite <- EQ''. reflexivity. }
    apply H.

    (** Unforunately, now we are stuck. To make that apparent, let's move
        [E'] back into the goal from the hypotheses. *)

    generalize dependent E'.

    (** Now it is clear we are trying to prove another instance of the
        same theorem we set out to prove.  This instance is with [n'],
        instead of [n], where [n'] is a smaller natural number than [n]. *)
Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this looks familiar, it is no coincidence: We've encountered
    similar problems in the [Induction] chapter, when trying to
    use case analysis to prove results that required induction.  And
    once again the solution is... induction! *)

(** The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypothesis for each recursive occurrence of
    the property in question.

    To prove a property of [n] holds for all numbers for which [ev
    n] holds, we can use induction on [ev n]. This requires us to
    prove two things, corresponding to the two ways in which [ev n]
    could have been constructed. If it was constructed by [ev_0], then
    [n=0], and the property must hold of [0]. If it was constructed by
    [ev_SS], then the evidence of [ev n] is of the form [ev_SS n'
    E'], where [n = S (S n')] and [E'] is evidence for [ev n']. In
    this case, the inductive hypothesis says that the property we are
    trying to prove holds for [n']. *)

(** Let's try our current lemma again: *)

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    unfold Even. exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : Even E' *)
    unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even. exists (S k). simpl. reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas, and in particular when
    formalizing the semantics of programming languages, where many
    properties of interest are defined inductively. *)

(** The following exercises provide simple examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros.
  induction H.
  - auto.
  - simpl. constructor. auto.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ev'_ev)

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from [Logic]) of
    applying theorems to arguments, and note that the same technique
    works with constructors of inductively defined propositions. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  split; intros.
  - induction H; simpl.
    + constructor.
    + repeat constructor.
    + apply ev_sum; auto.
  - induction H.
    + constructor.
    + replace (S (S n)) with (2 + n). apply (ev'_sum 2 n).
      * constructor.
      * auto.
      * lia.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, especially useful (ev_ev__ev)

    There are two pieces of evidence you could attempt to induct upon
    here. If one doesn't work, try the other. *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros.
  induction H0; simpl in *.
  - auto.
  - inversion H. apply IHev in H2. auto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)

    This exercise can be completed without induction or case analysis.
    But, you will need a clever assertion and some tedious rewriting.
    Hint:  is [(n+m) + (n+p)] even? *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros.
  assert (ev ((n+m) + (n+p))). { apply ev_sum; auto. }
  assert ((n + m) + (n + p) = (n+n) + (m+p)). { lia. }
  rewrite H2 in H1.
  apply ev_ev__ev with (m:=m+p) (n:=n+n).
  - auto.
  - replace (n+n) with (double n). apply ev_double.
    apply double_plus.
Qed.
(** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** ... And, just like properties, relations can be defined
    inductively.  One useful example is the "less than or equal to"
    relation on numbers. *)

(** The following definition says that there are two ways to
    show that one number is less than or equal to another: either
    observe that they are the same number, or, if the second has the
    form [S m], give evidence that the first is less than or equal to
    [m]. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

End Playground.

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_ev : nat -> nat -> Prop :=
  | ne_1 n (H: ev (S n))     : next_ev n (S n)
  | ne_2 n (H: ev (S (S n))) : next_ev n (S (S n)).

(** **** Exercise: 2 stars, standard, optional (total_relation)

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive my_total : nat -> nat -> Prop :=
  | total_refl n : my_total n n
  | total_suc n m (H : my_total n m) : my_total n (S m)
  | total_pred n m (H : my_total n m) : my_total n (pred m).
                                                
(** **** Exercise: 2 stars, standard, optional (empty_relation)

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive my_empty : nat -> nat -> Prop :=
  | empty_none n m (H : my_empty (pred n) (pred m)) : my_empty n m.
  
(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n'].
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** **** Exercise: 3 stars, standard, optional (le_exercises)

    Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros. induction H0.
  - assumption.
  - constructor. assumption.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n; auto.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction H; auto.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. inversion H.
  - auto.
  - apply le_trans with (n:=S n); auto.
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intro n. induction n; intros.
  - induction m.
    + right. auto.
    + inversion IHm. left. inversion H; auto.
      inversion H. left. auto.
  - induction m.
    + right. constructor. apply O_le_n.
    + inversion IHm.
      * left. inversion H; auto.
      * inversion H.
        -- left. auto.
        -- right. apply n_le_m__Sn_le_Sm. auto.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros. induction a.
  - apply O_le_n.
  - apply n_le_m__Sn_le_Sm. auto.
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros.
  specialize (le_plus_l n1 n2) as H1.
  specialize (le_plus_l n2 n1) as H2.
  split.
  - eapply le_trans; eauto.
  - rewrite add_comm in H2. eapply le_trans; eauto.
Qed.

(** Hint: the next one may be easiest to prove by induction on [n]. *)

Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intro n.
  induction n; simpl; intros.
  - left. apply O_le_n.
  - destruct p.
    + right. apply le_trans with (n:=(S (n + m))).
      constructor. rewrite add_comm. apply le_plus_l. simpl in H. assumption.
    + specialize (IHn m p q).
      simpl in H. apply Sn_le_Sm__n_le_m in H. apply IHn in H.
      inversion H.
      * left. apply n_le_m__Sn_le_Sm. auto.
      * right. auto.
Qed.        

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros. induction p.
  - auto.
  - simpl. apply n_le_m__Sn_le_Sm. auto.
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros.
  rewrite add_comm. assert (m + p = p + m). { apply add_comm. }
  rewrite H0.
  apply plus_le_compat_l. auto.
Qed.
  
Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros.
  specialize (le_plus_l n p). intros.
  specialize (plus_le_compat_r n m p H). intros.
  eapply le_trans; eauto.
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  intros.
  inversion H.
  - auto.
  - constructor. apply le_trans with (n:=S n); auto.
Qed.


Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros. unfold lt. induction H; split.
  - apply n_le_m__Sn_le_Sm. apply le_plus_l.
  - apply n_le_m__Sn_le_Sm. rewrite add_comm. apply le_plus_l.
  - inversion IHle. auto.
  - inversion IHle. auto.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intro n. induction n. intros.
  - apply O_le_n.
  - intros. destruct m.
    * inversion H.
    * apply n_le_m__Sn_le_Sm. auto.
Qed.

(** Hint: The next one may be easiest to prove by induction on [m]. *)

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros. generalize dependent n. induction m; intros.
  - inversion H. auto.
  - destruct n.
    + auto.
    + simpl. apply IHm. apply Sn_le_Sm__n_le_m. auto.
Qed. 

(** Hint: The next one can easily be proved without using [induction]. *)

 
Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros.
  apply leb_complete in H. apply leb_complete in H0.
  apply leb_correct.
  eapply le_trans; eauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (leb_iff) *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  split; intros.
  apply leb_complete. auto.
  apply leb_correct. auto.
Qed.
(** [] *)


Theorem leb_false_rev : forall n m,
   n <=? m = false -> m <=? n = true.
Proof.
  intros.
  generalize dependent m.
  induction n; intros.
  - destruct m.
    + auto.
    + simpl in H. discriminate.
  - destruct m; auto.
    + simpl in *. apply IHn, H.
Qed.

      
Module R.

(** **** Exercise: 3 stars, standard, especially useful (R_provability)

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
  | c1                                     : R 0     0     0
  | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
  | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
  | c5 m n o (H : R m     n     o        ) : R n     m     o
.

(** - Which of the following propositions are provable?
      - [R 1 1 2] yes
      - [R 2 2 6] no

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
      no, swap c2 and c3 

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
      no. c4 can be replaced by c2 + c3
 *)


(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact)

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq. *)

Definition fR : nat -> nat -> nat :=
  fun a => fun b => a + b.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  unfold fR. split; intros.
  - induction H; subst; auto.
    + simpl in IHR. rewrite <- plus_n_Sm in IHR. do 2 inversion IHR. auto.
    + apply add_comm.
  - generalize dependent m. generalize dependent n.
    induction o; intros; destruct n; destruct m; try inversion H.
    + constructor.
    + rewrite H1. constructor. apply IHo. auto.
    + constructor. apply IHo. auto.
    + rewrite H1. apply c2. apply IHo. auto.
Qed.

End R.

(** **** Exercise: 2 stars, advanced (subsequence)

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully! *)

Inductive subseq : list nat -> list nat -> Prop :=
  | subseq_zero : subseq [] []
  | subseq_one (n : nat) (ls1 ls2 : list nat) (H : subseq ls1 ls2) : subseq ls1 (n :: ls2)
  | subseq_two (n : nat) (ls1 ls2 : list nat) (H : subseq ls1 ls2) : subseq (n :: ls1) (n :: ls2)                       .                                        

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  induction l; intros.
  - apply subseq_zero.
  - apply subseq_two. auto.
Qed.    

Theorem subseq_empty : forall (l : list nat), subseq [] l.
Proof.
  induction l; intros.
  - apply subseq_zero.
  - apply subseq_one. auto.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros. induction H.
  - apply subseq_empty.
  - simpl. apply subseq_one. apply IHsubseq.
  - simpl. apply subseq_two. apply IHsubseq.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
 intros.
 generalize dependent l1.
 induction H0.
 - intros. apply H.
 - intros. apply subseq_one, IHsubseq, H.
 - intros. inversion H; subst.
   + apply subseq_one, IHsubseq, H3.
   + apply subseq_two, IHsubseq, H3.
Qed.
    
(** [] *)

(** **** Exercise: 2 stars, standard, optional (R_provability2)

    Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1                    : R 0     []
      | c2 n l (H: R n     l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n     l.

    Which of the following propositions are provable?

    - [R 2 [1;0]] yes 
    - [R 1 [1;2;1;0]] no
    - [R 6 [3;2;1;0]] yes *)   

(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** The [ev] property provides a simple example for
    illustrating inductive definitions and the basic techniques for
    reasoning about them, but it is not terribly exciting -- after
    all, it is equivalent to the two non-inductive definitions of
    evenness that we had already seen, and does not seem to offer any
    concrete benefit over them.

    To give a better sense of the power of inductive definitions, we
    now show how to use them to model a classic concept in computer
    science: _regular expressions_. *)

(** Regular expressions are a simple language for describing sets of
    strings.  Their syntax is defined as follows: *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- that is, lists of elements of [T].

    (We depart slightly from standard practice in that we do not
    require the type [T] to be finite.  This results in a somewhat
    different theory of regular expressions, but the difference is not
    significant for our purposes.) *)

(** We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2],
        then [App re1 re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s],
        then [Union re1 re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation
        of a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i],
        then [Star re] matches [s].

        In particular, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this informal definition into an
    [Inductive] one as follows.  We use the notation [s =~ re] in
    place of [exp_match s re].  (By "reserving" the notation before
    defining the [Inductive], we can use it in the definition.) *)

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

(** Again, for readability, we can also display this definition using
    inference-rule notation. *)

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re
*)

(** Notice that these rules are not _quite_ the same as the
    informal ones that we gave at the beginning of the section.
    First, we don't need to include a rule explicitly stating that no
    string matches [EmptySet]; we just don't happen to include any
    rule that would have the effect of some string matching
    [EmptySet].  (Indeed, the syntax of inductive definitions doesn't
    even _allow_ us to give such a "negative rule.")

    Second, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the informal rules are indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the string
    [[1]] directly.  Since the goal mentions [[1; 2]] instead of
    [[1] ++ [2]], Coq wouldn't be able to figure out how to split
    the string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the same shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars, standard (exp_match_ex1)

    The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  unfold not. intros. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros. inversion H.
  - apply MUnionL. auto.
  - apply MUnionR. auto.
Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss.
  - apply MStar0.
  - simpl. apply MStarApp.
    + specialize (H x). assert (In x (x::ss)). { simpl. left. auto. } apply H in H0. auto.
    + apply IHss. intros. apply H. simpl. right. auto.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (reg_exp_of_list_spec)

    Prove that [reg_exp_of_list] satisfies the following
    specification: *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  split; intros.
  - generalize dependent s1. induction s2; intros; inversion H.
    + auto.
    + subst. inversion H3. specialize (IHs2 s3 H4).
      rewrite IHs2. auto.
  - rewrite <- H. induction H. induction s1; simpl.
    + constructor.
    + replace (x :: s1) with ([x] ++ s1). Focus 2. auto.
      constructor.
      * constructor.
      * auto.
Qed.

(** [] *)

(** Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)

(** For example, suppose that we wanted to prove the following
    intuitive result: If a regular expression [re] matches some string
    [s], then all elements of [s] must occur as character literals
    somewhere in [re].

    To state this theorem, we first define a function [re_chars] that
    lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** We can then phrase our theorem as follows: *)


Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.

(** Something interesting happens in the [MApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re1]), and a second one that applies when [x]
    occurs in [s2] (which matches [re2]). *)

    rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.

(** Here again we get two induction hypotheses, and they illustrate
    why we need induction on evidence for [exp_match], rather than
    induction on the regular expression [re]: The latter would only
    provide an induction hypothesis for strings that match [re], which
    would not allow us to reason about the case [In x s2]. *)

    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars, standard (re_not_empty)

    Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
  | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
  | Star re => true
  end.
   

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split; intros.
  - induction re; inversion H; auto; simpl.
    + inversion H0.
    + inversion H0; subst. apply andb_true_iff. split.
      apply IHre1. exists s1. auto. apply IHre2. exists s2. auto.
    + inversion H0; subst; apply orb_true_iff.
      left. apply IHre1. exists x. auto.
      right. apply IHre2. exists x. auto.
  - induction re.
    + inversion H.
    + exists []. constructor.
    + exists [t]. constructor.
    + inversion H. apply andb_true_iff in H1. inversion H1.
      specialize (IHre1 H0). specialize (IHre2 H2).
      inversion IHre1. inversion IHre2.
      exists (x ++ x0). constructor; auto.
    + inversion H. apply orb_true_iff in H1. inversion H1.
      * specialize (IHre1 H0). inversion IHre1. exists x. apply MUnionL. auto.
      * specialize (IHre2 H0). inversion IHre2. exists x. apply MUnionR. auto.
    + exists []. apply MStar0.
Qed.
(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it will let you try to perform an induction over a term that
    isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] without an [eqn:] clause can do),
    and leave you unable to complete the proof.  Here's an example: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** Now, just doing an [inversion] on [H1] won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence!). Here is a naive first attempt.

    (We can begin by generalizing [s2], since it's pretty clear that we
    are going to have to walk over both [s1] and [s2] in parallel.) *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** But now, although we get seven cases (as we would expect
    from the definition of [exp_match]), we have lost a very important
    bit of information from [H1]: the fact that [s1] matched something
    of the form [Star re].  This means that we have to give proofs for
    _all_ seven constructors of this definition, even though all but
    two of them ([MStar0] and [MStarApp]) are contradictory.  We can
    still get the proof to go through for a few constructors, such as
    [MEmpty]... *)

  - (* MEmpty *)
    simpl. intros s2 H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show that

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    which is clearly impossible. *)

  - (* MChar. *) intros s2 H. simpl. (* Stuck... *)
Abort.

(** The problem is that [induction] over a Prop hypothesis only works
    properly with hypotheses that are completely general, i.e., ones
    in which all the arguments are variables, as opposed to more
    complex expressions, such as [Star re].

    (In this respect, [induction] on evidence behaves more like
    [destruct]-without-[eqn:] than like [inversion].)

    An awkward way to solve this problem is "manually generalizing"
    over the problematic expressions by adding explicit equality
    hypotheses to the lemma: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence
    directly, because the argument to the first hypothesis is
    sufficiently general, which means that we can discharge most cases
    by inverting the [re' = Star re] equality in the context.

    This idiom is so common that Coq provides a
    tactic to automatically generate such equations for us, avoiding
    thus the need for changing the statements of our theorems. *)
Abort.

(** As we saw above, The tactic [remember e as x] causes Coq to (1)
    replace all occurrences of the expression [e] by the variable [x],
    and (2) add an equation [x = e] to the context.  Here's how we can
    use it to show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, allowing us to
    conclude immediately. *)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    injection Heqre' as Heqre''. intros s H. apply H.

  - (* MStarApp *)
    injection Heqre' as Heqre''.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite Heqre''. reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars, standard, optional (exp_match_ex2) *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros.  
  remember (Star re) as re'.
  induction H; try discriminate.
  - exists []. split.
    + auto.
    + intros. contradiction.
  - inversion Heqre'. subst.
    specialize (IHexp_match2 Heqre') as H1.
    destruct H1 as [ss2 [Hss2_1 Hss2_2]].
    exists (s1 :: ss2). split.
    + simpl. rewrite Hss2_1. auto.
    + intros. inversion H1.
      * subst. auto.
      * apply Hss2_2. auto.
Qed.      

(** **** Exercise: 5 stars, advanced (weak_pumping)

    One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].  (For the sake of simplicity in this
    exercise, we consider a slightly weaker theorem than is usually
    stated in courses on automata theory.)

    To get started, we need to define "sufficiently long."  Since we
    are working in a constructive logic, we actually need to be able
    to calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)


Ltac app_assoc_eq := repeat rewrite app_assoc; auto.

Ltac split_all := repeat (try split).
  
Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

(** You may find these lemmas about the pumping constant useful when
    proving the pumping lemma below. *)

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
  intros T re. induction re.
  - (* EmptySet *)
    apply le_n.
  - (* EmptyStr *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* App *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Union *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Star *)
    simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  inversion Hp1 as [Hp1'| p Hp1' Hp1''].
  - rewrite H in Hp1'. discriminate Hp1'.
  - rewrite H in Hp1''. discriminate Hp1''.
Qed.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

(** This auxiliary lemma might also be useful in your proof of the
    pumping lemma. *)

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.

(** The (weak) pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3] will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)


Lemma napp_star' : forall T s (re : reg_exp T)  m, s =~ Star re -> napp m s =~ Star re.
Proof.
  intros.
  induction m.
  - simpl. constructor.
  - simpl. apply star_app; auto.
Qed.

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You are to fill in the proof. Several of the lemmas about
    [le] that were in an optional exercise earlier in this chapter
    may be useful. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  -
    simpl. intros contra. inversion contra. inversion H0.
  -
    simpl. intros. rewrite app_length in H. apply add_le_cases in H. destruct H as [H1 | H2].
    + apply IH1 in H1. destruct H1 as [s2' [s3' [s4' [Heq [Hs3notempty Hs234pumping]]]]].
      exists s2', s3', (s4' ++ s2). all : split_all.
      * rewrite Heq. app_assoc_eq. 
      * auto.
      * intros. assert (s2' ++ (napp m s3') ++ s4' ++ s2 = (s2' ++ (napp m s3') ++ s4') ++ s2). { app_assoc_eq. }
        rewrite H. constructor; auto.
   + apply IH2 in H2. destruct H2 as [s2' [s3' [s4' [Heq [Hs3notempty Hs234pumping]]]]].
      exists (s1 ++ s2'), s3', s4'. all : split_all.
      * rewrite Heq. app_assoc_eq.
      * auto.
      * intros. assert (((s1 ++ s2') ++ napp m s3' ++ s4') = (s1 ++ (s2' ++ napp m s3' ++ s4'))). { app_assoc_eq. }
        rewrite H. constructor; auto.
  -
    simpl. intros. apply plus_le in H. destruct H as [H1 H2]. 
    apply IH in H1. destruct H1 as [s2' [s3' [s4' [Heq [Hs3notempty Hs234pumping]]]]].
    exists s2', s3', s4'.  all : split_all; auto.
    intros. apply MUnionL. auto.
  -
    simpl. intros. apply plus_le in H. destruct H as [H1 H2]. 
    apply IH in H2. destruct H2 as [s2' [s3' [s4' [Heq [Hs3notempty Hs234pumping]]]]].
    exists s2'. exists s3'. exists s4'.  all : split_all; auto.
    intros. apply MUnionR. auto.
  -
    simpl. intros. inversion H. apply pumping_constant_0_false in H1.  inversion H1.
  -
    intros. destruct s1; destruct s2.
    + simpl in H. inversion H. apply pumping_constant_0_false in H1. contradiction.      
    + exists []. exists (x :: s2). exists []. all : split_all; simpl.
      * rewrite app_nil_r. auto.
      * unfold not. intros. inversion H0.
      * intros. rewrite app_nil_r. apply napp_star'. assumption.
    + exists []. exists (x :: s1). exists []. all : split_all; simpl.
      * unfold not. intro contra. inversion contra.
      * intros. apply napp_star; auto.
    + exists [], (x :: s1), (x0::s2). all : split_all; auto.
      * unfold not. intro contra. inversion contra.
      * intros. simpl. apply napp_star; auto.
Qed.


Lemma negb_true_iff : forall b, (negb b = true) <-> b = false.
  split; intros; destruct b; try auto.
Qed.

Lemma weak_pumping' : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You are to fill in the proof. Several of the lemmas about
    [le] that were in an optional exercise earlier in this chapter
    may be useful. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  -
    simpl. intros contra. inversion contra. inversion H0.
  -
    simpl. intros. rewrite app_length in H. apply add_le_cases in H. destruct H as [H1 | H2].
    + apply IH1 in H1. destruct H1 as [s2' [s3' [s4' [Heq [Hs3notempty Hs234pumping]]]]].
      exists s2', s3', (s4' ++ s2). all : split_all.
      * rewrite Heq. app_assoc_eq. 
      * auto.
      * intros. assert (s2' ++ (napp m s3') ++ s4' ++ s2 = (s2' ++ (napp m s3') ++ s4') ++ s2). { app_assoc_eq. }
        rewrite H. constructor; auto.
   + apply IH2 in H2. destruct H2 as [s2' [s3' [s4' [Heq [Hs3notempty Hs234pumping]]]]].
      exists (s1 ++ s2'), s3', s4'. all : split_all.
      * rewrite Heq. app_assoc_eq.
      * auto.
      * intros. assert (((s1 ++ s2') ++ napp m s3' ++ s4') = (s1 ++ (s2' ++ napp m s3' ++ s4'))). { app_assoc_eq. }
        rewrite H. constructor; auto.
  -
    simpl. intros. apply plus_le in H. destruct H as [H1 H2]. 
    apply IH in H1. destruct H1 as [s2' [s3' [s4' [Heq [Hs3notempty Hs234pumping]]]]].
    exists s2', s3', s4'.  all : split_all; auto.
    intros. apply MUnionL. auto.
  -
    simpl. intros. apply plus_le in H. destruct H as [H1 H2]. 
    apply IH in H2. destruct H2 as [s2' [s3' [s4' [Heq [Hs3notempty Hs234pumping]]]]].
    exists s2', s3', s4'.  all : split_all; auto.
    intros. apply MUnionR. auto.
  -
    simpl. intros. inversion H. apply pumping_constant_0_false in H1.  inversion H1.
  -
    intros.
    assert ((eqb (length s1) 0) && (eqb (length s2) 0) || (negb (eqb (length s1) 0) || negb (eqb (length s2) 0)) = true).
    apply all3_spec. apply orb_true_iff in H0. inversion H0.
    + (* length s1 = 0 && length s2 ==0 *)
      apply andb_true_iff in H1. destruct H1 as [H0lens1 H0lens2].
      apply eqb_eq in H0lens1, H0lens2.
      rewrite app_length in H. rewrite H0lens1, H0lens2 in H. simpl in H.
      inversion H. apply pumping_constant_0_false in H2. inversion H2.
    + (* length s1 <> 0 || length s2 <> 0 *)
      apply orb_true_iff in H1.
      inversion H1.
      * apply negb_true_iff in H2. apply eqb_neq in H2.
        exists [], s1, s2. all : split_all; auto.
        -- unfold not. intros. subst s1. simpl in H2. specialize (H2 (eq_refl 0)). contradiction.
        -- intros. apply napp_star; auto.
      * apply negb_true_iff in H2. apply eqb_neq in H2.
        exists s1, s2, [].  all : split_all. auto.
        -- rewrite app_nil_r. auto.
        -- unfold not. intros. subst s2. simpl in H2. specialize (H2 (eq_refl 0)). contradiction.
        -- intros. rewrite app_nil_r. constructor; auto. apply napp_star'. auto.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (pumping)

    Now here is the usual version of the pumping lemma. In addition to
    requiring that [s2 <> []], it also requires that [length s1 +
    length s2 <= pumping_constant re]. *)

(* Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You may want to copy your proof of weak_pumping below. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  -
    simpl. intros contra. inversion contra. inversion H0.
  -
    simpl. intros. rewrite app_length in H. apply add_le_cases in H. destruct H as [H1 | H2].
    + apply IH1 in H1. destruct H1 as [s2' [s3' [s4' [Heq [Hs3notempty [Hs234len Hs234pumping]]]]]].
      exists s2', s3', (s4' ++ s2).  all : split_all.
      * rewrite Heq. app_assoc_eq.
      * auto.
      * eapply le_trans. eauto. apply le_plus_l.
      * intros. assert (s2' ++ (napp m s3') ++ s4' ++ s2 = (s2' ++ (napp m s3') ++ s4') ++ s2). { app_assoc_eq. }
        rewrite H. constructor; auto.
    + apply IH2 in H2. destruct H2 as [s2' [s3' [s4' [Heq' [Hs3'notempty [Hs'234len Hs'234pumping]]]]]].
      destruct (leb (pumping_constant re1) (length s1)) eqn: Hpcre1.
      * apply leb_iff in Hpcre1. apply IH1 in Hpcre1.
        destruct Hpcre1 as [s2'' [s3'' [s4'' [Heq'' [Hs3''notempty [Hs''234len Hs''234pumping]]]]]].
        exists s2'', s3'', (s4'' ++ s2). all : split_all.
        -- rewrite Heq''. app_assoc_eq.
        -- auto.
        -- eapply le_trans. eauto. apply le_plus_l.
        -- intros. assert (s2'' ++ napp m s3'' ++ s4'' ++ s2 = (s2'' ++ napp m s3'' ++ s4'') ++ s2). { app_assoc_eq. }
           rewrite H. constructor; auto.
      * exists (s1 ++ s2'), s3', s4'. all : split_all.
        -- rewrite Heq'. app_assoc_eq.
        -- auto.
        -- rewrite app_length. apply le_trans with (n:=pumping_constant re1 + length s2' + length s3').
           ++ repeat apply plus_le_compat_r; auto. apply leb_false_rev in Hpcre1. apply leb_complete in Hpcre1. auto.
           ++ rewrite <- add_assoc. apply plus_le_compat_l. auto.
        -- intros. simpl. assert ((s1 ++ s2') ++ napp m s3' ++ s4' = s1 ++ (s2' ++ napp m s3' ++ s4')). { app_assoc_eq. }
           rewrite H. constructor; auto.
  -
    simpl. intros.
    assert (H1: pumping_constant re1 <= length s1). { eapply le_trans. 2: apply H. apply le_plus_l. }
    apply IH in H1. destruct H1 as [s2' [s3' [s4' [Heq [Hs3notempty [Hs234len Hs234pumping]]]]]].
    exists s2', s3', s4'. all : split_all; auto.
    + eapply le_trans. apply Hs234len. apply le_plus_l.
    + intros. apply MUnionL. auto.
  -
    simpl. intros.
    assert (H2: pumping_constant re2 <= length s2). { eapply le_trans. 2: apply H. rewrite add_comm. apply le_plus_l. }
    apply IH in H2. destruct H2 as [s2' [s3' [s4' [Heq [Hs3notempty [Hs234len Hs234pumping]]]]]].
    exists s2', s3', s4'. all : split_all; auto.
    + eapply le_trans. apply Hs234len. rewrite add_comm. apply le_plus_l.
    + intros. apply MUnionR. auto.
  -
    simpl. intro contra. inversion contra. apply pumping_constant_0_false in H0. contradiction.
  -
    intros.
    assert ((eqb (length s1) 0) && (eqb (length s2) 0) || (negb (eqb (length s1) 0) || negb (eqb (length s2) 0)) = true).
    apply all3_spec. apply orb_true_iff in H0. inversion H0.
    + (* length s1 = 0 && length s2 ==0 *)
      apply andb_true_iff in H1. destruct H1 as [H0lens1 H0lens2].
      apply eqb_eq in H0lens1, H0lens2.
      rewrite app_length in H. rewrite H0lens1, H0lens2 in H. simpl in H.
      inversion H. apply pumping_constant_0_false in H2. inversion H2.
    + (* length s1 <> 0 || length s2 <> 0 *)
      apply orb_true_iff in H1.
      inversion H1.
      -- (* length s1 <> 0 *)
         destruct (leb (pumping_constant re) (length s1)) eqn:Hlens1.
         ++ apply leb_complete in Hlens1.
            apply IH1 in Hlens1.
            destruct Hlens1 as [s2' [s3' [s4' [Heq [Hs3notempty [Hs234len Hs234pumping]]]]]].
            exists s2', s3', (s4' ++ s2). all : split_all.
            ** rewrite Heq. app_assoc_eq.
            ** auto.
            ** simpl. auto.
            ** intros. assert  (s2' ++ napp m s3' ++ s4' ++ s2 = (s2' ++ napp m s3' ++ s4') ++ s2). { app_assoc_eq. }
             rewrite H3. constructor; auto.
         ++ exists [], s1, s2. all : split_all.
            ** unfold not. intro. subst s1. simpl in H2. discriminate.
            ** simpl. apply leb_false_rev in Hlens1. apply leb_complete in Hlens1. auto.
            ** intros. simpl. apply napp_star; auto.               
      -- (* length s2 <> 0 *)
         destruct (leb (pumping_constant re) (length s1)) eqn:Hlens1.
         ++ (* length s1 >= pumping_constant re *)
            apply leb_complete in Hlens1.
            apply IH1 in Hlens1.
            destruct Hlens1 as [s2' [s3' [s4' [Heq [Hs3notempty [Hs234len Hs234pumping]]]]]].
            exists s2', s3', (s4' ++ s2). all : split_all.
            ** rewrite Heq. app_assoc_eq.
            ** auto.
            ** simpl. auto.
            ** intros. assert  (s2' ++ napp m s3' ++ s4' ++ s2 = (s2' ++ napp m s3' ++ s4') ++ s2). { app_assoc_eq. }
             rewrite H3. constructor; auto.
         ++ (* length s1 <= pumping_constant re *)
            destruct (length s1) eqn:Hlens1eq0. assert (s1 = []). { destruct s1. auto. inversion Hlens1eq0. }
            ** (* length s1 = 0 *)
               inversion Hlens1eq0.
               destruct (leb (pumping_constant re) (length s2)) eqn:Hlens2.
               --- apply leb_complete in Hlens2.
                   apply IH2 in Hlens2. destruct Hlens2 as [s2' [s3' [s4' [Heq [Hs3notempty [Hs234len Hs234pumping]]]]]].
                   exists s2', s3', s4'. all : split_all; auto.
                   +++ subst. auto.
               --- apply leb_false_rev in Hlens2.
                   exists [], s2, []. all : split_all; auto.
                   +++ subst. rewrite app_nil_r. auto.
                   +++ unfold not. intro. subst. inversion H2.
                   +++ apply leb_complete in Hlens2. auto.
                   +++ intros. rewrite app_nil_r. apply napp_star'. auto.
            ** exists [], s1, s2. all : split_all.
               --- unfold not. intros. subst s1. inversion Hlens1eq0.
               --- simpl. apply leb_false_rev in Hlens1.  rewrite Hlens1eq0. apply leb_complete in Hlens1. auto.
               --- intros. simpl. apply napp_star; auto.
Qed. *)



Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You may want to copy your proof of weak_pumping below. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - 
    simpl. intros contra. inversion contra. inversion H0.
  -
    simpl. intros. rewrite app_length in H. apply add_le_cases in H. destruct H as [H1 | H2].
    + apply IH1 in H1. destruct H1 as [s2' [s3' [s4' [Heq [Hs3notempty [Hs234len Hs234pumping]]]]]].
      exists s2', s3', (s4' ++ s2). all : split_all.
      * rewrite Heq. app_assoc_eq.
      * auto.
      * eapply le_trans. eauto. apply le_plus_l.
      * intros. assert (s2' ++ (napp m s3') ++ s4' ++ s2 = (s2' ++ (napp m s3') ++ s4') ++ s2). { app_assoc_eq. }
        rewrite H. constructor; auto.
    + apply IH2 in H2. destruct H2 as [s2' [s3' [s4' [Heq' [Hs3'notempty [Hs'234len Hs'234pumping]]]]]].
      destruct (leb (pumping_constant re1) (length s1)) eqn: Hpcre1.
      * apply leb_iff in Hpcre1. apply IH1 in Hpcre1.
        destruct Hpcre1 as [s2'' [s3'' [s4'' [Heq'' [Hs3''notempty [Hs''234len Hs''234pumping]]]]]].
        exists s2'', s3'', (s4'' ++ s2). all : split_all.
        -- rewrite Heq''. app_assoc_eq.
        -- auto.
        -- eapply le_trans. eauto. apply le_plus_l. 
        -- intros. assert (s2'' ++ napp m s3'' ++ s4'' ++ s2 = (s2'' ++ napp m s3'' ++ s4'') ++ s2). { app_assoc_eq. }
           rewrite H. constructor; auto.
      * exists (s1 ++ s2'), s3', s4'. all : split_all.
        -- rewrite Heq'. app_assoc_eq.
        -- auto.
        -- rewrite app_length. apply le_trans with (n:=pumping_constant re1 + length s2' + length s3').
           ++ repeat apply plus_le_compat_r; auto. apply leb_false_rev in Hpcre1. apply leb_complete in Hpcre1. auto.
           ++ rewrite <- add_assoc. apply plus_le_compat_l. auto.
        -- intros. simpl. assert ((s1 ++ s2') ++ napp m s3' ++ s4' = s1 ++ (s2' ++ napp m s3' ++ s4')). { app_assoc_eq. }
           rewrite H. constructor; auto.
  -
    simpl. intros.
    assert (H1: pumping_constant re1 <= length s1). { eapply le_trans. 2 : apply H. apply le_plus_l. }
    apply IH in H1. destruct H1 as [s2' [s3' [s4' [Heq [Hs3notempty [Hs234len Hs234pumping]]]]]].
    exists s2', s3', s4'. all : split_all; auto.
    + eapply le_trans. apply Hs234len. apply le_plus_l.
    + intros. apply MUnionL. auto.
  -
    simpl. intros.
    assert (H2: pumping_constant re2 <= length s2). { eapply le_trans. 2 : apply H. rewrite add_comm. apply le_plus_l. }
    apply IH in H2. destruct H2 as [s2' [s3' [s4' [Heq [Hs3notempty [Hs234len Hs234pumping]]]]]].
    exists s2', s3', s4'. all : split_all; auto.
    + eapply le_trans. apply Hs234len. rewrite add_comm. apply le_plus_l.
    + intros. apply MUnionR. auto.
  -
    simpl. intro contra. inversion contra. apply pumping_constant_0_false in H0. contradiction.
  -
    intros.
    destruct (leb (pumping_constant re) (length s1)) eqn: Hpcre1.
    +
      apply leb_complete in Hpcre1.
      apply IH1 in Hpcre1.
      destruct Hpcre1 as [s2' [s3' [s4' [Heq [Hs3notempty [Hs234len Hs234pumping]]]]]].
      exists s2', s3', (s4' ++ s2). all : split_all; auto.
      * subst. app_assoc_eq.
      * intros. assert (s2' ++ napp m s3' ++ s4' ++ s2 = (s2' ++ napp m s3' ++ s4') ++ s2). { app_assoc_eq. }
        rewrite H0. constructor; auto.
    +
      destruct (eqb (length s1) 0) eqn:Hlens1eq0. 
      **
         assert (s1 = []). { destruct s1. auto. inversion Hlens1eq0. } subst s1.
         destruct (leb (pumping_constant re) (length s2)) eqn: Hpcre2.
         --- apply leb_complete in Hpcre2.
             apply IH2 in Hpcre2. destruct Hpcre2 as [s2' [s3' [s4' [Heq [Hs3notempty [Hs234len Hs234pumping]]]]]].
             exists s2', s3', s4'. all : split_all; auto.
         --- apply leb_false_rev in Hpcre2.
             destruct (eqb (length s2) 0) eqn:Hlens2eq0.
             +++ assert (s2 = []). { destruct s2. auto. inversion Hlens2eq0. } subst s2.
                 simpl in H. inversion H. apply pumping_constant_0_false in H1. contradiction.
             +++
                 exists [], s2, []. all : split_all; auto.
                 *** rewrite app_nil_r. auto.
                 *** unfold not. intro. subst. inversion Hlens2eq0.
                 *** apply leb_complete in Hpcre2. auto.
                 *** intros. rewrite app_nil_r. apply napp_star'. auto.
      **
         exists [], s1, s2. all : split_all.
         --- unfold not. intros. subst s1. inversion Hlens1eq0.
         --- apply leb_false_rev in Hpcre1. apply leb_complete in Hpcre1. auto.
         --- intros. apply napp_star; auto.
Qed.


End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we often need to
    relate boolean computations to statements in [Prop].  But
    performing this conversion as we did it there can result in
    tedious proof scripts.  Consider the proof of the following
    theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [eqb_eq] lemma to the equation generated by
    destructing [n =? m], to convert the assumption [n =? m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case. *)

(** We can streamline this by defining an inductive proposition that
    yields a better case-analysis principle for [n =? m].  Instead of
    generating an equation such as [(n =? m) = true], which is
    generally not directly useful, this principle gives us right away
    the assumption we really need: [n = m].

    Following the terminology introduced in [Logic], we call
    this the "reflection principle for equality (between numbers),"
    and we say that the boolean [n =? m] is _reflected in_ the
    proposition [n = m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  Intuitively, it states that the property
    [P] is _reflected_ in (i.e., equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].  To see this, notice
    that, by definition, the only way we can produce evidence for
    [reflect P true] is by showing [P] and then using the [ReflectT]
    constructor.  If we invert this statement, this means that it
    should be possible to extract evidence for [P] from a proof of
    [reflect P true].  Similarly, the only way to show [reflect P
    false] is by combining evidence for [~ P] with the [ReflectF]
    constructor. *)

(** To put this observation to work, we first prove that the
    statements [P <-> b = true] and [reflect P b] are indeed
    equivalent.  First, the left-to-right implication: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(** Now you prove the right-to-left implication: *)

(** **** Exercise: 2 stars, standard, especially useful (reflect_iff) *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros.
  inversion H.
  - split; auto.
  - split; intros.
    + contradiction.
    + inversion H2.
Qed.
(** [] *)

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second). *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** A smoother proof of [filter_not_empty_In] now goes as follows.
    Notice how the calls to [destruct] and [rewrite] are combined into a
    single call to [destruct]. *)

(** (To see this clearly, look at the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, standard, especially useful (eqbP_practice)

    Use [eqbP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Lemma eq_symm : forall A (x y : A), x = y <-> y = x.
Proof.
  intros. split; auto.
Qed.


Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros; unfold not; intros.
  induction l as [| n' l'].
  - inversion H0.
  - destruct (eqb n n') eqn:Heqnn'.
    + apply eqb_eq in Heqnn'. subst. simpl in H. rewrite (eqb_refl n') in H. inversion H.
    + simpl in H0. inversion H0.
      * rewrite eq_symm in H1. apply eqb_eq in H1. rewrite H1 in Heqnn'. discriminate.
      * inversion H. rewrite Heqnn' in H3. simpl in H3.
        specialize (IHl' H3 H1). contradiction.
Qed.
(** [] *)

(** This small example shows reflection giving us a small gain in
    convenience; in larger developments, using [reflect] consistently
    can often lead to noticeably shorter and clearer proof scripts.
    We'll see many more examples in later chapters and in _Programming
    Language Foundations_.

    The use of the [reflect] property has been popularized by
    _SSReflect_, a Coq library that has been used to formalize
    important results in mathematics, including as the 4-color theorem
    and the Feit-Thompson theorem.  The name SSReflect stands for
    _small-scale reflection_, i.e., the pervasive use of reflection to
    simplify small proof steps with boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (nostutter_defn)

    Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence [[1;4;1]] repeats the element [1] but does not
    stutter.)  The property "[nostutter mylist]" means that [mylist]
    does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
| ns_empty : nostutter []
| ns_one : forall (x: X), nostutter [x]
| ns_app : forall (x y : X) (ls:list X) (H: x<>y) (H2 : nostutter (x::ls)), nostutter (y::x::ls)                             
 (* FILL IN HERE *)
.

(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_2:  nostutter (@nil nat).
Proof. repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; auto. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)

    Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    Translate this specification into a Coq theorem and prove
    it.  (You'll need to begin by defining what it means for one list
    to be a merge of two others.  Do this with an inductive relation,
    not a [Fixpoint].)  *)

(* FILL IN HERE *)

Inductive inordermerge {X:Type} : list X -> list X -> list X -> Prop :=
| iom_nil : inordermerge [] [] []
| iom_app_l : forall (x : X) (l1 l2 l : list X) (H : inordermerge l1 l2 l), inordermerge (x::l1) l2 (x::l)
| iom_app_r : forall (x : X) (l1 l2 l : list X) (H : inordermerge l1 l2 l), inordermerge l1 (x::l2) (x::l)                            
 (* FILL IN HERE *)
.

Theorem inordermerge_test1 : inordermerge [1;6;2] [4;3] [1;4;6;2;3].
Proof.
  repeat constructor.
Qed.

Lemma In_cons : forall X (x : X) (l : list X), In x (x ::l).
Proof.
  intros.
  replace (x::l) with ([x] ++ l).
  apply In_app_iff. left. simpl. left. auto. auto.
Qed.

Theorem sublist_holds_P : forall X (x0 : X) (l : list X) (P : X -> Prop), 
  (forall x, In x (x0::l) -> P x) -> (forall x, In x l -> P x).
Proof.
  intros.
  specialize (H x).
  assert (In x (x0 :: l)). {
    replace (x0 :: l) with ([x0] ++ l).
    apply In_app_iff. right. auto.
    auto.
  }
  apply H. auto.
Qed.

Theorem filter_challenge : forall X (l1 l2 l : list X) (test : X -> bool), 
  inordermerge l1 l2 l -> 
  (forall x, In x l1 -> test x = true) -> 
  (forall x, In x l2 -> test x = false) -> 
  filter test l = l1.
Proof.
  intros. generalize dependent l1. generalize dependent l2.
  induction l; intros.
  - inversion H. auto.
  - inversion H; subst.
    + specialize (IHl l2 H1 l0 H5). 
      specialize (H0 x (In_cons X x l0)) as Htestt. simpl. rewrite H0. simpl. 
      specialize (sublist_holds_P X x l0 (fun x => test x = true) H0). intros. apply IHl in H2. rewrite H2. auto.
      apply (In_cons X x l0).
    + specialize (sublist_holds_P X x l3 (fun x => test x = false) H1). intros.
      specialize (IHl l3 H2 l1 H5 H0).
      specialize (H1 x (In_cons X x l3)). simpl. rewrite H1. auto.
Qed. 


(* Do not modify the following line: *)
Definition manual_grade_for_filter_challenge : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)

    A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

(* To avoid re-defining subseq relation, use list nat instead of list X, but the proof should be same *)
Theorem filter_challenge2 : forall (l l' : list nat) (test : nat -> bool) , (subseq l' l) -> (forall x, In x l' -> test x = true)
  -> length l' <= length (filter test l).
Proof.
  intros. generalize dependent l'.
  induction l; intros.
  - inversion H. simpl. lia.
  - inversion H; subst.
    + simpl. specialize (IHl l' H3 H0). destruct (test x); simpl; lia.
    + simpl. 
      specialize (sublist_holds_P nat x ls1 (fun x => test x = true) H0) as Ht.
      specialize (IHl ls1 H3 Ht).
      specialize (H0 x (In_cons nat x ls1)). rewrite H0. simpl. lia.
Qed. 

(** **** Exercise: 4 stars, standard, optional (palindromes)

    A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

Inductive pal {X:Type} : list X -> Prop :=
| pal_zero : pal []
| pal_one (x : X) : pal [x]
| pal_add (x : X) (ls : list X) (H : pal ls) : pal ([x] ++ ls ++ [x])
.

(* A failed but insteresting try 

Fixpoint take_not_last X (ls : list X) : list X :=
  match ls with
  | [] => []
  | [x] => []
  | x::ls' => x :: take_not_last X ls'
  end.

Locate "{ _ : _ | _ }".

Lemma zgtz : 0 > 0 -> False.
Proof. intros. inversion H.  Qed.

Check proj1_sig.

(* Fixpoint take_last X (l : list X) {struct l}: length l > 0 -> X.
refine (
  match l return length l > 0 -> X with 
  | [] => fun pf : 0 > 0 => match zgtz pf with end
  | [x] => fun _ => x
  | x::y::ls => fun _ => take_last X (y::ls) _
  end).
  simpl. lia.
Fail Defined. *)

Definition take_middle X (ls : list X) : list X :=
  match ls with 
  | [] => []
  | [x] => []
  | x::y::ls' => take_not_last X ls'
  end.

Definition list_ind2:
  forall X (P : list X -> Prop),
    P [] ->
    (forall x, P [x]) ->
    (forall x y ls, P ls -> P ([x] ++ ls ++ [y])) ->
    forall (ls : list X), P ls.
Proof.
  intros. 
      fun X => fun P => fun P0 => fun P1 => fun Pss => 
        fix f (ls : list X) := match ls with 
                               | [] => P0
                               | [x] => P1 x
                               | x :: y :: ls => Pss x y (take_middle X ls) (f (take_middle X ls))
        end. 

*)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_pal_pal_app_rev_pal_rev : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (palindrome_converse)

    Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

Lemma pal_converse': forall X len (l:list X), length l <= len -> l = rev l -> pal l.
Proof.
  intros X len.
  induction len; intros.
  - destruct l. constructor. inversion H.
  - destruct l. constructor. simpl in *.
      destruct (rev l) eqn:Heqrevl.
      + rewrite H0. constructor.
      + inversion H0. constructor.
        apply Sn_le_Sm__n_le_m in H.
        assert (length l = length (l0 ++ [x0])). { rewrite H3. auto. }
        rewrite app_length in H1. 
        simpl in H1.
        assert (length l0 <= len). { lia. }
        specialize (IHlen l0 H4).
        apply IHlen.
        rewrite H3 in Heqrevl.
        rewrite rev_app_distr in Heqrevl.
        simpl in Heqrevl.
        inversion Heqrevl.
        rewrite H6 at 2. auto.
Qed.

Lemma pal_converse: forall X (l:list X), l = rev l -> pal l.
Proof.
  intros.
  eapply pal_converse'; eauto.
Qed.

(** **** Exercise: 4 stars, advanced, optional (NoDup)

    Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)


(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

Inductive disjoint (X : Type) : list X -> list X -> Prop :=
| disj_nil    : disjoint X [] []
| disj_cons_l : forall (l1 l2 : list X) (x : X),
                ~ In x l2 -> 
                  disjoint X l1 l2 -> disjoint X (x :: l1) l2
| disj_cons_r : forall (l1 l2 : list X) (x : X),
                ~ In x l1 -> 
                  disjoint X l1 l2 -> disjoint X l1 (x :: l2).
(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

Inductive NoDup (X : Type) : list X -> Prop :=
| nodup_nil    : NoDup X []
| nodup_app (x : X) (l : list X) (H1 : ~ In x l) (H2 : NoDup X l) : NoDup X (x :: l).

Lemma disjoint_nil_l : forall X (l : list X), disjoint X [] l.
Proof.
  induction l.
  - constructor. 
  - constructor; auto.
Qed.

Lemma disjoint_nil_r : forall X (l : list X), disjoint X l [].
Proof.
  induction l.
  - constructor. 
  - constructor; auto.
Qed.

Lemma disjoint_sub_l: forall X (x: X) (l1 l2 : list X), disjoint X (x :: l1) l2 -> disjoint X l1 l2.
Proof.
  intros.
  generalize dependent x. generalize dependent l1.
  induction l2; intros.
  - eapply disjoint_nil_r.
  - induction l1.
    + eapply disjoint_nil_l.
    + inversion H; subst.
      * auto.
      * specialize (IHl2 (x1::l1) x0 H4).
        apply disj_cons_r.
        -- unfold not. intros. assert (In x (x0 :: x1 :: l1)). 
        { replace (x0 :: x1 :: l1) with ([x0] ++ (x1 :: l1)). apply In_app_iff. right. assumption. auto. } contradiction.
        -- auto.
Qed.


Lemma disjoint_sub_r: forall X (x: X) (l1 l2 : list X), disjoint X l1 (x :: l2) -> disjoint X l1 l2.
Proof.
  intros.
  generalize dependent x. generalize dependent l2.
  induction l1; intros.
  - eapply disjoint_nil_l.
  - induction l2.
    + eapply disjoint_nil_r.
    + inversion H; subst.
      * specialize (IHl1 (x1::l2) x0 H4).
        apply disj_cons_l.
        -- unfold not. intros. assert (In x (x0 :: x1 :: l2)). 
        { replace (x0 :: x1 :: l2) with ([x0] ++ (x1 :: l2)). apply In_app_iff. right. assumption. auto. } contradiction.
        -- auto.
      * auto.
Qed.

Lemma disjoint_one : forall X (x: X) (l1 l2 : list X), disjoint X (x::l1) l2 -> ~ In x l2.
Proof.
  intros. generalize dependent x. generalize dependent l1.
  induction l2; intros.
  - unfold not. intros. inversion H0. 
  - unfold not. intros.
  inversion H; subst.
  + contradiction.
  + unfold not in H4.
    replace (x::l2) with ([x] ++ l2) in H0. apply In_app_iff in H0. inversion H0.
    * inversion H1.
      -- subst. assert (In x0 (x0::l1)). {  
        replace (x0::l1) with ([x0] ++ l1).
        apply In_app_iff. left. auto. auto.
      } 
      apply H4 in H2. contradiction.
      -- inversion H2.
    * specialize (IHl2 l1 x0 H5). contradiction.
    * auto.
Qed.


(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)
Theorem disjoint_app_nodup : forall X (l1 l2 : list X), NoDup X l1 -> NoDup X l2 -> disjoint X l1 l2 -> NoDup X (l1 ++ l2).
Proof.
  intros. generalize dependent l2.
  induction H; intros.
  - auto.
  - simpl. constructor.
    + unfold not. intros. apply In_app_iff in H3.
      inversion H3.
      * contradiction.
      * specialize (disjoint_one X x l l2 H2).
        unfold not. intros. contradiction.
    + apply IHNoDup; auto.
      eapply disjoint_sub_l. eauto. 
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle)

    The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy and useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros.
  induction l; inversion H.
  - subst x0. exists [], l. auto.
  - apply IHl in H0. destruct H0 as [l1 [l2]].
    exists (x0::l1), l2. rewrite H0. auto. 
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
| rp_base: forall x l, In x l -> repeats (x::l)
| rp_next: forall x l, repeats l -> repeats (x::l)
.

(* Do not modify the following line: *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: excluded_middle ->
  forall (X:Type) (l1 l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1. induction l1 as [|x l1' IHl1'].
  - intros. inversion H0.
  - intros. specialize (EM (In x l1')) as Hxinl1'. 
    inversion Hxinl1'. 
    + apply rp_base. auto.
    + apply rp_next. destruct (in_split X x l2).
      * apply H. apply In_cons.
      * destruct H2 as [l3 Heql2]. subst. 
        apply IHl1' with (l2:=x0 ++ l3).
        -- intros. specialize (EM (x = x1)) as Hxeqx1.
           inversion Hxeqx1.
           ++ subst. contradiction. 
           ++ assert (In x1 (x0 ++ x :: l3) -> In x1 (x0 ++ l3)).
              { intros. apply In_app_iff in H4. inversion H4.
                + apply In_app_iff. left. auto.
                + replace (x :: l3) with ([x] ++ l3) in H5. apply In_app_iff in H5. inversion H5.
                * simpl in H6. inversion H6. contradiction. inversion H7.
                * apply In_app_iff. right. auto.
                * auto.
              }
              apply H4. apply H. replace (x :: l1') with ([x] ++ l1').
              apply In_app_iff. right. auto. auto.
        -- rewrite app_length in H0. rewrite app_length. simpl in *. lia.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match automatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function that reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)
Require Import Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne)

    [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([ ] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros. split; intros.
  - inversion H. subst.
    induction s1; intros.
    + left; split; subst; auto.
    + right. inversion H1. subst. exists s1, s2. all : split_all; auto. 
  - inversion H. 
    + inversion H0. replace (a::s) with ([] ++ (a :: s)). constructor; auto. auto.
    + destruct H0 as [s0 [s1 [Heq [Hmre0 Hmre1]]]].
      replace (a::s) with ((a::s0) ++ s1). constructor; auto. rewrite Heq. app_assoc_eq.
Qed.
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
  s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne)

    [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)
Check exp_match_ind.

Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  intros. split; intros.
  - remember (Star re) as re'. remember (a::s) as s'. induction H; try discriminate.
    + destruct s1.
      * simpl in Heqs'. eapply IHexp_match2; auto.
      * inversion Heqs'. inversion Heqre'. subst.
        exists s1, s2. all : split_all; auto. 
  - destruct H as [s0 [s1 [Heq [Hmre Hmstarre]]]].
    replace (a :: s) with ((a :: s0) ++ s1). constructor; auto. rewrite Heq. auto.
Qed.
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps)

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: reg_exp ascii) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => false
  | App re1 re2 => andb (match_eps re1) (match_eps re2)
  | Union re1 re2 => orb (match_eps re1) (match_eps re2)
  | Star re => true
  end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl)

    Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps. intros.
  destruct (match_eps re) eqn:Hmepsre.
  - apply ReflectT. induction re; inversion Hmepsre.
    + constructor.
    + apply andb_true_iff in H0. inversion H0.
      replace ([]) with (@app ascii [] []). constructor; auto. auto.
    + apply union_disj. apply orb_true_iff in H0. inversion H0.
      * left. auto.
      * right. auto.
    + constructor.
  - apply ReflectF. induction re; inversion Hmepsre; unfold not; 
    intros contra; inversion contra.
    + destruct s1; destruct s2; inversion H1.
      apply andb_false_iff in H0. inversion H0. 
      * apply IHre1 in H5. contradiction.
      * apply IHre2 in H5. contradiction.
    + apply orb_false_iff in H0; inversion H0.
      apply IHre1 in H4. contradiction.
    + apply orb_false_iff in H0; inversion H0.
      apply IHre2 in H5. contradiction.
Qed.

Lemma match_eps_refl' : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps. intros.
  apply iff_reflect. split; intros.
  - remember ([]) as s. induction H; try discriminate; auto.
    + destruct s1; destruct s2; inversion Heqs.
      simpl. specialize (IHexp_match2 (eq_refl [])). specialize (IHexp_match1 (eq_refl [])). 
      rewrite IHexp_match1. rewrite IHexp_match2. auto.
    + simpl. apply orb_true_iff. left. apply IHexp_match. auto.
    + simpl. apply orb_true_iff. right. apply IHexp_match. auto.
  -
    induction re; inversion H; try solve constructor.
    + constructor.
    + replace ([]) with (@app ascii [] []). 
      apply andb_true_iff in H1. inversion H1. constructor; auto.
      auto.
    + apply orb_true_iff in H1.
      inversion H1. 
      apply MUnionL; auto.
      apply MUnionR; auto.
    + constructor.
Qed.

(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive)

    Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char x => if (eqb a x) then EmptyStr else EmptySet
  | App re1 re2 => if (match_eps re1) 
                   then
                     (Union (App (derive a re1) re2) (derive a re2)) 
                   else App (derive a re1) re2
  | Union re1 re2 => Union (derive a re1) (derive a re2)
  | Star re' => App (derive a re') re
  end.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  auto. Qed.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  auto. Qed.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  auto. Qed.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  auto. Qed.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  auto. Qed.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  auto. Qed.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  auto. Qed.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  auto. Qed.

(** **** Exercise: 4 stars, standard, optional (derive_corr)

    Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)

Ltac reflect_transform H re := 
  match goal with 
  H1 : refl_matches_eps match_eps
  |- _ => specialize (H1 re); apply reflect_iff in H1; apply H1 in H; auto
  end.

Lemma derive_corr : derives derive.
Proof.
  specialize match_eps_refl. intros Hreflmeps.
  unfold derives. intros. generalize dependent a.
  induction re; unfold is_der in *; intros.
  - split; intros; try inversion H.
  - split; intros; try inversion H.
  - split; intros; specialize (ascii_dec a t) as Hateqdec; intros; destruct Hateqdec as [Hateq | Hatneq].
    + subst. inversion H. simpl. rewrite eqb_refl. constructor.
    + inversion H. contradiction.
    + subst. simpl in H. rewrite eqb_refl in H. inversion H. constructor.
    + simpl in H. apply eqb_neq in Hatneq. rewrite Hatneq in H. inversion H.
  - split; intros. 
    + apply app_ne in H. inversion H.
      * destruct H0 as [Hmre1 Hmre2].
        pose proof Hmre1 as Hmre1t. reflect_transform Hmre1t re1. simpl.
        rewrite Hmre1t. apply MUnionR. replace s with ([] ++ s). apply IHre2; auto. auto.
      * destruct H0 as [s0 [s1 [Heqs [Hmre1 Hmre2]]]].
        simpl. destruct (match_eps re1).
        -- apply MUnionL. rewrite Heqs. constructor. apply IHre1; auto. auto.
        -- rewrite Heqs. constructor. apply IHre1; auto. auto.
    + simpl in H. 
      assert (Happd : s =~ App (derive a re1) re2 -> a :: s =~ App re1 re2). {
        intros.
        apply app_exists in H0.
        destruct H0 as [s0' [s1' [Heqs [Hmre1 Hmre2]]]].
        replace (a :: s) with ((a :: s0') ++ s1'). constructor; auto.
        ++ apply IHre1 in Hmre1. auto.
        ++ rewrite Heqs. app_assoc_eq.
      }
      destruct (match_eps re1) eqn:Hre1meps.
      * inversion H.
        -- apply Happd. auto.
        -- replace (a :: s) with ([] ++ (a :: s)).
        constructor.
        ++ reflect_transform Hre1meps re1. 
        ++ apply IHre2. auto.
        ++ auto.
      * apply Happd. auto.
  - split; intros. 
    + inversion H; simpl.
      apply MUnionL. apply IHre1. auto.
      apply MUnionR. apply IHre2. auto.
    + simpl in H. inversion H.
      apply MUnionL. apply IHre1. auto.
      apply MUnionR. apply IHre2. auto.
  - split; intros.
    + apply star_ne in H.
      destruct H as [s0 [s1 [Heqs [Hmre1 Hmre2]]]].
      simpl. rewrite Heqs. constructor.
      apply IHre. auto. auto.
    + simpl in H.
      apply app_exists in H.
      destruct H as [s0 [s1 [Heqs [Hmre1 Hmre2]]]].
      apply IHre in Hmre1.
      rewrite Heqs. replace (a :: s0 ++ s1) with ((a::s0) ++ s1). constructor; auto.
      app_assoc_eq.
Qed.


(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(** A function [m] matches regexes if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match)

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool :=
  match s with
  | a :: s' => regex_match s' (derive a re)
  | [] => match_eps re
  end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_refl)

    Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)


Theorem regex_refl : matches_regex regex_match.
Proof.
  specialize derive_corr. specialize match_eps_refl. unfold derives. unfold is_der.
  unfold matches_regex. intros Hmeps Hdc. intros. 
  apply iff_reflect. split; intros; generalize dependent re; induction s; intros.
  - simpl. reflect_transform H re.
  - simpl. apply Hdc in H. apply IHs. auto.
  - simpl in H. reflect_transform H re.
  - apply Hdc. simpl in H. apply IHs. auto.
Qed.
(** [] *)

(* 2021-08-11 15:08 *)
