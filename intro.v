(** * Introduction

    Programming is a hard task, and writing correct programs is even
    harder, as any person having tried to write one can attest. A few
    factors contribute to this state of affairs.

    First, in order to write a correct program, we must first
    understand what "correct" means -- that is, what a particular
    program is supposed to do. Unfortunately, interesting programs
    have complex specifications, which are almost never stated
    completely. If we don't have a clear idea of what the purpose of a
    program is, it is less likely that we will be able to write a
    correct implementation.

    Second, even with a complete, precise specification in hand, it is
    not easy to see whether an implementation conforms to
    it. Programmers convince themselves of this by using the program
    in controlled trials, by running extensive testing, or with tool
    support. These techniques can lead to a dramatic increase in
    software quality, but often fail to detect subtle mistakes that
    end up appearing after the program is deployed.

    Many tools and methodologies have been introduced to try to solve
    these two problems. Among those, we can mention a particularly
    interesting class: _proof assistants_. Proof assistants allow
    programmers to write spefications and connect them to programs via
    _machine-checked proofs_. If a programmer can formulate a
    logically sound argument for why their program is correct, the
    proof assistant will agree and tell them so. Otherwise, if the
    argument contains any flaws, the proof assistant will notice it
    and report to the programmer.

    This document is an introduction to Coq, a powerful proof
    assistant. Coq comes with a rich language for writing programs,
    specifications, and mathematical concepts, and connecting them
    with formal proofs. Coq has been successfully applied to the
    verification of complex programs, including compilers and
    operating systems, and also used to formalize important
    mathematical results, such as the four-color theorem or the
    odd-order theorem.

    Coq is a complex system that includes many features, and the Coq
    community has developed many styles for using it. In this
    introduction, we will focus on _ssreflect_, a Coq library that has
    its own set of best practices.


    * First steps

    Most of the time, Coq is used interactively within a specialized
    programming environment: while the user is working on a Coq
    development, the system is giving feedback on what definitions and
    proofs are acceted or rejected, which results can be used to prove
    a certain claim, etc. The most widely used environments for
    interacting with Coq are _CoqIDE_, a stand-alone editor that is
    part of the official Coq distribution, and _Proof General_, an
    Emacs plugin. *)

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.

(** These commands turn on options that make programming in Coq a bit
    easier; it is usually a good idea to include those at the
    beginning of your files. The first two allow us to omit arguments
    that can be automatically inferred by Coq (usually, type
    parameters for polymorphic functions); the last one instructs
    Coq's printer to omit these arguments when printing terms. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** As a first example, we will use Coq to implement and verify
    red-black-tree operations for building an abstract data type of
    sets.

    To make our code simpler, we enclose our basic definitions in a
    Coq section. The [Variable] command below declares a type variable
    [T] that will be in scope throughout the entire [Def] section. *)

Section Def.

Variable T : Type.

(** The [Inductive] command declares new data types; its syntax and
    meaning are similar to definitions of algebraic data types in
    languages such as Haskell and OCaml. Each declaration contains a
    list of values that specify how to form elements of that data
    type; each such value is called a _constructor_. For instance,
    here is how we define a data type [color] consisting of two
    elements: [Red] and [Black]. *)

Inductive color : Type :=
| Red
| Black.

(** The above definition adds three new constants to our environment:
    [color], [Red], and [Black]. Every valid expression in Coq has a
    type; we can ask Coq what the type of these three new constants is
    with the [Check] command. For instance: *)

Check Red.
Check Black.

(** It is usually preferable to avoid including [Check] commands in
    Coq files, since they only make sense interactively; we add them
    here for explanation purposes. You can avoid writing [Check] when
    using Coq interactively by issuing the appropriate command in your
    Coq environment. In ProofGeneral, for instance, you can hit [C-c
    C-a C-c].

    Constructors of inductive data types can take arguments, which can
    include elements of the type being defined. The next declaration
    defines a red-black tree data type. These are binary trees whose
    internal nodes contain elements of [T] and are colored either
    [Red] or [Black]. *)

Inductive tree : Type :=
| Leaf
| Node of color & tree & T & tree.

(** [Leaf] is a constructor that takes no arguments, as the [Red] and
    [Black] constructors of [color]. [Node], on the other hand, takes
    four arguments: a [color], a [tree], a [T], and another
    [tree]. The [of] and [&] symbols are part of ssreflect. Here is
    what the previous declaration would look like in usual Coq syntax:
    *)

Inductive tree' : Type :=
| Leaf' : tree'
| Node' : color -> tree' -> T -> tree' -> tree'.

(** We have replaced the type and constructor names above to avoid
    clashes, but the two declarations are otherwise equivalent.

    We can define other values and functions with the [Definition]
    command. For instance: *)

Definition singleton (x : T) : tree :=
  Node Red Leaf x Leaf.

(** The above declaration defines a function [singleton] that takes
    one argument, an element [x] of [T]. Its result is a [tree]
    consisting of one internal node colored [Red] that contains
    [x]. As the example above shows, we apply a constructor to
    arguments by writing them in order, separated by spaces (as in
    Haskell). This is also the same syntax for function
    application. For instance: *)

Definition three_times (x : T) : tree :=
  Node Red (singleton x) x (singleton x).

(** Note that the above definitions have type annotations in them. We
    usually don't have to supply them, since Coq can infer them most
    of the time: *)

Definition three_times' x := three_times x.

(** Nevertheless, it is often a good idea to do so, since it can
    improve readability and serve as good documentation.

    We define recursive functions using the [Fixpoint] command. For
    instance, here is a function [tsize] that computes the number of
    elements stored in a tree: *)

Fixpoint tsize (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node _ t1 _ t2 => tsize t1 + 1 + tsize t2
  end.

(** The type [nat] type is the type of natural numbers -- that is, all
    non-negative integers. The [ssrnat] library of ssreflect comes
    with many predefined functions on them, including addition,
    multiplication, subtraction, etc. Natural numbers are used
    extensively in Coq developments.

    Here is another recursive function: one for mirroring the tree. *)

Fixpoint tmirror (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node c t1 x t2 => Node c (tmirror t2) x (tmirror t1)
  end.

(** * Proof by simplification

    After writing simple programs in Coq's functional language, let's
    turn our attention to stating and proving properties about these
    programs. For example, we might want to claim that [singleton x]
    has size [1] for all possible values of [x]. In Coq, this is done
    with the [Lemma] command: *)

Lemma tsize1 (x : T) : tsize (singleton x) = 1.

(** By issuing this commmand, we declare that we want to prove a lemma
    called [tsize1], whose statement is a direct translation of the
    above claim. This causes Coq to enter _proof mode_, where it
    expects us to provide a proof for that statement. We can now see a
    new window which displays the current state of our proof. This
    window is split by a horizontal line. Below that line is the
    _goal_, which says what else remains to be proved; above that line
    is a list of local variables and hypotheses. Proofs are written
    with special commands called _tactics_. Each tactic transforms the
    goal a little bit, applying inference steps that (hopefully) bring
    us towards a state where our claim becomes obvious enough to be
    accepted by Coq. Coq checks each argument that we try to enter
    according to the rules of its logic, rejecting any invalid
    proofs. This ensures that, whenever a proof is accepted by Coq, we
    can have a high degree of confidence that it is correct.

    We start proofs with the [Proof] command: *)

Proof.

(** Our first tactic is [rewrite /=], which attempts to simplify the
    current goal according to the computation rules of Coq's logic. *)

rewrite /=.

(** We can see that [rewrite /=] replaced [tsize (singleton x) = 1] by
    [0 + 1 + 0 = 1]. At this point, the statement is obvious enough
    that Coq can accept that it is true without further help. We can
    complete the proof with the [done] tactic: *)

done.

(** Coq now tells us that there are no more subgoals, which means that
    our proof is complete. The [Qed.] command causes Coq to exit proof
    mode once the proof is complete. *)

Qed.

(** We can now refer to the theorem we just proved by its name. The
    [forall] annotation given in the statement of the checked lemma
    means (as you may guess) that [x] is universally quantified and
    may be instantiated arbitrarily. *)

Check tsize1.

(** Calling [done] after a tactic is so common that ssreflect offers
    special syntax for it: if [t] is a tactic, then [by t] tries to
    execute [t] and to conclude the proof afterwards by calling
    [done]. If the proof cannot be complete, Coq raises an error. *)

Lemma tsize1' (x : T) : tsize (singleton x) = 1.
Proof. by rewrite /=. Qed.

(** As a matter of fact, the above proof is so simple that we don't
    even need to tell Coq to simplify the goal; [done] alone
    suffices. Alternatively, we can also write [by []] (that is, [by]
    with an "empty" first tactic) as a synonym of [done]: *)

Lemma tsize1'' (x : T) : tsize (singleton x) = 1.
Proof. done. Qed.

Lemma tsize1''' (x : T) : tsize (singleton x) = 1.
Proof. by []. Qed.

(** Before we move on to more interesting proofs, it is worth leaving
    a small note on naming conventions: ssreflect tries to follow very
    consistent naming conventions for its lemmas, which we will try to
    emulate here. The [1] suffix on [tsize1], for instance, signals
    that this lemma relates [tsize] to something of size [1]; in this
    case, a singleton tree. We will point to other naming conventions
    as we progress.


    * Proof by case analysis

    Often, simplification is not enough to complete a proof. For
    instance, suppose that we have the following function [tcolor]
    which computes the color of the root of a tree (by convention,
    empty trees are colored black): *)

Definition tcolor (t : tree) : color :=
  match t with
  | Leaf => Black
  | Node c _ _ _ => c
  end.

(** Clearly, the [tmirror] function defined above does not change the
    color of the tree it is applied to. Let's try to convince Coq of
    this fact: *)

Lemma tcolor_tmirror (t : tree) : tcolor (tmirror t) = tcolor t.
Proof.

(** We can try to simplify the goal, but Coq won't be able to make any
    progress. We can also try to use [done], to see if Coq accepts
    this fact on its own, but it raises an error instead: *)

rewrite /=. (* Nothing happens... *)
(* done. *) (* Cannot finish the proof. *)

(** The reason why simplification worked on the previous example, but
    cannot make any progress here, is that Coq knew exactly what shape
    the result of [singleton] has, because its definition started with
    a [Node] constructor. In the current lemma, however, we are trying
    to prove something about an _arbitrary_ tree [t], without any
    further information about what [t] is. What we need is a way to
    consider all possible forms that [t] can have, which we can
    accomplish with the [case] tactic: *)

case: t.

(** The [case: t] call instructs Coq to do a proof by cases. The proof
    state now shows that we need to complete two subgoals: one where
    [t] is replaced by [Leaf], and another one where it is replaced by
    a tree that starts with the [Node] constructor. We can proceed by
    proving each of the subgoals in sequence. Following the ssreflect
    convention, we indent the proof of the first subgoal by two
    spaces. Its proof follows by simplification. *)

  rewrite /=.
  by [].

(** The second subgoal looks a little bit different: besides not
    mentioning [t] anymore, our goal now contains additional
    universally quantified variables, the arguments to the [Node]
    constructor. We can introduce these variables, bringing them from
    the goal into the context by using the [move]: *)

move=> c t1 x t2.

(** Each name given after the [=>] operator is used to name one
    universally quantified variable present in the goal. We can now
    simplify our goal as before and conclude. *)

rewrite /=.
by [].
Qed.

(** Ssreflect allows us to combine some of these steps into a single
    tactic. For instance, we can use [case] to name all constructor
    arguments and perform a simplification automatically, like this: *)

Lemma tcolor_tmirror' (t : tree) : tcolor (tmirror t) = tcolor t.
Proof.
case: t => [|c t1 x t2] /=.

(** The pattern enclosed by square brackets in the above tactic names
    the arguments resulting from each constructor of [tree]. In the
    general case, each group of variables separated by [|] corresponds
    to one constructor. Since the [Leaf] constructor doesn't take any
    arguments, its corresponding part in the pattern doesn't contain
    any variables.

    The [/=] symbol tells Coq to attempt to simplify the goal _after_
    doing case analysis on [t]. We can see that the resulting goals
    can be solved immediately: *)

  by [].
by [].
Qed.

(** As a matter of fact, we didn't even have to name the constructor
    arguments, since the [done] tactic is smart enough to do this by
    itself. *)

Lemma tcolor_tmirror'' (t : tree) : tcolor (tmirror t) = tcolor t.
Proof. by case: t. Qed.

(** Of course, in many cases we _do_ have to perform non-trivial
    reasoning steps after calling [case]. We will encounter many
    examples of such proofs as we make progress.


    * Proof by rewriting

    So far, we have done simple proofs showing that certain equations
    between two expressions hold. We can also use these equations in
    other proofs to show more results. This process is known as
    _rewriting_.

    The [rewrite] tactic can be used not only with the [/=] symbol,
    which performs simplification by computation, but also with any
    previously proved equation. As a simple example, we can try to
    prove the following variant of [tcolor_tmirror]: *)

Lemma tcolor_tmirror2 (t : tree) : tcolor (tmirror (tmirror t)) = tcolor t.
Proof.

(** This result is simple enough that a single call to [case] would
    suffice to solve it, as in [tcolor_tmirror]. However, we can take
    a slightly different approach, using [tcolor_tmirror] instead to
    rewrite on the left-hand side of the equation. *)

rewrite tcolor_tmirror.
rewrite tcolor_tmirror.
by [].
Qed.

(** As we can see, each call to [rewrite] instantiated the
    [tcolor_tmirror] lemma with a different tree value, successively
    removing calls to [tmirror]. In the first rewrite, the tree value
    was instantiated to [tmirror t], while in the second one, it was
    instantiated with [t] itself. Coq performs unification to find out
    how to instantiate each lemma given to [rewrite], but we can also
    explicitly instantiate our lemma by passing the value we want to
    use as an argument to the theorem. This is useful when there are
    multiple possible instantiations and Coq doesn't choose the one we
    want by itself. *)

Lemma tcolor_tmirror2' t : tcolor (tmirror (tmirror t)) = tcolor t.
Proof.
rewrite (tcolor_tmirror (tmirror t)).
rewrite (tcolor_tmirror t).
by [].
Qed.

(** It is also possible to perform several rewrite steps at once: *)

Lemma tcolor_tmirror2'' t : tcolor (tmirror (tmirror t)) = tcolor t.
Proof. by rewrite tcolor_tmirror tcolor_tmirror. Qed.

(** Alternatively, we can use the [!] flag to rewrite with a lemma as
    many times as possible: *)

Lemma tcolor_tmirror2''' t : tcolor (tmirror (tmirror t)) = tcolor t.
Proof. by rewrite !tcolor_tmirror. Qed.

(** * Proof by induction

    Coq is not smart enough to come up with its own inductive
    proofs. These are done with the [elim] tactic.

    At its simplest form, [elim] is just a more powerful version of
    [case] that generates induction hypothesis for structurally
    smaller terms. Here's an example. Suppose that we wanted to show
    that [tmirror] is its own inverse. *)

Lemma tmirrorK t : tmirror (tmirror t) = t.
Proof.

(** The [K] suffix in the name of this lemma stands for
    "cancellation", and is a convention used by ssreflect to name
    similar results.

    As with [case], when we call [elim: t], we get to provide names
    for the arguments of each constructor. The difference is that
    every recursive argument also generates an induction hypothesis,
    saying that the result we are trying to prove is valid for that
    argument. Thus, in the tactic below, [IH1] and [IH2] stand for the
    induction hypotheses that correspond to [t1] and [t2]. Notice that
    we use the [/=] flag to simplify both subgoals. *)

elim: t => [|c t1 IH1 x t2 IH2] /=.

(** The first subgoal corresponds to the [t = Leaf] case, and can be
    solved by Coq automatically. *)

  by [].

(** When attacking the second subgoal, where [t] has the form [Node c
    t1 x t2], we can see that our context looks a bit
    different. Besides the usual arguments, it also contains the
    induction hypotheses [IH1] and [IH2], which state that [tmirror
    (tmirror t1) = t1] and [tmirror (tmirror t2) = t2]. To conclude
    this subgoal, we can rewrite with these hypotheses, as if they
    were normal lemmas: *)

rewrite IH1 IH2.

(** Now, both sides of the equation are equal, and Coq accepts our proof. *)

by [].
Qed.

(** Ssreflect provides nice syntax for simplifying this proof. Since
    many cases in a proof follow directly by simplification, we can
    use the [//] flag with [elim] to tell Coq to try to close all
    goals it can with the [done] tactic. *)

Lemma tmirrorK' t : tmirror (tmirror t) = t.
Proof.
elim: t => [|c t1 IH1 x t2 IH2] // /=.
by rewrite IH1 IH2.
Qed.

(** Both [//] and [/=] can be combined in a single flag, [//=]. *)

Lemma tmirrorK'' t : tmirror (tmirror t) = t.
Proof.
elim: t => [|c t1 IH1 x t2 IH2] //=.
by rewrite IH1 IH2.
Qed.

(** We can further condense this proof by performing some of the
    rewriting steps directly after calling [elim]. When [->] is given
    as a name for a hypothesis, this tells Coq to try to rewrite with
    that hypothesis. This leads to the following proof: *)

Lemma tmirrorK''' t : tmirror (tmirror t) = t.
Proof. by elim: t => [|/= c t1 -> x t2 ->]. Qed.

(** Notice that, before rewriting with the induction hypotheses in the
    [Node] branch, we perform a simplification step with [/=], so that
    Coq can find the terms [tmirror (tmirror t1)] and [tmirror
    (tmirror t2)] in the goal.


    * Propositions are first-class values

    One interesting aspect of Coq's theory is that propositions are
    first-class values that can be manipulated according to the same
    rules that are used for other objects of the language. In
    particular, since Coq is a _typed_ language, all propositions have
    a type: [Prop]. For instance: *)

Check 1 = 1.

(** Note that being a syntatically well-formed proposition does not
    imply that this proposition is true. Hence, [0 = 1] also has type
    [Prop], even though it corresponds to a false claim. *)

Check 0 = 1.

(** Coq comes with a rich language for writing propositions. So far,
    we have encountered the equality operator [=], and universal
    quantification [forall], but there are many more. We will
    introduce more of them as we go along.

    We can define functions that return propositions, allowing us to
    develop convenient abbreviations for common patterns.

    As an example, we can define a function [cancel] that takes in two
    functions [f] and [g] as arguments, and states that [g] is the
    left inverse of [f]. Since [cancel] is already provided by
    ssreflect, we restate the definition here with a different name,
    to avoid clashes. *)

Definition cancel' (S R : Type) (f : S -> R) (g : R -> S) : Prop :=
  forall x : S, g (f x) = x.

(** Notice that the [S] and [R] types are explicitly given as
    arguments to [cancel]. However, because of the "implicit
    arguments" option we enabled at the beginning of the file, we
    don't have to provide them most of the time. For instance: *)

Lemma tmirrorK'''' : cancel tmirror tmirror.
Proof.

(** To understand what's going on, it is sometimes useful to unfold
    the definition of [cancel]. Simplification by default does not
    perform this kind of unfolding, because it would create bigger and
    harder-to-understand proof contexts. To unfold a term [foo], we
    use the [/foo] rewrite flag. For instance (even though it won't
    affect the rest of the proof): *)

rewrite /cancel.

(** Since [cancel] has an explicitly quantified variable [x] in its
    definition, we need to bring it into the context, much like we did
    after doing case analysis. Of course, we can give [x] any name we
    like: *)

move=> t.
by elim: t => [|/= c t1 -> x t2 ->].
Qed.

(** In situations like this, where we want our tactic to act on the
    first quantified value on the goal, we can just call that tactic
    directly, without having to introduce that value directly. In
    other words, tactics such as [case] and [elim] always act
    implicitly on the first universally quantified value in our goal,
    in stack-like fashion. *)

Lemma tmirrorK''''' : involutive tmirror.
Proof. by elim=> [|/= c t1 -> x t2 ->]. Qed.

(** Notice that we have used [involutive tmirror] instead of [tcancel
    tmirror tmirror]. [involutive foo] is defined exactly as [cancel
    foo foo].

    The reason we wrote [: t] on previous calls to [elim] is simple:
    the [:] is actually a tactic operator, whose effect is to put some
    variables in the context back in the goal. In this sense, it is
    the inverse of the [=>] introduction operator. For instance: *)

Lemma tmirrorK'''''' : involutive tmirror.
Proof.
move=> t.
move: t.
Abort.

(** * Using previous results

    Coq and ssreflect come with many definitions and lemmas about
    them. In order to make effective use of Coq, it is important to
    know how to reuse this infrastructure. Here is a simple
    example. Suppose that we wanted to prove that mirroring a tree
    does not change its size. *)

Lemma tsize_tmirror t : tsize (tmirror t) = tsize t.
Proof.

(** We could try to prove this by induction: *)

elim: t => [|/= c t1 -> x t2 ->] //.

(** Here, we see that Coq was able to discharge the base case by
    itself, with [//]. However, it was not able to get rid of the
    second one. Indeed, we can see that the order of the summands on
    both sides is different:

    [tsize t2 + 1 + tsize t1 = tsize t1 + 1 + tsize t2]

    Unfortunately, ssreflect's [done] tactic does not perform this
    kind of arithmetic reasoning by itself, and we must find previous
    results that will allow us to show that these two terms are
    equal. Coq comes with a [SearchAbout] command that can be used for
    looking up lemmas that mention certain definitions. In this case,
    we want to be able to argue about commutativity and associativity
    of [+]. As it turns out, ssreflect already these notions for us: *)

Print commutative. (* [C-c C-a C-p] in Proof General *)
Print associative.

(** We can then try to use [SearchAbout] to find lemmas that may help
    us here. *)

SearchAbout "+" commutative. (* [C-c C-a C-a] in Proof General *)
SearchAbout "+" associative.

(** Running these commands shows us that there are two lemmas, [addnC]
    and [addnA], that we can use. You will notice that both lemmas
    mention a function [addn] instead of the [+] operator. Coq comes
    with a notation mechanism for changing the syntax of certain
    constructs. Thus, natural number addition is actually defined as a
    function [addn], and only later we issue a [Notation] command for
    using the nice infix syntax. Notice also that we had to enclose
    [+] in quotes so that Coq can understand that we are referring to
    a notation as opposed to a normal identifier. We will not discuss
    the details of the [Notation] command right now, though, as it is
    a bit complicated to explain. *)

by rewrite addnC (addnC _ 1) addnA.
Qed.

Fixpoint tree_elems (t : tree) : seq T :=
  match t with
  | Leaf => [::]
  | Node c t1 x t2 => tree_elems t1 ++ x :: tree_elems t2
  end.

(** Our definition says that, when called on the empty tree [Leaf],
    [tree_elems] returns the empty sequence, which is denoted by
    [[::]]. When called on a non-empty tree of the form [Node c t1 x
    t2], [tree_elems] constructs a sequence that contains elements of
    [t1], then [x], then all elements of [t2]. This definition uses
    basic operations provided by the ssreflect [seq] library. The [seq
    T] type is the type of finite sequences (or lists) of elements of
    [T]; [++] is the sequence concatenation operator; and [::] is the
    _cons_ operator, which adds an element of [T] at the beginning of
    some sequence. *)



End Def.

(** Exercise:

    The type of booleans [bool] is defined as an inductive type
    generated by two values, [true] and [false]. In this sense, it is
    equivalent to the [color] type defined above. The [negb] function
    implements boolean negation. It is defined as:

        negb b := if b then false else true

    Prove this: *)

Lemma negbK' : involutive negb.
Proof. Admitted.
