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

    Users write Coq code interactively within specialized programming
    environments. Among those, the most widely used are _CoqIDE_, a
    stand-alone editor that is part of the official Coq distribution,
    and _Proof General_, an Emacs plugin. We will assume that you have
    access to such an environment for running examples and doing
    exercises. To test whether your environment is working, try
    opening this file and hitting the "Next Step" button on the menu
    bar; your environment should change, telling you that it started
    Coq and highlight a region of the file.

    This highlighted region indicates what part of the file has been
    processed and accepted by Coq so far. We can use the "Next Step"
    command to tell Coq to try to advance to the next code fragment;
    in Proof General, this is done with the [C-c C-n] key combination,
    or by pressing the corresponding button on the top bar. We can
    also tell Coq to go back on the file, allowing us to edit parts of
    the file that are currently highlighted. In Proof General, this is
    done with the [C-n C-p] key combination. It is also possible to
    try to jump to an arbitrary point in the file (in Proof General,
    by placing the cursor at that point and hitting [C-n C-RET]), and
    to ask Coq to check the entire file ([C-n C-b] in Proof
    General). Try to play with these commands a little bit to
    familiarize yourself with the environment.

    The two lines that you see below import ssreflect libraries that
    we use in this file. *)

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.

(** (If you encounter warning messages when importing these files,
    don't worry: they are probably harmless. Ssreflect redefines some
    of the basic Coq definitions, which sometimes causes Coq to print
    warnings.)

    The next commands turn on options that make programming in Coq a
    bit easier; it is usually a good idea to include those at the
    beginning of your files. The first two allow us to omit arguments
    that can be automatically inferred by Coq (usually, type
    parameters for polymorphic functions); the last one instructs
    Coq's printer to omit these arguments when printing terms. If this
    sounds a bit mysterious to you, don't worry -- you don't need to
    understand what they do right now. We will come back to them
    later. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Defining simple data types

    In this chapter, we will study how to use Coq to implement and
    verify red-black-tree operations for building an abstract data
    type of sets. We will begin by showing how to use Coq to define
    simple data types.

    The [Inductive] command declares new data types; its syntax and
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
    Coq environment. In Proof General, for instance, you can hit [C-c
    C-a C-c].

    Constructors of inductive data types can take arguments, which can
    include elements of the type being defined. The next declaration
    defines a red-black tree data type for storing number values;
    these are binary trees whose internal nodes are colored either
    [Red] or [Black], and contain an element of [nat], a standard Coq
    type representing natural numbers. *)

Inductive nat_tree : Type :=
| NatLeaf
| NatNode of color & nat_tree & nat & nat_tree.

(** Let's analyze this declaration. [NatLeaf] is a constructor that
    takes no arguments, as the [Red] and [Black] constructors of
    [color]. [Node], on the other hand, takes four arguments: a
    [color], a [nat_tree], a [nat], and another [nat_tree]. We can
    check that Coq understands our new definitions: *)

Check NatLeaf.
Check NatNode.

(** The arrows ([->]) indicate that [NatNode] expects arguments; each
    type to the left of an arrow specifies the type of an argument to
    [NatNode]. To use [NatNode], we must supply elements of matching
    types by writing them in sequence after that constructor: *)

Check NatNode Red NatLeaf 0 NatLeaf.
Check NatNode Black (NatNode Red NatLeaf 0 NatLeaf) 1 NatLeaf.

(** The first expression represents a tree of natural numbers that
    contains a single element: the number [0]. Its root node is
    colored [Red]. The second expression represents a tree of natural
    numbers that contains two elements, [0] and [1]. The number [1] is
    stored at the root of the tree, while [0] is stored on its left
    child. The root of that tree is colored [Black], while the subtree
    that stores [0] is colored [Red].

    As in other functional programming languages, we can make our
    definition more generic, by allowing our trees to store elements
    of any type [T] that we want: *)

Inductive tree (T : Type) : Type :=
| Leaf
| Node of color & tree T & T & tree T.

(** Now, when we check the types of [Leaf] and [Node], we see that
    they are prefixed with a [forall], which allows us to choose what
    type the contents of our tree should have. *)

Check Leaf.
Check Node.

(** One thing that makes Coq different from other functional languages
    is that polymorphism is _explicit_: each use of a polymorphic
    value must be annotated with the type we want to instantiate it
    with, as if it were the argument to a function. For instance, this
    is how we use [Leaf] to construct an empty [tree] of [nat]
    elements: *)

Check Leaf nat.

(** Providing these annotations can be cumbersome, so Coq provides a
    shorthand. We can specify that the value of [T] should be inferred
    every time [Leaf] is used. This feature is known as _implicit
    arguments_. *)

Arguments Leaf {T}.

(** The curly braces around [T] in the above command declare that type
    as being implicit. In some cases, type parameters can be deduced
    from the type of the arguments of a term. For instance, the third
    argument of the [Node] constructor has exactly the type that is
    used as a parameter to [Node]. Hence, if we know the type of that
    argument, we know what [T] should be. The [Set Implicit Arguments]
    directive we used earlier instructs Coq to always declare such
    arguments as implicit. This allows us to write expressions such as
    the following: *)

Check Node Red Leaf 0 Leaf.
Check Node Black (Node Red Leaf 0 Leaf) 1 Leaf.

(** We can also turn off implicit arguments temporarily by prefixing
    an identifier with [@]. This is useful in situations where Coq
    doesn't have enough information to determine what the value of
    some type parameter should be. *)

Check @Node nat Red Leaf 0 (@Leaf nat).

(** Before we move on, a small comment: the [of] and [&] symbols are
    part of ssreflect. Here is what the previous declaration would
    look like in usual Coq syntax: *)

Inductive tree' (T : Type) : Type :=
| Leaf' : tree' T
| Node' : color -> tree' T -> T -> tree' T -> tree' T.

(** We have replaced the type and constructor names above to avoid
    clashes, but the two declarations are otherwise equivalent.


    * Definitions

    We can give names to values and functions with the [Definition]
    command. For instance: *)

Definition singleton (T : Type) (x : T) : tree T :=
  Node Red Leaf x Leaf.

(** The above declaration defines a function [singleton] that takes
    one argument, an element [x] of some type [T], which can be chosen
    arbitrarily. Its result is a [tree T] consisting of one internal
    node colored [Red] that contains [x]. We can see that this is
    reflected in the type of [singleton]: *)

Check singleton.

(** The syntax for applying functions is the same as for data
    constructors: *)

Check singleton 0.

(** Note that the above definition has type annotations in them. We
    can usually omit some or all of them, since Coq can infer them
    most of the time. Here, for instance, we don't annotate the result
    type of [three_times], and omit the type of [T]: *)

Definition three_times T (x : T) :=
  Node Black (singleton x) x (singleton x).

(** Nevertheless, it is often a good idea to include type annotations,
    since they can improve readability and serve as good
    documentation.

    We can use the [Compute] command to evaluate an expression: *)

Compute three_times 0.

(** We define recursive functions using the [Fixpoint] command. For
    instance, here is a function [tsize] that computes the number of
    elements stored in a tree: *)

Fixpoint tsize T (t : tree T) : nat :=
  match t with
  | Leaf => 0
  | Node _ t1 _ t2 => tsize t1 + 1 + tsize t2
  end.

(** Notice that this definition uses the addition operation on natural
    numbers, [+]. The [ssrnat] library of ssreflect comes with many
    other predefined functions on [nat], including multiplication,
    subtraction, etc. The [nat] type is used extensively in Coq
    developments, and we will encounter it often.

    Here is another recursive function: one for mirroring a tree. *)

Fixpoint tmirror T (t : tree T) : tree T :=
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

Lemma tsize1 T (x : T) : tsize (singleton x) = 1.

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

(** To better understand how simplification is performed, we can write
    a step-by-step version of the previous proof, showing intermediate
    simplification steps that are omitted by Coq. *)

Lemma tsize1' T (x : T) : tsize (singleton x) = 1.
Proof.

(** Writing [rewrite -[x]/(y)] instructs Coq to replace all
    occurrences of [x] by [y] in the current goal, provided that both
    expressions are equivalent according to the computation rules of
    Coq's logic. In the line below, Coq understands that both terms
    are equal because the second is exactly what we gave for the
    definition of [singleton]. *)

rewrite -[singleton x]/(Node Red Leaf x Leaf).

(** Here, we can see that [rewrite] is a more general tactic that
    takes many possible actions as arguments, which have slightly
    different effects.

    We can perform a similar exercise for [tsize], and replace the
    call to it by its definition. *)

rewrite -[tsize _]/(match Node Red Leaf x Leaf with
                    | Leaf => 0
                    | Node _ t1 _ t2 => tsize t1 + 1 + tsize t2
                    end).

(** Notice that we didn't specify the argument that was given to
    [tsize], and just said [_] instead. Coq can often understand these
    incomplete patterns from the context where they are used.

    Simplifying the [match] expression is easy: since Coq knows the
    first constructor used in the discriminee, it knows which branch
    to take. Here, we use the [LHS] (short for _left-hand side_)
    pattern instead of writing the entire term. *)

rewrite -[LHS]/(tsize Leaf + 1 + tsize Leaf).

(** Similar simplification steps show that [tsize Leaf] evaluates to [0]. *)

rewrite -[tsize Leaf]/(0).

(** At this point, we can conclude. *)

done.
Qed.

(** Calling [done] after a tactic is so common that ssreflect offers
    special syntax for it: if [t] is a tactic, then [by t] tries to
    execute [t] and to conclude the proof afterwards by calling
    [done]. If the proof cannot be complete, Coq raises an error. *)

Lemma tsize1'' T (x : T) : tsize (singleton x) = 1.
Proof. by rewrite /=. Qed.

(** As a matter of fact, the above proof is so simple that we don't
    even need to tell Coq to simplify the goal; [done] alone
    suffices. Alternatively, we can also write [by []] (that is, [by]
    with an "empty" first tactic) as a synonym for [done]: *)

Lemma tsize1''' T (x : T) : tsize (singleton x) = 1.
Proof. done. Qed.

Lemma tsize1'''' T (x : T) : tsize (singleton x) = 1.
Proof. by []. Qed.

(** Before we move on to more interesting proofs, it is worth leaving
    a small note on naming conventions: ssreflect tries to follow very
    consistent naming conventions for its lemmas, which we will try to
    emulate here. The [1] suffix on [tsize1], for instance, signals
    that this lemma relates [tsize] to something of size [1]; in this
    case, a singleton tree. We will point to other naming conventions
    as we progress.


    * Using sections

    Coq provides another mechanism for alleviating the burden of
    annotations: _sections_. Sections allow us to declare certain
    parameters as being common to all definitions and lemmas enclosed
    within it. Inside the section, these parameters don't have to be
    redeclared and applied; when the section is closed, on the other
    hand, all parameters become explicit.

    Sections are opened with the [Section] keyword. Each section must
    be given a name (in this case, [Ex]). *)

Section Ex.

(** Once we are inside a section, we can use the [Variable] command to
    declare a parameter that will be shared by all definitions in the
    section. *)

Variable T : Type.

(** We can also associate variable names to certain types. After the
    following command, Coq assumes that [x] has type [T], unless
    otherwise specified. This has the same effect for variables with
    "similar" names, such as [x0] and [x']. *)

Implicit Type x : T.

(** We can now write statements such as this one: *)

Lemma tsize1''''' x : tsize (singleton x) = 1.
Proof. by []. Qed.

(** Notice that [x] had to be declared in the statement of the lemma,
    but that we didn't have to supply its type. [T], on the other
    hand, didn't have to be declared again.

    If we check the lemma we just proved, we see that [T] is "fixed"
    (that is, not universally quantified): *)

Check tsize1'''''.

(** Once we close the [Ex] section, we see that [T] becomes explicitly
    quantified: *)

End Ex.

Check tsize1'''''.

(** We will enclose some of the remaining material in a section with
    some variable declarations and implicit types, to make our lives
    easier. *)

Section Basic.

Variable T : Type.

Implicit Type (t : tree T) (x : T) (c : color).

(** * Proof by case analysis

    Often, simplification is not enough to complete a proof. For
    instance, suppose that we have the following function [tcolor]
    which computes the color of the root of a tree (by convention,
    empty trees are colored black): *)

Definition tcolor t : color :=
  match t with
  | Leaf => Black
  | Node c _ _ _ => c
  end.

(** Clearly, the [tmirror] function defined above does not change the
    color of the tree it is applied to. Let's try to convince Coq of
    this fact: *)

Lemma tcolor_tmirror t : tcolor (tmirror t) = tcolor t.
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
    the goal into the context by using the [move] tactic: *)

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

Lemma tcolor_tmirror' t : tcolor (tmirror t) = tcolor t.
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

Lemma tcolor_tmirror'' t : tcolor (tmirror t) = tcolor t.
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

Lemma tcolor_tmirror2 t : tcolor (tmirror (tmirror t)) = tcolor t.
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

(** Finally, we can prefix a lemma with a minus sign [-] to indicate
    that we want to rewrite in the opposite direction: *)

Lemma tcolor_tmirror2'''' t : tcolor (tmirror (tmirror t)) = tcolor t.
Proof.

(* Replace [tcolor t] by [tcolor (tmirror t)] *)
rewrite -(tcolor_tmirror t).

(* Replace [tcolor (tmirror t)] by [tcolor (tmirror (tmirror t))] *)
rewrite -(tcolor_tmirror (tmirror t)).

by [].
Qed.

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

Lemma tmirrorK'''' : cancel (@tmirror T) (@tmirror T).
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

Lemma tmirrorK''''' : involutive (@tmirror T).
Proof. by elim=> [|/= c t1 -> x t2 ->]. Qed.

(** Notice that we have used [involutive tmirror] instead of [tcancel
    tmirror tmirror]. [involutive foo] is defined exactly as [cancel
    foo foo].

    The reason we wrote [: t] on previous calls to [elim] is simple:
    the [:] is actually a tactic operator, whose effect is to put some
    variables in the context back in the goal. In this sense, it is
    the inverse of the [=>] introduction operator. For instance: *)

Lemma tmirrorK'''''' : involutive (@tmirror T).
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

(** * Hypothetical statements

    So far, we have seen how to prove facts that are always true. In
    many cases, however, we are interested in facts that are only
    valid when certain hypotheses hold. In Coq, we can express such
    hypothetical statements with the implication operator [->]. For
    example: *)

Lemma tmirror_leaf t : tmirror t = Leaf -> t = Leaf.

(** Each formula preceeding an arrow is a hypothesis that needs to be
    met for the conclusion of the statement (the formula after [->])
    to hold. In this case, the lemma says that if the result of
    [tmirror t] is [Leaf], then [t] itself must be equal to [Leaf].

    We can use the [=>] operator to name hypotheses that appear in the
    goal and bring them into the context. This allows us to use a
    hypothesis like we used previous lemmas or induction hypotheses: *)

Proof.
move=> e.

(** We can use [tmirrorK] to replace [t] by [tmirror (tmirror t)]. *)

rewrite -(tmirrorK t).

(** Thanks to our hypothesis, we can now bring the goal to a more
    palatable form. *)

rewrite e.

(** Since [tmirror Leaf] is equal to [Leaf] by simplification, Coq can
    conclude directly. *)

by [].
Qed.

(** This shows how to prove hypothetical results. It is also possible
    to use hypothetical results to prove other statements; this in
    turn requires that we prove separately each hypothesis in that
    statement. *)

Lemma tmirror_leaf2 t : tmirror (tmirror t) = Leaf -> t = Leaf.
Proof.
move=> e.

(** Since the [tmirror_leaf] lemma used below has a hypothesis, the
    rewrite below generates two subgoals: [Leaf = Leaf] and [tmirror t
    = Leaf]. The first one is trivial, and can be discharged directly
    with [//]. Notice*)

rewrite (@tmirror_leaf t) //.

(** Alternatively, if the goal matches exactly the conclusion of a
    lemma or hypothesis in the context, we can use the [apply]
    tactic. Once again, if the result we apply has any hypotheses,
    we will have to solve them as separate subgoals. *)

apply: tmirror_leaf.
by [].

(** In this case, choosing between [rewrite] and [apply] was (almost)
    just a matter of style. It is important to notice, however, that
    both tactics are usually not interchangeable. [rewrite] only works
    with statements whose conclusions are equalities, and performs a
    small modification on the goal. [apply], on the other hand, works
    with goals that involve _arbitrary_ logical constructs, not just
    equalities. It will be more useful once we learn more about Coq's
    logic.

    Besides using lemmas as functions to specify the value of
    universally quantified variables, we can use function application
    syntax to supply hypotheses. We can use this feature to prove the
    previous theorem with a single call to [apply]. *)

Restart.
move=> e.
by apply: (tmirror_leaf (tmirror_leaf e)).

(** Instead of using [by apply], we can also use [exact]. There are
    subtle differences between the two, but for now we can think of
    [exact] as a shorter version of [by apply]. *)

Restart.
move=> e.
exact: (tmirror_leaf (tmirror_leaf e)).
Qed.

(** * Forward reasoning tactics

    Coq's primary style of interaction is backwards: we progressively
    simplify the goal, until it reaches a state where it can be solved
    trivially. Often, it is more convenient to reason _forward_
    instead: progressively deduce more and more complex facts from the
    hypotheses that we have, until some of them can apply directly to
    the goal.

    In ssreflect, the two primary forward-reasoning tactics are [have]
    and [suffices]. When we write [have e: P], Coq adds a new
    intermediate subgoal where it asks for a proof of [P]. Once we
    complete the proof, it resumes the original subgoal, enriching the
    context with a new hypotheses [e : P]. We can use [have] to write
    an alternative proof of [tmirror_leaf2]: *)

Lemma tmirror_leaf2' t : tmirror (tmirror t) = Leaf -> t = Leaf.
Proof.
move=> e.
have e': tmirror t = Leaf.
  by apply: tmirror_leaf.
by apply: (tmirror_leaf e').

(** It is important to notice that the [:] symbol used in [have] is
    unrelated to the use of [:] in tactics such as [apply], [move] and
    [case]: in [have], its purpose is to state the intermediate result
    we want to prove, while in the other tactics we have seen it moves
    variables and hypotheses from the context into the goal.

    If the intermediate proof used with [have] is short, we can
    condense it into a single tactic, using the [by] keyword. *)

Restart.
move=> e.
have e': tmirror t = Leaf by apply: tmirror_leaf.
by apply: (tmirror_leaf e').

(** The [suffices] tactic is similar to [have]. Its main difference is
    that it reverses the order of the generated subgoals: the first
    subgoal is augmented with the new fact, while the second one asks
    of the proof of that auxiliary fact. Compare: *)

Restart.
move=> e.
suffices e': tmirror t = Leaf.
  by apply: (tmirror_leaf e').
by apply: tmirror_leaf.

(** We are also allowed to merge the proof of the first subgoal into
    the call to [suffices]: *)

Restart.
move=> e.
suffices e': tmirror t = Leaf by apply: (tmirror_leaf e').
by apply: tmirror_leaf.
Qed.

(** The [suffices] tactic is useful when the proof of the auxiliary
    statement is more complicated than the part that uses it. Its name
    is meant to mimic the usual pattern seen in mathematical proofs:
    "To show A, it suffices to show B, because [short argument
    follows]. Let's then prove B." *)

End Basic.

(** Before discussing more interesting operations on trees, it is
    worth having a tour of some of the basic types and operations
    provided by Coq and ssreflect.


    * Booleans

    Coq defines [bool] as an inductive data type with two
    constructors: [true] and [false]. In that sense, it is equivalent
    to the definition of the [color] type above. *)

Print bool.

(** We can perform case analysis on a boolean with the familiar
    if-then-else syntax: *)

Compute if true then 1 else 2.

(** This form is just a shorthand to an explicit [match]: *)

Compute match true with true => 1 | false => 2 end.

(** Many standard boolean operations are already defined for us. We
    write [&&], [||] and [~~] for the "and", "or", and "not"
    functions. *)

Check true && true.
Check true || ~~ false.

(** The [case] tactic can be used to do a proof by cases on members of
    any inductively defined type, including [bool]. *)

Lemma andbF' b : b && false = false.
Proof.

(** Coq cannot solve this goal by itself because [&&] is defined by
    case analysis on its first argument: *)

Print andb.

(** If we do case on [b], on the other hand, the goal becomes
    trivial. We can see that [b] is replaced by [true] and [false] on
    each generated subgoal: *)

case: b.
  by [].
by [].
Qed.

(** Ssreflect provides an [andbF] lemma whose statement is similar to
    the one above. The name [andbF] means that the lemma talks about
    what happens when we compute the [and] of an arbitrary boolean [b]
    and [false] ([F]). (Can you guess what [andFb] states? What about
    [andbT]?).


    * Natural numbers

    We have already seen some definitions involving natural
    numbers. Unlike other languages, where numeric types are often
    primitive, [nat] in Coq is just another inductive data type. It is
    defined as the type having one constructor [O], representing zero,
    and one constructor [S : nat -> nat], which represents the
    successor of a number. *)

Print nat.

(** Coq allows us to write elements of [nat] with conventional arabic
    notation. This feature is just for making programming with [nat]
    more convenient: internally, natural numbers are still represented
    with [S] and [O]. *)

Check 2.
Check S (S O).

(** Additionally, ssreflect uses [n.+1] as special syntax for [S
    n]. For instance, here's how we can define a function for
    computing the Fibonacci numbers: *)

Fixpoint fib_aux n acc1 acc2 :=
  if n is n'.+1 then fib_aux n' acc2 (acc1 + acc2)
  else acc2.

Definition fib n := fib_aux n 0 1.

Compute fib 8.

(** This definition also uses a different syntax for doing pattern
    matching. [if e is p then e1 else e2] is just a synonym for [match
    e with p => e1 | _ => e2]. If it is not obvious for you that this
    function defines the Fibonacci numbers, check the exercise at the
    end of the chapter.

    We can subtract two numbers by using the [subn] function, written
    as the familiar infix operator [-]. It is worth noting that,
    because [nat] doesn't contain negative values, subtraction on
    [nat] is _truncated_: if [n] is less than [m], then [n - m =
    0]. *)

Compute 2 - 4.

(** We can test whether a number is less than other with the [<=] operator: *)

Compute 2 <= 4.
Compute 4 <= 2.

(** We can also write [n < m], which is just special syntax for [n.+1 <= m]. *)

Check (2 + 3).+1 <= 5.

(** When used with a [nat], the [case] tactic behaves similarly to
    [tree] or [bool]: it generates subgoals corresponding to the [O]
    and [S] constructors. The [elim] tactic also works with members of
    [nat], generating an induction hypothesis for the [S] case. Here is
    a proof of the [addnA] lemma we have used above. *)

Lemma addnA' : associative addn.
Proof.
move=> n m p.
elim: n => [|n IH] //=.
rewrite addSn IH.
by [].
Qed.

(** * Sequences

    Like other functional programming languages, ssreflect provides a
    data type [seq] of finite sequences, or lists. To use it, you must
    import the [Ssreflect.seq] library. This type is parameterized
    over the type of elements contained in the sequence; hence,
    elements of [seq nat] are sequences of natural numbers, while
    elements of [seq bool] are sequences of booleans.

    As in other languages, the [seq] type is generated by two
    constructors: [nil], which denotes an empty sequence, and [cons],
    which adds an element at the beginning of some other sequence. For
    those, Ssreflect provides the notations [[::]] and [::]. For
    example, the sequence consisting of the natural numbers [1], [2],
    and [3] is written as follows: *)

Check 1 :: 2 :: 3 :: [::].

(** Notice that Coq prints the above expression in a slightly
    different form. In ssreflect, we can refer to a literal sequence
    [e1 :: .. :: en :: [::]] using the notation [[:: e1; .. ; en]]: *)

Check [:: 1; 2; 3].

(** The [++] operator concatenates two sequences. *)

Check [:: true; false] ++ [:: true].

(** The [seq] library defines many common operations on sequences for
    us. The familiar [map] function applies some function [f] to all
    elements of a sequence [s]. Here, the [fun n => e] expression is
    Coq's syntax for an an _anonymous function_ that takes [n] as an
    argument and produces [e] as its result. *)

Check map (fun n => [:: n]) [:: 1; 2; 3].

(** Ssreflect has support for a limited form of _list comprehension_
    syntax, similar to Haskell's. We can see that the above expression
    is printed slightly different by Coq when we execute [Check]: *)

Check [seq [:: n] | n <- [:: 1; 2; 3]].

(** Unfortunately, Coq's notation mechanism is not powerful enough to
    define a flexible, generic equivalent of the list comprehension
    syntax. Thus, ssreflect defines special syntax for only a handful
    of expressions involving sequences. You can read more about them
    in the documentation of the [seq] library.

    Since [seq] is generated by [nil] and [cons], doing case analysis
    or induction on a sequence will generate two cases: one for [nil]
    and one for [cons]. For example: *)

Lemma catA' T : associative (@cat T).
Proof.
move=> s1 s2 s3.
elim: s1 => [|x s1 IH] /=.
  by []. (* [nil] case *)
by rewrite IH. (* [cons] case *)
Qed.

(** (Can you make the above proof shorter?)

    Finally, ssreflect provides an operator [\in] for testing whether
    an element occurs in a sequence. *)

Check 1 \in [:: 1; 2; 3].

(** The [\in] operator is actually defined not just for sequences, but
    for any type supporting a "membership test" operation. In the case
    of sequences, we can only test for membership of elements of some
    [eqType], which is a Coq type equipped with a boolean operation
    for testing equality. We will come back to [eqType] in more detail
    later; for now, you only need to know that ssreflect defines such
    operations for many basic types, including [nat], [seq], among
    others.


    * Reasoning about constructors

    Intuitively, there are two properties that we expect to hold of
    data constructors. The first one is that constructors are
    _disjoint_: if we construct two values using different
    constructors, the two values must be different. The second one is
    that constructors are _injective_: whenever two expressions
    involving the same constructor are equal, we can conclude that the
    arguments given to the constructors are equal. These principles
    are validated by Coq's logic, and are useful for proving many
    results; we discuss a few examples here to show how they work.

    Suppose we wanted to prove the following result: *)

Lemma eq_map_nil T S (f : T -> S) s :
  [seq f x | x <- s] = [::] ->
  s = [::].

(** We can argue by case analysis. Since [seq] is generated by [nil]
    and [cons], [s] can have to forms: [[::]] and [x :: s'], for some
    values [x] and [s']. *)

Proof.
case: s=> [|x s'] /=.

(** We can see that the first case was reduced to [[::] = [::] -> [::]
    = [::]]. Since the conclusion is trivial, [done] suffices: *)

  by [].

(** The second case is more interesting: our goal wants us to conclude
    that [x :: s' = [::]], which is clearly false. However, the
    hypothesis in our goal now equates two expressions that start with
    different constructors:

    [f x :: [seq f x' | x' <- s'] = [::]]

    This hypothesis is now absurd, which means that this case can
    actually never occur. The [done] tactic can detect this situation
    and remove the case from further consideration, allowing us to
    conclude. In logic jargon, this is a particular instance of the
    _principle of explosion_, which states that a contradiction
    entails anything. *)

by [].
Qed.

(** (Can you make this proof shorter?)

    The second principle, injectivity, is not handled by [done] by
    default. Instead, ssreflect provides an introduction form for
    decomposing an equality between expressions with constructors in
    terms of the arguments that appear in it. Here is a simple
    example: *)

Lemma inj_ex T (x1 x2 y1 y2 : T) :
  [:: x1; y1] = [:: x2; y2] -> x1 = x2.

(** We have seen that we can use the [=>] tactic operator to name
    hypotheses and bring them into the context. If instead of giving
    it a single name, we give a _list_ of names enclosed in brackets
    [[]], Coq will enumerate all equations between arguments that it
    can infer from that fact, from left to right, and name them
    according to the given list. Thus, the call *)

Proof.
move=> [ex ey].

(** converts the [[:: x1; y1] = [:: x2; y2]] hypothesis into two
    equations [ex] and [ey], asserting [x1 = x2] and [y1 = y2]. The
    syntax tries to mimic the one for case-analysis patterns on
    purpose. On a data value, the pattern has the effect of
    enumerating all constructors that could have been used to produce
    that value. On an equality, the pattern enumerates all equalities
    that must hold for that one to be valid.

    At this point, we can conclude by rewriting with [e1], or by using
    [done] directly: *)

by [].
Qed.

(** (Can you make this proof shorter?)


    * Using booleans as propositions

    We often want to state facts as an equality between booleans. For
    instance, here's is how we might say that the number [1] occurs in
    the sequence [[:: 1; 2; 3]]: *)

Lemma bool_prop_ex1 : (1 \in [:: 1; 2; 3]) = true.

(** Since the [\in] operator is defined by a function that computes a
    boolean, Coq can attest that this claim is valid by computation. *)

Proof. by []. Qed.

(** This pattern is so common that ssreflect provides a shorthand for
    it: whenever an expression [e] of type [bool] is used in a context
    that expects an expression of type [Prop], [e] is implicitly
    converted to [Prop] by mapping it to [e = true]. *)

Lemma bool_prop_ex2 : 1 \in [:: 1; 2; 3].

(** This is an instance of a generic feature of Coq called _implicit
    coercions_, which allows certain functions to be implicitly
    inserted in an expression to convert from one type to another. We
    can have a better sense of what is going on by telling Coq to show
    all coercions that are applied: *)

Set Printing Coercions.

(** We can see that the goal we were trying to prove is actually
    [is_true (1 \in [:: 1; 2; 3])], where [is_true b] is defined as [b
    = true]. *)

Unset Printing Coercions.

(** Coq treats [is_true b] as if it were an equality. For instance,
    it can solve trivial goals involving [is_true] with [done]. *)

Proof. by []. Qed.

(** It can also rewrite with hypotheses of the form [is_true b], which
    has the effect of replacing [b] by [true]. For instance, we can
    prove the following fact about the boolean "and" operator [&&]: *)

Lemma bool_prop_ex3 (b c : bool) : b -> b && c = c.
Proof. by move=> ->. Qed.

(** Since different constructors are disjoint, we know that [false]
    cannot occur in a hypothesis, because that is synonym with [false
    = true]. The [done] tactic can detect this and similar hypotheses
    in our context and discharge the current goal
    automatically. Consider the following result: *)

Lemma bool_prop_ex4 n : n <= 0 -> n = 0.
Proof.

(** To put the goal in a shape that can be simplified, we can perform
    case analysis on [n]: *)

case: n => [|n] /=.

(** In the first subgoal, we have to prove [0 = 0], which is trivial: *)

  by [].

(** In the second one, we are left with a contradictory hypothesis,
    stating that [n < 0] (recall that [n < 0] is just notation for
    [n.+1 <= 0]). We can rewrite with [ltn0] lemma from [ssrnat]
    to replace that hypothesis by [false], allowing us to conclude.. *)

rewrite ltn0.
by [].

(** As a matter of fact, we don't even need to call [rewrite], because
    [n < 0] can be "forced" to simplify to [false]: *)

Restart.
by case: n.
Qed.

(** We may also use a boolean to state that a certain proposition is
    not valid. For instance: *)

Lemma bool_prop_ex5 : (4 < 2) = false.
Proof. by []. Qed.

(** However, because of how the coercion from [bool] to [Prop] is
    defined, ssreflect prefers statements of the form [~~ b = true]:
    *)

Lemma bool_prop_ex6 : ~~ (4 < 2).
Proof. by []. Qed.

(** * Generalizing the induction hypothesis *)

Module Rev.

Section Rev.

Variable T : Type.

Implicit Type s : seq T.

Fixpoint rev s :=
  match s with
  | [::] => [::]
  | x :: s => rev s ++ [:: x]
  end.

Fixpoint tr_rev_aux s acc :=
  match s with
  | [::] => acc
  | x :: s => tr_rev_aux s (x :: acc)
  end.

Definition tr_rev s := tr_rev_aux s [::].

Lemma tr_revE s : tr_rev s = rev s.
Proof.
rewrite /tr_rev -[RHS]cats0.
elim: s [::] => [|x s IH] //= acc.
by rewrite IH -catA.
Qed.

End Rev.

End Rev.

(** * Specifying and verifying a tree operation

    We can use sequences to specify and verify our first interesting
    tree operation: a [tmember] function, that tests whether some
    element [x] occurs on a tree [t], assuming that [t] is a binary
    search tree -- that is, that any element on a node is greater than
    those on its left subtree and smaller than those on its right
    subtree.

    It would be possible to program [tmember] for any type of elements
    with a comparison operator. However, we will begin with something
    simpler, and define [tmember] only for trees of natural numbers,
    taking advantage of the usual comparison operator [<] defined in
    the [ssrnat] library. Notice that our definition uses [if]
    expressions, which are defined in the obvious way in terms of
    [match]. *)

Fixpoint tmember (x : nat) (t : tree nat) : bool :=
  match t with
  | Leaf => false
  | Node _ t1 x' t2 =>
    if x < x' then tmember x t1
    else if x' < x then tmember x t2
    else true
  end.

(** We will state the specification of [tmember] in terms of a
    [telems] function, which lists all elements that appear in the
    tree from left to right. *)

Fixpoint telems T (t : tree T) : seq T :=
  match t with
  | Leaf => [::]
  | Node _ t1 x t2 => telems t1 ++ x :: telems t2
  end.

(** In order to fully specify the behavior of [tmember], we would have
    to reason about the search-tree invariant. Before getting there,
    however, we start with something simpler: showing that if [tmember
    x t] is true, then [x] must occur in [telems t]. *)

Lemma tmember_sound x t : tmember x t -> x \in telems t.
Proof.

(** It seems a good idea to try to prove this result by induction. *)

elim: t => [|c t1 IH1 x' t2 IH2] /=.

(** In the first case ([t = Leaf]), we have to prove that [x] occurs
    in the empty sequence (that is, [telems Leaf]), assuming that
    [tmember x Leaf] is true. While [x] cannot occur in an empty
    sequence, we can remark that [tmember x Leaf] is [false] by
    definition. This means that we never have to consider this case
    because it can never occur. The [done] tactic can detect this and
    remove this case from consideration for us.  *)

  by [].

(** The second case is more interesting, as we have to consider all
    possible outcomes of comparing [x'] and [x]. The [case] variant
    below can be used to perform case analysis on a value while
    generating an equation for that case. For reasons that soon will
    become apparent, we will need these additional equations later. *)

case e1: (x < x').

(** In the first generated subgoal, we have an additional hypothesis
    [e1] stating [(x < x') = true], and the original compliated
    premise has been simplified to [tmember x t1]. *)

  rewrite mem_cat => e.
  by rewrite (IH1 e).

case e2: (x' < x).

  rewrite mem_cat /= inE.

Admitted.

(** * Exercises: *)

Lemma negbK' : involutive negb.
Proof. Admitted.

Lemma eq_add_0L n m : n + m = 0 -> n = 0.
Proof. Admitted.

Lemma eq_add_0R n m : n + m = 0 -> m = 0.
Proof. Admitted.

(** Hint: The [drop_size_cat] lemma might come in handy. *)
Lemma cat_fact T (s : seq T) : s ++ s = s -> s = [::].
Proof. Admitted.

(** Hint: What is the value of [fib_aux n (x1 + x2) (y1 + y2)]? *)
Lemma fib2 n : fib n.+2 = fib n.+1 + fib n.
Proof. Admitted.
