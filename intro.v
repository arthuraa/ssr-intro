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

    We define recursive functions using the [Fixpoint] command. For
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

End Basic.

(** * Interlude: programming with sequences

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

(** This statement is slightly different compared to the ones we have
    encountered so far: it is a _conditional_ statement, which says
    that a fact is true under certain hypotheses. Each formula
    preceeding the implication operator [->] is a hypothesis that
    needs to be met for the conclusion of the statement (the formula
    after [->]) to hold. In this case, the lemma says that if the
    result of mapping a function [f] over a sequence [s] is empty,
    then [s] must be the empty sequence.

    To solve this goal, we can argue by case analysis. Since [seq] is
    generated by [nil] and [cons], [s] can have to forms: [[::]] and
    [x :: s'], for some values [x] and [s']. *)

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
    conclude. *)

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

(** With the [=>] operator, we can give this hypothesis a name and
    bring it into the context. This allows us to manipulate it,
    rewrite with it in our goal, etc., just like we did with the
    induction hypotheses we saw before. *)

Proof.
move=> e.

(** If instead of giving it a single name, we give a _list_ of names
    enclosed in brackets [[]], Coq will enumerate all equations
    between arguments that it can infer from that fact, from left to
    right, and name them according to the given list. Thus, the call
    *)

move: e => [ex ey].

(** removes [e] from the context, converting it into two equations
    [ex] and [ey], asserting [x1 = x2] and [y1 = y2]. The syntax tries
    to mimic the one for case-analysis patterns on purpose. On a data
    value, the pattern has the effect of enumerating all constructors
    that could have been used to produce that value. On an equality,
    the pattern enumerates all equalities that must hold for that one
    to be valid.

    At this point, we can conclude by rewriting with [e1], or by using
    [done] directly: *)

by [].
Qed.

(** (Can you make this proof shorter?)


    * Specifying and verifying a tree operation

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

(** The statement of the lemma may may look simple, but there is a
    subtle point worth noting: the logical implication operator [->]
    takes two [Prop] expressions as arguments, but we use it with two
    boolean expressions. Strictly speaking, [bool] and [Prop] are
    distinct types, which means that there is no reason why Coq should
    accept this statement a priori. The trick here is that ssreflect
    automatically converts from [bool] to [Prop] whenever there is a
    similar type mismatch: the boolean value [true], seen as a
    proposition, is trivially true, while [false] is trivially
    false. We will discuss the difference between [bool] and [Prop] in
    more detail later, but for now you can think of [bool] as a
    special case of [Prop].

    It seems a good idea to try to prove this result by induction. *)

elim: t => [|c t1 IH1 x' t2 IH2] /=.

(** In the first case ([t = Leaf]), we have to prove that [x] occurs
    in the empty sequence (that is, [telems Leaf]), assuming that
    [tmember x Leaf] is true. While [x] cannot occur in an empty
    sequence, we can remark that [tmember x Leaf] is [false] by
    definition. This means that we never have to consider this case
    because it can never occur. The [done] tactic can detect this and
    remove this case from consideration for us. In logic jargon, this
    is a particular case of the _principle of explosiion_, which
    states that a contradiction entails anything. *)

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

  rewrite mem_cat.




    * Injectivity and disjointness of constructors

    Here's an interesting lemma that we might want to prove about
    sequences: *)

Lemma map1_inj : injective (map (fun x : T => [:: x])).

(** This lemma says building a sequence consisting only of singleton
    sequences with elements drawn from some sequence is an injective
    operation. (Note that, as many other functional programming
    languages, Coq allows us to partially apply a function.) A
    function [f] is injective if [f x1 = f x2] implies [x1 = x2], as
    Coq can tell us: *)

Print injective.

(** We see that the hypothesis [f x1 = f x2] appears in the statement
    of [injective] as a formula to the left of an arrow [->]. This is
    just Coq's syntax for expressing hypothetical statements -- that
    is, statements that require some assumptions to hold. Hypotheses
    can be given names and brought into the context just as
    universally quantified variables. Thus, we could try to begin our
    proof like this: *)

Proof.
move=> s1 s2 e.

(** Since our proof needs to reason about all elements of these
    sequences, it seems reasonable to try to proceed by induction. For
    instance, we could try doing induction on [s1]: *)

Fail elim: s1.

(** Unfortunately, Coq complains that it cannot do induction on [s1]
    because that sequence appears in the [e] hypothesis. The solution
    is to put [e] back into the goal with the generalization operator
    [:], and then perform induction: *)

move: e.
elim: s1.

(** We can generalize several expressions at the same time, which
    allows us to combine both tactics above into a single call: *)

Restart.
move=> s1 s2 e.
elim: s1 e => [|x1 s1 IH] /= e.

(** Notice that the tactic above also moves [e] back into the context
    after simplifying the goal, which has the effect of simplifying
    [e] as well. (Try to remove the [/=] flag to see what happens!)

    The induction principle for sequences says that, in order to prove
    that some property holds of all sequences [s], it suffices to show
    two things: (1) that the property holds of [[::]], and (2) that it
    holds all sequences of the form [x :: s'] while assuming that it
    is valid for [s']. This principle is just a consequence of [seq]
    being inductively defined as having two constructors, which
    correspond exactly to these cases.

    On the first case, we see that the [e] hypothesis states that
    mapping a function over [s2] results in an empty
    sequence. Intuitively, we know that this must imply that [s2] is
    also empty, because otherwise the result of map would have at
    least one element. But how do we convince Coq of this fact?

    Arguments of this form are usually done formally by case analysis:
    we consider all possible forms that [s2] can have, but argue that
    some of them cannot arise because a contradiction would
    follow. Hence, we use the [case] tactic: *)

  case: s2 e => [|x2 s2] /= e.

(** Notice that we had also to generalize over [e] before performing
    case analysis on [s2]. The first subgoal becomes [[::] = [::]],
    which follows immediately. *)

    by [].

(** The goal on the second branch becomes [[::] = x2 :: s2], which is
    obviously false! Fortunately, we see that [e] now asserts that the
    empty sequence is equal to one that starts with the cons
    constructor [::]. In Coq's logic, expressions of some inductive
    type that begin with different constructors cannot be equal, which
    means that this case is contradictory and can never occur. The
    basic [done] tactic can take advantage of this fact to remove this
    subgoal from further consideration. In common logic jargon, this
    is an instance of the _principle of explosion_, which assert that
    a contradiction entails anything. *)

  by [].

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

End Basic.

(** Exercise:

    The type of booleans [bool] is defined as an inductive type
    generated by two values, [true] and [false]. In this sense, it is
    equivalent to the [color] type defined above. The [negb] function
    implements boolean negation. It is defined as:

        negb b := if b then false else true

    Prove this: *)

Lemma negbK' : involutive negb.
Proof. Admitted.

(** Exercise:

    Prove this fact. *)

Lemma cat_fact T (s : seq T) : s ++ s = s -> s = [::].
Proof. Admitted.