(** * Introduction

    Programming is a hard task, and writing correct programs is even harder, as
    any person having tried to write one can attest. A few factors contribute to
    this state of affairs.

    First, in order to write a correct program, we must first understand what
    "correct" means -- that is, what a particular program is supposed to
    do. Unfortunately, interesting programs have complex specifications, which
    are almost never stated completely. If we don't have a clear idea of what
    the purpose of a program is, it is less likely that we will be able to write
    a correct implementation.

    Second, even with a complete, precise specification in hand, it is not easy
    to see whether an implementation conforms to it. Programmers convince
    themselves of this by using the program in controlled trials, by running
    extensive testing, or with tool support. These techniques can lead to a
    dramatic increase in software quality, but often fail to detect subtle
    mistakes that end up appearing after the program is deployed.

    Many tools and methodologies have been introduced to try to solve these two
    problems. Among those, we can mention a particularly interesting class:
    _proof assistants_. Proof assistants allow programmers to write spefications
    and connect them to programs via _machine-checked proofs_. If a programmer
    can formulate a logically sound argument for why their program is correct,
    the proof assistant will agree and tell them so. Otherwise, if the argument
    contains any flaws, the proof assistant will notice it and report to the
    programmer.

    This document is an introduction to Coq, a powerful proof assistant. Coq
    comes with a rich language for writing programs, specifications, and
    mathematical concepts, and connecting them with formal proofs. Coq has been
    successfully applied to the verification of complex programs, including
    compilers and operating systems, and also used to formalize important
    mathematical results, such as the four-color theorem or the odd-order
    theorem.

    Coq is a complex system that includes many features, and the Coq community
    has developed many styles for using it. In this introduction, we will focus
    on _ssreflect_, a Coq library that has its own set of best practices.


    * First Steps

    Users write Coq code interactively within specialized programming
    environments. Among those, the most widely used are _CoqIDE_, a stand-alone
    editor that is part of the official Coq distribution, and _Proof General_,
    an Emacs plugin. We will assume that you have access to such an environment
    for running examples and doing exercises. To test whether your environment
    is working, try opening this file and hitting the "Next Step" button on the
    menu bar; your environment should change, telling you that it started Coq
    and highlight a region of the file.

    This highlighted region indicates what part of the file has been processed
    and accepted by Coq so far. We can use the "Next Step" command to tell Coq
    to try to advance to the next code fragment; in Proof General, this is done
    with the [C-c C-n] key combination, or by pressing the corresponding button
    on the top bar. We can also tell Coq to go back on the file, allowing us to
    edit parts of the file that are currently highlighted. In Proof General,
    this is done with the [C-n C-p] key combination. It is also possible to try
    to jump to an arbitrary point in the file (in Proof General, by placing the
    cursor at that point and hitting [C-n C-RET]), and to ask Coq to check the
    entire file ([C-n C-b] in Proof General). Try to play with these commands a
    little bit to familiarize yourself with the environment.

    The next line imports ssreflect libraries that we use in this file. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

(** (If you encounter warning messages when importing these files, don't worry:
    they are probably harmless. Ssreflect redefines some of the basic Coq
    definitions, which sometimes causes Coq to print warnings.)


    * Defining a Data Type

    In this chapter, we introduce the most basic features of Coq with a simple
    case study: using _binary search trees_ to represent sets of numbers.
    First, we define a Coq data type of binary search trees: *)

Inductive tree : Type :=
| Leaf
| Node of tree & nat & tree.

(** This command declares a new type [tree] with two kinds of values: a value
    can be either [Leaf], which represents an empty tree, or of the form [Node
    t1 n t2], which represents a nonempty tree that stores a natural number [n]
    at its root and has two subtrees, [t1] and [t2].

    If you are familiar with functional programming languages, such as Haskell,
    OCaml, or Scala, it might help to know that the [Inductive] command is very
    similar to how we define data types in those languages.  In any case, it is
    worth analyzing this definition in some more detail.  In Coq, we call [Leaf]
    and [Node] the _constructors_ of the [tree] type.  A type declaration such
    as the one above can have as many constructors as we want, each listed after
    a vertical bar ([|]).  We see that there are two kinds of constructors:
    those that take arguments and those that don't.  The [Leaf] constructor does
    not take any arguments; we can use it directly to create a [tree] value.
    For instance: *)

Definition empty_tree : tree :=
  Leaf.

(** This command declares a new constant [empty_tree] of type [tree] that is
    defined as [Leaf].  (Note that Coq commands usually begin with an uppercase
    letter and are terminated by a period ([.]).)

    If we want to define a nonempty tree, we must apply the [Node] constructor
    to some arguments: *)

Definition nonempty_tree : tree :=
  Node Leaf 0 Leaf.

(** When Coq sees a list of expressions separated by white space, it understands
    that the first one is a function, and that the others are arguments to that
    function.  Note that the second argument, [0], is a value of the predefined
    [nat] representing natural numbers (non-negative integers). Thus, this
    definition represents a nonempty tree that stores [0] at its root and has
    empty children.

    Coq is a _typed_ language, and it always checks expressions to ensure that
    everything make sense.  For instance, the definition of [tree] says the
    second argument of [Node] must be an element of [nat].  When Coq sees
    anything that does not match what it expects, it complains: *)

Fail Definition nonempty_tree_wrong : tree :=
  Node Leaf Leaf Leaf.

(** (The [Fail] keyword allows us to enter commands that cause errors; Coq
    simply ignores them.)

    We can also combine previous definitions to write new ones: *)

Definition nonempty_tree' : tree :=
  Node nonempty_tree 0 empty_tree.

(** * Functions

    Like in other programming languages, we can define functions in Coq.  The
    following function checks whether a tree is empty. *)

Definition is_empty (t : tree) : bool :=
  match t with
  | Leaf         => true
  | Node t1 n t2 => false
  end.

(** This code says that [is_empty] takes one argument [t] of type [tree] and
    returns a Boolean. (The type [bool] of Booleans is already defined for us in
    Coq.) The body of the function analyzes the possible shapes that [t] can
    have using the [match] expression. Each clause after a [|] sign is called a
    _branch_, and describes the value of the expression when [t] has the
    corresponding shape; [t] is known as the _scrutinee_. Paraphrasing this
    definition, if [t] is a [Leaf], the function returns [true]; otherwise, if
    it is a [Node], it returns [false].  In Coq, every function that we write
    must be _total_; that is, defined for all inputs.  This means that the
    branches of a [match] must cover every possible shape that [t] may have.
    Since [tree] was defined with two constructors, these two branches already
    cover all cases.  Had we omitted one of them, Coq would complain. *)

Fail Definition is_empty_wrong (t : tree) : bool :=
  match t with
  | Leaf => true
  end.

(** Note that in the [Node] branch of [is_empty] we were able to give names to
    the of the constructor.  These names can be used in the return value, as in
    the next function, which returns the left child of a nonempty tree, or
    [Leaf] if the tree is empty: *)

Definition left_child (t : tree) : tree :=
  match t with
  | Leaf       => Leaf
  | Node t _ _ => t
  end.

(** As this example shows, when an argument to a function or to a [match] branch
    is not used, we can name it [_] instead. *)

(** ** Exercises

    Based on [left_child], write a [right_child] that extracts the right child
    of a tree. *)

(** We can test the behavior of Coq functions using the [Compute] command.  It
    simply takes a Coq expression as input and prints the result of fully
    evaluating it. *)

Compute is_empty empty_tree.
Compute is_empty nonempty_tree.
Compute left_child nonempty_tree.
Compute left_child nonempty_tree'.

(** We can also write functions of multiple arguments, and analyze multiple
    scrutinees in a single [match]: *)

Definition are_both_empty (t1 : tree) (t2 : tree) : bool :=
  match t1, t2 with
  | Leaf, Leaf => true
  | _   , _    => false
  end.

(** This last example shows that a branch can cover multiple constructors. When
    we give [_] instead of a constructor name, Coq understands that that branch
    corresponds to any cases that are not covered by the previous ones; here,
    those would be the ones where at least one of the trees is a [Node].  We can
    check that this function has the expected behavior: *)

Compute are_both_empty Leaf Leaf.
Compute are_both_empty Leaf nonempty_tree.

(** As a shorthand, when consecutive arguments of a function have the same type,
    we can group them together, like this: *)

Definition are_both_empty' (t1 t2 : tree) : bool :=
  match t1, t2 with
  | Leaf, Leaf => true
  | _   , _    => false
  end.

(** We saw earlier that Coq is a typed language, and that it rejects definitions
    that do not follow its typing rules.  Functions, like anything else, also
    have types.  We can query their types with the [Check] command, like this: *)

Check is_empty.
Check are_both_empty.

(** (It is usually preferable to avoid including [Check] commands in Coq files,
    since they only make sense interactively; we add them here for explanation
    purposes. You can avoid writing [Check] when using Coq interactively by
    issuing the appropriate command in your Coq environment. In Proof General,
    for instance, you can hit [C-c C-a C-c].)

    Types to the left of an arrow ([->]) specify the types of the arguments that
    a function expects; the right-most type is the return type.  The type of
    [is_empty], [tree -> bool], shows that that function expects one argument of
    type [tree] and produces a result of type [bool].  The type of
    [are_both_empty], [tree -> tree -> bool], shows that that function expects
    two arguments of type [tree] and produces a result of type [bool].

    Note that data-type constructors that take arguments are just another
    instance of functions, and are treated as such by Coq.  For instance, the
    type of [Node] is [tree -> nat -> tree -> tree], reflecting the arguments it
    takes and the result it produces; try checking it yourself!


    * Preexisting Definitions

    Before moving on to more interesting definitions, it is worth spending some
    time overviewing basic ones that are already provided by Coq.  Besides types
    such as [nat] and [bool], there are also many predefined functions on those
    types.  The [addn] function, as its name says, adds two natural numbers: *)

Check addn.
Compute addn 3 4.

(** Coq provides convenient infix syntax for such operators; the expression [n +
    m] is just a shorthand for [addn n m].  It is also possible to define our
    own custom notations in Coq, although we will defer this discussion for
    later. *)

Check 3 + 4.
Compute 3 + 4.

(** Other operations include subtraction ([subn]), and multiplication ([muln]),
    each with its own infix notation.  Note that subtraction on natural numbers
    is _truncated_: [n - m] equals [0] whenever [m] is greater than [n]. *)

Compute 4 - 3.
Compute 3 - 4.
Compute 3 * 4.

(** The [leq] function tests if its first argument is smaller than or equal to
    its second argument; the corresponding infix notation is [<=].  To test
    numbers for equality, we use [eq_op] (infix [==]). *)

Compute 3 <= 4.
Compute 4 <= 3.
Compute 4 == 4.
Compute 3 == 4.

(** If we ask Coq for the types of these operators, the answers we get are
    mostly unsurprising.  For instance, [addn] has type [nat -> nat -> nat]. *)

Check addn.

(** The exception to the rule is [eq_op]: Coq tells us that it has type [rel
    ?T], where [?T : eqType].  Although puzzling, this simply means that [eq_op]
    is a _polymorphic_ operator that can be used with any type that is provided
    with an equality test.  Basic types such as [nat] or [bool] already have
    predefined equality tests, so we don't have to worry about this; later, we
    will discuss how polymorphism works in Coq and how to define equality
    operators for our own types.

    For Booleans, besides equality testing, we also have the basic logic
    operations: [andb] ([&&]), [orb] ([||]), and [negb] ([~~], used in prefix
    form).  We can combine these operations to express complex conditions. *)

Compute (3 <= 4) && ~~ (4 == 5).
Compute (4 != 5). (* An abbreviation for [~~ (4 == 5)]. *)
Compute false || (3 + 4 <= 8).

(** For instance, here is an alternative definition of the [are_both_empty]
    function we saw previously. *)

Definition are_both_empty'' (t1 t2 : tree) : bool :=
  is_empty t1 && is_empty t2.

(** We can perform case analysis on a Boolean with the familiar if-then-else
    syntax: *)

Compute if true then 1 else 2.

(** This form is just a shorthand to an explicit [match]: *)

Compute match true with true => 1 | false => 2 end.

(** * Recursive Functions

    To write interesting programs, we often need to perform some form of
    iteration; in Coq, this is done using _recursion_, as in most functional
    programming languages.  We define recursive functions using the [Fixpoint]
    command.  It is similar to [Definition], except that we are allowed to make
    recursive calls inside the function we define.  Here is a first example: a
    recursive function that computes the size of a tree. *)

Fixpoint tsize (t : tree) : nat :=
  match t with
  | Leaf         => 0
  | Node t1 _ t2 => tsize t1 + 1 + tsize t2
  end.

(** We can test that our function works as expected: *)

Compute tsize empty_tree.
Compute tsize nonempty_tree.
Compute tsize (Node Leaf 0 nonempty_tree).

(** Here is another example: a function that mirrors a binary tree, swapping its
    left and right children. *)

Fixpoint tmirror (t : tree) : tree :=
  match t with
  | Leaf         => Leaf
  | Node t1 n t2 => Node (tmirror t2) n (tmirror t1)
  end.

(** Recursive functions in Coq work almost the same as in other languages, with
    one important caveat: since every function needs to be total, Coq only
    accepts recursive functions that terminate on all inputs.  Of course,
    computability theory tells us that no computer program can determine without
    error whether an arbitrary function terminates or not, so Coq must
    approximate that somehow.  What it does is that it checks that functions are
    only called recursively on _subterms_ of one of its arguments -- arguments
    that appear in the branch of a [match] that have the same type.  For
    instance, in the recursive functions above, the only recursive calls are
    those performed on the [t1] and [t2] children of [t].  This criterion is
    enough to guarantee that functions terminate, but it is far from complete:
    there are many terminating functions that Coq fails to recognize as such
    because they don't fit this criterion.  For instance, consider the following
    alternative implementation of [tsize]: *)

Fail Fixpoint tsize' (t : tree) : nat :=
  match t with
  | Leaf         => 0
  | Node t1 _ t2 => tsize' (tmirror t1) + 1 + tsize' (tmirror t2)
  end.

(** Intuitively, the definition of [tsize'] is safe because it is only called
    recursively on arguments with a strictly smaller height.  Unfortunately,
    Coq's termination checker is not powerful enough to realize this, and
    rejects it because [tmirror t1] is not a subterm of [t].  This is an
    admittedly artificial example, since nobody would implement [tsize] in this
    way, but it's good for understanding the limitations of the programs we can
    write in Coq.


    ** Exercises

    Write a [theight] function that computes the height of a binary tree.  You
    may want to use the [maxn] function, which computes the maximum of two
    numbers. *)
