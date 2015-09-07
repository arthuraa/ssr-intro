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
  | Node c t1 x t2 => Node c (tmirror t1) x (tmirror t2)
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


(*lists all elements stored in a tree from left to
    right: *)

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