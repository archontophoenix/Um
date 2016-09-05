The Uncomplicated Machine project.

The goal is:

. To define a syntax for infix binary operators that translates, by
  easy-to-understand rules (implemented by the Uh parser), to s-expressions.

. To create a logic programming language (Rofl), based on s-expressions, that
  omits the confusing/imperative cruft that has accumulated in Prolog.

. To create a typechecker, written in Rofl, for a dependently typed language
  (Duh) that will do general term inference.

Status 5 September 2016:

. Uh seems to be running fine. But if I were to rewrite it, I would probably
  start out by writing a straightforward recursive-descent parser, and not
  introduce parsing combinators except as needed. Writing the combinator
  library first seems to have driven the development in a direction that makes
  it hard to give good error messages (so they aren't good).

. Rofl parses input correctly, but doesn't get the right answers when it runs.
  The source is full of TODOs  However, I think the main ideas of Rofl are
  becoming clear enough that it's worth creating a Github repository.

  Rofl's ideas, with respect to its ancestor Prolog, include:

  . No cut operator. I believe this is the thing that freaks out more people
    trying to learn Prolog than anything else. There is no excuse for the cut
    operator; Prolog has perfectly good conditional constructs whose scope is
    not ridiculous.

  . Pattern matching as the conditional operator instead of one based on
    negation as failure.

    Negation as failure is wonderfully expressive, but it commits the language
    to an indefinite (and sometimes infinite) amount of work before it can
    choose which branch of a conditional to execute. Pattern matching, by
    contrast, performs a single unification for each pattern in a match
    expression.

  . Configurable operations during search. The configuration is divided into
    two pieces: Visitors (which decide what to do with the answers and failures
    found at each node in the search tree) and Strategies (which decide which
    node in the search tree to explore next).

    Configurable strategies were the motivation for replacing negation as
    failure with pattern matching. A strategy might choose not to explore a
    subtree completely, but negation as failure requires a full search in
    order to decide to choose the false branch of a condition. Pattern matching,
    on the other hand, can be implemented without imposing artificial
    constraints on search strategies.

  . Hypotheticals (not yet implemented): executing a query on an altered
    database. This can be done without mutating the current database (as
    Prolog's assert, retract, etc., do), which means that the language is
    still suitable for concurrent search strategies (or for anything else where
    mutation leads to disaster).

. The Duh project hasn't started. The Rofl files included here are just starting
  to play around with simple typechecking and function evaluation. Dependent
  types are a ways off.

Files:

Alts.scala:
  Lists of alternating types of odd (A B ... B A) or even (A B ... A B) length.

Fresh.scala:
  A source of values that are always unequal to any value previously created by
  the program. This is by definition a side effect, yet any code that uses
  Freshnesses without exporting them may be referentially transparent.

Fun.rofl:
  A first cut at a natural style for lambdas in Rofl.

Parsing.scala:
  Combinators used by Uh.

Rofl.scala:
  The Rofl language.

Sexps.scala:
  S-expressions.

SystemF.rofl:
  The start of a typechecker for something more complicated than the simply
  typed lambda calculus.

Types0.rofl:
  Some simply typed data structures.

Types1.rofl:
  A more elaborate version of Types0 -- complicated enough to illustrate why
  you might want to implement more general lambdas.

Uh.scala:
  The Uh parser, which converts a syntax with infix operators (among a few
  other features) into s-expressions.

Valids.scala:
  Small validation library.