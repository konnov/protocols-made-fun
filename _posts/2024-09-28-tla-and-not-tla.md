---
layout: post
title: "Why I use TLA+ and not(TLA+): Part 1"
date: 2024-10-04
categories: specification modelchecking tlaplus quint
quint: true
tlaplus: true
math: true
---

**Author**: Igor Konnov

Recently, we have seen several interesting write-ups in the
[TLA<sup>+</sup>][TLA+] ecosystem:

 1. Leslie Lamport posted the document on [The Future of TLA+][].
 
 1. Andrew Helwer wrote the blogpost called [TLA+ is more than a DSL for
 breadth-first search][].
 
 1. prestonph asked about [Opinions on Quint][].

These three posts made me think about the TLA<sup>+</sup>-related work I have
been doing since 2016. There were numerous discussions on [Hacker News][], but
those seem to have saturated to saying that there are also Lean, Coq, and
dependent types. With this blogpost, I would like to summarize my experience
with [TLA<sup>+</sup>][TLA+], [TLC][TLA+ Tools], [Apalache][], and [Quint][].  I
share these learnings in the hope to spark new ideas about improving the tooling
for TLA<sup>+</sup>.

**Disclaimer:**  All opinions are of my own. I resigned from Informal Systems on
December 31, 2023 and have not been receiving any funding from them since then.
Even though I still have some equity there, not knowing its current value, I do
not feel financially motivated to promote their work or products. I am fixing
small issues in Quint, when my customers ask me to do that.

## 1. Why I am using TLA+

I am using TLA<sup>+</sup> in the new projects for [fun][protocols-made-fun.com]
and [profit][konnov.phd], mainly, by running the [Apalache][] model checker.
However, it is up to the customer to decide whether they want to use
TLA<sup>+</sup> or another syntax like [Quint][], or something else.

<img src="{{ site.baseurl }}/assets/images/heart-tlaplus.png"
  style="float: right; padding: 20pt;">

**TLA<sup>+</sup> is consistent with my prior knowledge on model checking.**
Before I started to learn TLA<sup>+</sup>, I spent some time learning model
checking algorithms and writing a (very much) domain-specific model checker
[ByMC][]. So I opened [Specifying Systems][] having a lot of baggage on
transition systems, Kripke structures, linear-temporal logic, computational-tree
logic, explicit-state model checking, symbolic model checking with BDDs and
SAT/SMT, abstractions and simulations, etc. Many of these topics are covered in
the [Handbook of Model Checking][].

As a result, I found it quite easy to grasp the concepts presented in the book.
I am not a historian, but this is probably because Leslie Lamport, Amir Pnueli,
Edmund Clarke, and many other researchers were actively working on these topics
and integrating their ideas in distributed algorithms and computer-aided
verification for long time.

So this is it. TLA<sup>+</sup> is pretty much what I expected from a general
specification language. It was definitely much easier for me to start using
TLA<sup>+</sup> for practical purposes than, e.g., learning Coq or Isabelle.

**TLA<sup>+</sup> has well-defined semantics.** It may come as a surprise to
some readers, but many programming languages still do not have formal semantics.
By formal semantics I do not mean formal English, but a set of consistent
mathematical definitions. Usually, someone defines formal semantics for a subset
of the programming language, and then they give up, because the general case is
too hard. If you are writing your own tool such as a model checker, this is
quite annoying, as you have to somehow define semantics in your tool, usually,
using your own judgment. Easy win for TLA<sup>+</sup> over programming
languages.

**TLA<sup>+</sup> offers a convenient set of primitives.** We don't have to
reinvent everything from scratch. Additionally, it provides a practical set of
primitives. Few engineers and protocol designers are interested in using Peano
arithmetic or effectively-propositional logic.

**The logic of TLA<sup>+</sup> is extremely flexible.** It is very easy
to switch between different levels of abstraction. This is extremely important
when modeling distributed systems. This is probably why some people keep
talking about refinement.

This is in contrast to verification tools that are tuned towards a specific
programming language. There, anything above the core abstractions requires
plenty of hacks.

**TLA<sup>+</sup> has a good level of automated analysis.** I am mainly
using the model checkers [Apalache][] and [TLC][] (unfortunately, TLC more often
does not scale to my problems than it does), but there is also the proof system
[TLAPS][]. When people ask me about Lean and Coq, it's kind of interesting, but
I am having hard time explaining a computer why a list reversal algorithm
reverses a list, or why two quorum sets have at least one element in common.  I
would rather like computers to disprove my hypotheses.

## 2. Lessons from Informal Systems and the Cosmos blockchains

We were actively using TLA<sup>+</sup> and Apalache in 2020-2022. As a result,
we wrote specifications of Tendermint, its light client, and IBC, see
[Tendermint TLA+ Spec][], [Light client TLA+ Spec][], [IBC TLA+ Specs][]. For
more details, see [Informal Q2 2020 Update][]. We used both TLC and Apalache. I
will only highlight several improvements to Apalache, even though there were a
lot of other exciting developments.

**Type checker.** Back then, Apalache had a lot of usability issues. For
instance, its type checker was very fragile and hard to use. In the first
version, we were writing type annotations as TLA<sup>+</sup> expressions. I
could not imagine that people would get so creative and start using operator
definitions in the annotation expressions. We completely rewrote the type
checker in 2021 and further improved it in 2022 by introducing precise type
inference for records, see [ADR-002][]. The [type checker][Snowcat Type Checker]
was essential for translating TLA<sup>+</sup> to [SMT][], as was laid out in the
[OOPSLA'19 paper].

Here is a code snippet that demonstrates type annotations for constants
and variables in a simple [labyrinth example][]:

```tla
CONSTANT
    \* The maximal x-coordinate.
    \* @type: Int;
    MAX_X,
    \* The maximal y-coordinate.
    \* @type: Int;
    MAX_Y,
    \* The set of walls.
    \* @type: Set(<<Int, Int>>);
    WALLS,
    \* The goal coordinates.
    \* @type: <<Int, Int>>;
    GOAL

VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    y
```

The type checker requires type annotations for constants and variables. Given
those, it tries to infer types for everything else using a modified version of
the type inference algorithm by [Damas and Milner][Damas-Milner]. In some cases,
type inference cannot distinguish between functions, sequences, tuples, and
records. In those cases, the type checker requires additional type annotations.

**Randomized symbolic execution.** At some point, we started to check properties
of the specifications that were too hard for bounded model checking. Of course,
one approach to the issue was to raise the level of abstraction. However, it was
not always possible without losing the engineers. Hence, we have introduced the
command `apalache-mc simulate` that randomly picks symbolic transitions instead
of non-deterministically choosing from the set of all enabled transitions. This
command is quite efficient for finding bugs, though it sacrifices completeness.
I will write a separate blog post on comparing `check` vs. [simulate][]. The
command name may be misleading; it does random+symbolic (randolic?) execution.

As a teaser, these are statistics from finding an agreement violation with
`apalache-mc check` on [Ben-Or's consensus][Ben_or83] for the case of too many
faults:

```
  Time (mean ± σ):     96.277 s ± 20.296 s
  Range (min … max):   68.131 s … 136.544 s    10 runs
```

And these are statistics for the same specification and the same invariant using
`apalache-mc simulate`:

```
  Time (mean ± σ):     163.336 s ± 184.750 s
  Range (min … max):   14.317 s … 609.343 s    10 runs
```

As we see, this random+symbolic execution is not the great on average. However,
there are cases, where it finds a counterexample way faster than bounded model
checking. Especially, when we run this search on multiple CPU cores, it is
finding counterexamples really fast. TODO: do that!

**Folds instead of recursion.** Recursive operators were introduced in
[TLA+ Version 2][], which appeared after [Specifying Systems][]. For example,
set cardinality (for finite sets) can be defined with a recursive operator:

```tla
RECURSIVE Cardinality(_)
Cardinality(S) ≜
  IF S = {}
  THEN 0
  ELSE 1 + Cardinality(S \ { CHOOSE y ∈ S })
```

Unfortunately, recursion (and loops) are a pain point of bounded model
checking.  First, a recursive operator does not have to terminate. Second, even
if it does terminate, it is impossible to predict the number of its iterations
in the general case. Obviously, the above operator has $|S|$ iterations.
Fortunately, many programming languages support bounded iteration called
`reduce` or `fold`, see the [Fold][] page on Wikipedia. We refactored Apalache
to work with folds instead of recursive operators:

```tla
EXTENDS Apalache

CardinalityFold(S) ≜
  LET Count(n, i) ≜ n + 1 IN
  ApaFoldSet(Count, 0, S)
```

More on that in [Folds in Apalache][]. A similar operator [FoldSet][] was
introduced in [TLA<sup>+</sup> community modules][community-modules]. Apalache
supports this operator as well.

**Improved stability.** Perhaps, the most interesting observation for me was
that in 2021 we were finding issues in Apalache, whenever we were writing a new
specification. We stopped finding new issues in 2022. People are still
submitting issues every now and then, but the current implementation is
significantly much more stable.

**Conversations with engineers.** Thanks to all that work, I had plenty of
conversations with engineers at Informal Systems as well as in the more global
Interchain/Cosmos ecosystem.

<img src="{{ site.baseurl }}/assets/images/01-bang.png"
  style="float: right; padding: 20pt;">

There were three recurrent themes in these conversations:

 1. Every time I was showing a TLA<sup>+</sup> specification to an engineer,
 they were asking about `/\`, `\/`, `\E`, `\A`, `=>`, and other operators.  Back
 then, the Unicode support in TLA<sup>+</sup> was not even a thing. When I was
 explaining the meaning of these operators, everything was clear. However, we
 were losing time in a meeting with every new person. We could use this time to
 discuss the specification itself. Instead, we were discussing the syntax of
 TLA<sup>+</sup>. There was no single engineer who said that they liked this
 part. Interestingly, these people did not want to write a specification, they
 just wanted to read it.

 1. An engineer would get excited about TLA<sup>+</sup> and literally write a
 program in every single detail, following good programming practices, but
 completely overdoing it. We all have seen that and all have done that.
 Surprisingly, the mantra "TLA<sup>+</sup> is not a programming language" did
 not stop them. They just treated TLA<sup>+</sup> as a programming language with
 strange syntax. There are plenty of languages with strange syntaxes around.  If
 they liked imperative languages, they wanted assignments are returns
 everywhere. If they liked functional languages, they wanted to wrap everything
 into Either and Option. The Rust engineers... they wanted to do both of these
 things.

 1. Perhaps, related to the previous point, everybody was asking whether it was
 possible to translate Rust, Golang, TypeScript, Python, whatever to
 TLA<sup>+</sup>, or the other way around. Every time, I had to explain that,
 yes, to some extent, it should be possible, but the outcome would be completely
 unusable in the both directions. People still keep asking these questions.

 1. Finally, every engineer wanted to connect their implementations to
 TLA<sup>+</sup> specifications. To this end, we introduced machine-readable
 output of traces in the [JSON format][ITF]. Moreover, [Andrey Kuprianov][]'s
 team has developed two tools for model-based testing: [Modelator][] and
 [Atomkraft][].

## 3. Conceptual and mental models

On the surface, it looked like people were only asking about the syntax, but it
was something deeper. I think I started understanding it a bit better after
reading [The Design of Everyday Things][] by Don Norman. Here are just two
sentences from the book that introduce *conceptual models* (p. 25):

> A conceptual model is an explanation, usually highly simplified, of how
 something works. It doesn't have to be complete or even accurate as long as it
 is useful.

<img src="https://images-na.ssl-images-amazon.com/images/S/compressed.photo.goodreads.com/books/1697900485i/164316035.jpg"
  style="float: right; padding: 20pt;">

When you buy a computer, nobody gives you a book that starts with: "Welcome to
the magical world of transistors!" Or, when you buy a fridge, nobody explains
you electricity or the Carnot cycle. I am afraid we are doing something like
that all the time, when we try to explain TLA<sup>+</sup> to newbies.

What are conceptual models in the world of TLA<sup>+</sup>? The canonical
conceptual models are given in the book on [Specifying Systems][] and [The TLA+
Video Course][] by Leslie Lamport. Hillel Wayne also presents another conceptual
model in his [Learn TLA+][] -- though it is more focused on [PlusCal][] -- but
exercises there are oriented towards another concept from the design book. When
the readers do exercises they start building their own *mental models* (p. 26):

> Mental models, as the name implies, are the conceptual models in people's
minds that represent their understanding of how things work. Different people
may hold different mental models of the same item, each dealing with a different
aspect of its operation: the models can even be in conflict.

I believe that these two concepts explain a lot. They explain why different
people like different aspects of TLA<sup>+</sup>: Like with a good book, we
interpret the message in various ways, building mental models of our own.
Moreover, as Andrew Helwer noticed in [TLA+ is more than a DSL for breadth-first
search][], many users of TLC believe that TLA<sup>+</sup> and TLC are exactly
the same thing. The explanation is very simple (not really a quote, just using
the style):

> The fastest way to build a solid mental model of TLA<sup>+</sup> is by running
TLC, unless you already know math and logic very well.

This is not really surprising. We all learn new topics by multiple iterations
and practice. I do not really know how people learn programming languages these
days. I still prefer reading a book, but I suspect that many people learn new
programming languages by interaction. For instance, it was possible for me to
start reading and writing Golang after doing [A Tour of Go][], though my code
was probably far from perfect.

I believe that every time people complained about the syntax and the tools, they
actually complained about the lack of a fast feedback loop, so they could keep
learning. With a programming language, you can just write some code and execute
it. However, "executable" is a taboo word in the TLA<sup>+</sup> community for
some reason, despite a large fragment of TLA<sup>+</sup> over finite sets being
executable. The closest thing to this feedback loop is actually TLC. There is
also [TLC REPL][], but it is probably not that well-known.

This also probably explains why so few people manage to pick up symbolic tools
(the stability issues aside). It is much harder to build a mental model there,
and there are not so many conceptual models around. On this topic, I have a new
idea on how to build a mental model of symbolic model checking for
TLA<sup>+</sup>. Subscribe to the blog below :blush:

## To be continued

As always, this text became too long. You will find the rest of the story in
Part 2.


[konnov.phd]: https://www.konnov.phd
[protocols-made-fun.com]: https://protocols-made-fun.com
[TLA+]: https://lamport.azurewebsites.net/tla/tla.html
[ByMC]: https://github.com/konnov/bymc
[Apalache]: https://apalache-mc.org/
[TLAPS]: https://proofs.tlapl.us/doc/web/content/Home.html
[Specifying Systems]: https://lamport.azurewebsites.net/tla/book.html
[Quint]: https://quint-lang.org/
[TLA+ Tools]: https://lamport.azurewebsites.net/tla/tools.html
[TLC]: https://lamport.azurewebsites.net/tla/tools.html
[Opinions on Quint]: https://www.reddit.com/r/tlaplus/comments/1fqf6e9/opinions_on_quint/
[TLA+ is more than a DSL for breadth-first search]: https://groups.google.com/g/tlaplus/c/g3WBUldS_ps
[The Future of TLA+]: https://groups.google.com/g/tlaplus/c/1tz1sYs2hxM
[Hacker News]: https://news.ycombinator.com/
[Handbook of Model Checking]: https://link.springer.com/book/10.1007/978-3-319-10575-8
[Tendermint TLA+ Spec]: https://github.com/cometbft/cometbft/blob/main/spec/light-client/accountability/TendermintAcc_004_draft.tla
[Light client TLA+ Spec]: https://github.com/cometbft/cometbft/blob/main/spec/light-client/verification/Lightclient_003_draft.tla
[IBC TLA+ Specs]: https://github.com/informalsystems/hermes/tree/master/docs/spec
[Informal Q2 2020 Update]: https://informal.systems/blog/q2-tech-update
[The Design of Everyday Things]: https://www.goodreads.com/book/show/164316035-the-design-of-everyday-things-design-of-everyday-thing-rev-e-paperback
[Specifying Systems]: https://lamport.azurewebsites.net/tla/book.html
[The TLA+ Video Course]: https://lamport.azurewebsites.net/video/videos.html
[Learn TLA+]: https://learntla.com/index.html
[Pluscal]: https://lamport.azurewebsites.net/tla/high-level-view.html#pluscal
[tdet-cover]: https://images-na.ssl-images-amazon.com/images/S/compressed.photo.goodreads.com/books/1697900485i/164316035.jpg
[SMT]: https://en.wikipedia.org/wiki/Satisfiability_modulo_theories
[Snowcat Type Checker]: https://apalache-mc.org/docs/tutorials/snowcat-tutorial.html
[OOPSLA'19 paper]: https://dl.acm.org/doi/10.1145/3360549
[simulate]: https://apalache-mc.org/docs/apalache/running.html#12-simulator-command-line-parameters
[TLA+ Version 2]: https://lamport.azurewebsites.net/tla/tla2-guide.pdf
[Modelator]: https://github.com/informalsystems/modelator
[Atomkraft]: https://github.com/informalsystems/atomkraft
[ITF]: https://apalache-mc.org/docs/adr/015adr-trace.html
[Andrey Kuprianov]: https://www.linkedin.com/in/andrey-kuprianov/
[community-modules]: https://github.com/tlaplus/CommunityModules
[FoldSet]: https://github.com/tlaplus/CommunityModules/blob/15317429e7db9be0b0f4acaa076d3c0bc6243de6/modules/FiniteSetsExt.tla#L6
[Fold]: https://en.wikipedia.org/wiki/Fold_(higher-order_function)
[Folds in Apalache]: https://apalache-mc.org/docs/apalache/principles/folds.html
[labyrinth example]: https://github.com/konnov/apalache-examples/tree/main/labyrinth
[Damas-Milner]: https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
[ADR-002]: https://apalache-mc.org/docs/adr/002adr-types.html
[A Tour of Go]: https://go.dev/tour/welcome/1
[TLC REPL]: https://www.reddit.com/r/tlaplus/comments/hpvkcw/demo_of_the_new_tlc_repl/
[Ben_or83]: https://github.com/konnov/apalache-examples/blob/main/ben-or83/Ben_or83.tla