---
layout: post
title: "Why I use TLA+ and not(TLA+)"
date: 2024-09-28
categories: specification modelchecking tlaplus quint
quint: true
tlaplus: true
math: true
---

Recently, we have seen several interesting write-ups in the
[TLA<sup>+</sup>][TLA+] ecosystem:

 1. Leslie Lamport posted the document on [The Future of TLA+][].
 
 1. Andrew Helwer wrote the blogpost called [TLA+ is more than a DSL for
 breadth-first search][].
 
 1. prestonph asked about [Opinions on Quint][].

These three posts made me think about the TLA<sup>+</sup>-related work I have
been doing since 2016. There was also a bunch of discussions on [Hacker News][],
but those seem to have saturated to saying that there are also Lean, Coq, and
dependent types. With this blogpost, I would like to summarize my experience
with [TLA<sup>+</sup>][TLA+], [TLC][TLA+ Tools], [Apalache][], and [Quint][].  I
share these learnings to spark new ideas about improving the tooling for
TLA<sup>+</sup>, not to start a flame war.

**Disclaimer:**  All opinions are of my own. I resigned from Informal Systems on
December 31, 2023 and have not been receiving any funding from them since then.
Even though I still have some equity there, not knowing its current value, I do
not feel financially motivated to promote their work or products.

## 1. Why I am using TLA+

I am using TLA<sup>+</sup> in the new projects for fun and [profit][konnov.phd],
mainly, by running the [Apalache][] model checker. However, it is up to the
customer to decide whether they want to use TLA<sup>+</sup> or another syntax
like [Quint][], or something else.

**TLA<sup>+</sup> is consistent with my prior knowledge on model checking.**
Before I started to learn TLA<sup>+</sup>, I spent some time learning model
checking algorithms and writing a (very much) domain-specific model checker
[ByMC][]. So I opened [Specifying Systems][] having a lot of baggage on
transition systems, Kripke structures, linear-temporal logic, computational-tree
logic, explicit-state model checking, symbolic model checking with BDDs and
SAT/SMT, abstractions and simulations, etc. Many of these topics are covered in
the [Handbook of Model Checking][].

As a result, I found it quite easy to grasp the concepts presented in the book.
I am not a historian, but this is probably because Amir Pnueli, Edmund Clarke,
Leslie Lamport, and many other researchers were actively working on these topics
and learning from one another for long time. I must admit that it took me much
longer to train myself to type TLA<sup>+</sup> without introducing obvious
syntax and semantic errors, despite having sufficient mathematical training and
over 10 years of experience typing papers in LaTeX.

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
primitives. Few engineers and protocol designers are interested in Peano
arithmetic or similar concepts.

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

## 2. Lessons from Informal Systems and the Cosmos ecosystem

## 3. Conceptual models

## 4. How do people learn to program?

## 5. Quint: not(TLA+)

## 6. Is it all about syntax?



[konnov.phd]: https://www.konnov.phd
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