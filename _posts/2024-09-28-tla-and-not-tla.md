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
not feel financially motivated to promote their work or products. I am fixing
small issues in Quint, when my customers ask me to do that.

## 1. Why I am using TLA+

I am using TLA<sup>+</sup> in the new projects for fun and [profit][konnov.phd],
mainly, by running the [Apalache][] model checker. However, it is up to the
customer to decide whether they want to use TLA<sup>+</sup> or another syntax
like [Quint][], or something else.

![I love TLA+]({{ site.baseurl }}/assets/images/heart-tlaplus.png)

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

## 2. Lessons from Informal Systems and the Cosmos ecosystem

We were actively using TLA<sup>+</sup> and Apalache in 2020-2022. As a result,
we wrote specifications of Tendermint, its light client, and IBC, see
[Tendermint TLA+ Spec][], [Light client TLA+ Spec][], [IBC TLA+ Specs][]. For
more details, see [Informal Q2 2020 Update][]. We used both TLC and Apalache.
Back then, Apalache had a lot of usability issues. For instance, its type
checker was very fragile and hard to use. We completely rewrote the type checker
in 2021 and further improved it in 2022. Perhaps, the most interesting
observation for me was that in 2021 we were finding issues in Apalache every
time we were writing a new specification. We stopped finding new issues in 2022.
People are still submitting issues every now and then, but the current
implementation is significantly more stable.

Thanks to that work, I had plenty of conversations with engineers at Informal
Systems as well as in the more global Cosmos ecosystem.

![Kind of Cosmos]({{ site.baseurl }}/assets/images/01-bang.png)

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

## 3. Conceptual models

On the surface, it looked like people were only asking about the syntax, but
their frustration was deeper. I think I started understanding it a bit better
after reading [The Design of Everyday Things][]. Here are just two sentences
from the book that introduce conceptual models (p. 25):

> A conceptual model is an explanation, usually highly simplified, of how
 something works. It doesn't have to be complete or even accurate as long as it
 is useful.

Basically, when you buy a computer, nobody gives you a book that starts with:
"Welcome to the magical world of transistors!" Or, when you buy a fridge, nobody
explains you electricity or the Carnot cycle. I am afraid we are doing something
like that all the time, when we try to explain TLA<sup>+</sup> to newbies.

![The Design of Everyday Things](https://images-na.ssl-images-amazon.com/images/S/compressed.photo.goodreads.com/books/1697900485i/164316035.jpg)

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
[Tendermint TLA+ Spec]: https://github.com/cometbft/cometbft/blob/main/spec/light-client/accountability/TendermintAcc_004_draft.tla
[Light client TLA+ Spec]: https://github.com/cometbft/cometbft/blob/main/spec/light-client/verification/Lightclient_003_draft.tla
[IBC TLA+ Specs]: https://github.com/informalsystems/hermes/tree/master/docs/spec
[Informal Q2 2020 Update]: https://informal.systems/blog/q2-tech-update
[The Design of Everyday Things]: https://www.goodreads.com/book/show/164316035-the-design-of-everyday-things-design-of-everyday-thing-rev-e-paperback
