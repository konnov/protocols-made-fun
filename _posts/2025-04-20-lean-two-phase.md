---
layout: post
title: "Specifying and simulating two-phase commit in Lean4"
date: 2025-04-20
categories: lean
tlaplus: true
math: true
lean: true
---

**Author:** [Igor Konnov][]

**Tags:** specification lean distributed simulation pbt tlaplus

More and more people mention the [Lean] theorem prover in my bubble. Just the
last week [Ilya Sergey][] and co announced [Veil][], an Ivy-like verification
framework on top of Lean. Luckily, I heard a long tutorial on Lean by [Sebastian
Ullrich][] and [Joachim Breitner][] at [VSTTE24][]. The interesting thing about
Lean is that it's not only a theorem prover, but also a decent [programming
language][lean-pl].

So, I have decided to take on a case study of specifying a relatively simple yet
interesting distributed protocol in Lean. For this reason, I did not choose a
more complex consensus algorithm and instead settled on two-phase commit, for
the following reasons:

 - It is an interesting distributed protocol with applications in databases.
 
 - It has been [specified in TLA<sup>+</sup>][two-phase-tla] by Leslie Lamport,
 so we do not have to think about choosing the right level of abstraction.  We
 simply follow the same level of abstraction as in the TLA<sup>+</sup>
 specification.

It took me about *three hours* to translate the TLA<sup>+</sup> specification
into [Lean spec][two-phase-lean], occasionally debating syntax and best
practices with ChatGPT and Copilot along the way. See the [Functional
specification][fun-spec] and [System-level specification][sys-spec]. I had to
invent several patterns on the way, as specifying distributed algorithms in Lean
looks like terra incognita :dragon:. Importantly, I tried to stay close to the
original TLA<sup>+</sup> specification in spirit, but not in the dogmas.  My
goal was to specify the protocol in a way that looks natural in Lean, instead of
literally replicating the TLA<sup>+</sup> idioms.

What is intriguing is that the resulting specification had the necessary
ingredients to be **executable**, since Lean can compile a large subset of its
language into an executable file. Obviously, it does not automatically generate
a distributed implementation of our distributed protocol. As we know from
[Quint][], it is quite useful to have a randomized simulator, especially, if
there are no other automatic analysis tools around.

As the next step, I wrote a very simple randomized simulator to check the
properties against the specification &mdash; see [Randomized
simulation][spec-sim]. It turned out to be even easier to implement in Lean than
I expected. After about *four hours* of work, I had the simulator running
and showing counterexamples. Maybe it is because I knew exactly what was needed,
having written the Quint simulator a couple of years ago. Or maybe it is because
Lean does not shy away from the occasional need for imperative code. Of course,
this is all done through ["monads"][lean monads], but they are relatively easy
to use in Lean &mdash; even if you are not quite ready to buy into the FP
propaganda.

Of course, if you have been reading the [orange website][hn], you should tell me
that writing a simulator by hand is not the way to go. Instead, we should use
property-based testing. Well, after the experiments with the simulator, this is
exactly what I did with [Plausible][]. See [Property-based testing][spec-pbt].
To my disappointment, PBT took took me about *six hours* of work, delivering
less impressive results in comparison to the simulator. I wasted so much time
figuring out the generators and trying to define my own instances of
`Sampleable` and `Shrinkable`, that I needed something `Drinkeable` after that.
This was a bit unexpected for me, as it was my first time writing property-based
tests (PBT) in Lean &mdash; though not my first time with PBT in general, since
I had prior experience using [ScalaCheck][] in Scala for [Apalache][]. While PBT
might be the way to go in the long run, at the moment, I find Plausible a bit
too hard to use. To be fair, ScalaCheck was not trivial to figure out, too. For
some reason, the PBT frameworks assume that everybody knows Haskell and
[QuickCheck][].

After having played with the simulator and the Plausible tests, I was quite
satisfied with my spec. (My experiments with more advanced language features did
not lead to serious improvements in the spec.) Obviously, the next question is
whether we want to prove that the protocol satisfies its state invariants.  At
the high-level, it is clear how to proceed: Discover an inductive invariant,
prove its inductiveness and show that the inductive invariant implies the state
invariants of the protocol. I must have an inductive invariant for the
TLA<sup>+</sup> spec of two-phase commit lying somewhere. Even if the inductive
invariant is lost, I am pretty sure that it is relatively easy to find it again
by iteratively running [Apalache][]. Even [TLC][] should work for the two-phase
commit. At the lower levels, it is hard to predict how much effort it would take
to write complete proofs with Lean tactics. This is definitely something to do
in another sprint.

To sum it up, I quite liked the experience with Lean as a programming and
specification language. I will definitely add it to my set of available tools.
If someone wants to write protocol specs in Lean, say, instead of TLA<sup>+</sup>,
Quint, or Python, I would be [happy to help][].

The rest of the blogpost goes into details. If you are interested, keep reading.
If not, you are free to stop here.

## 1. A brief intro to Two-phase commit and the TLA<sup>+</sup> specification

I am giving only a very brief introduction in two-phase commit. It is quite a
famous protocol. [Gray & Lamport'04][Gray-Lamport04] (Sec. 3) explain the
protocol nicely and by using the same vocabulary, as in the TLA<sup>+</sup>
specification. Moreover, Leslie Lamport explains the protocol idea and the
specification in his [Lecture 6][lamport-2phase] of the TLA<sup>+</sup> Course
on YouTube.

Here is the elevator pitch of two-phase commit: One transaction manager and $N$
resource managers have to agree on whether to commit or abort a transaction,
e.g., a database transaction. If they all decide to commit the transaction,
including the transaction manager, they all commit it. If at least one of them,
decides to abort, none of them commits the transaction.

The sequence diagram below shows the happy path: Everyone decides to commit
the transaction, and everybody does so:

![A happy path where TM commits][happy-path]

The following diagram shows an unhappy scenario, when the transaction manager
declines the transaction, even though all resources managers were ready to commit:

![An unhappy path where TM aborts][unhappy-path]

## 3. Functional specification in Lean

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/a00be5d914b9c7e11494a8f174f7d1a79c00bdd4/twophase/Twophase/Functional.lean
  lean 10-12
 %}

## 4. System-level specification in Lean

## 5. Randomised simulation in Lean

## 6. Property-based testing in Lean

[Igor Konnov]: https://konnov.phd
[Lean]: https://github.com/leanprover/lean4
[Veil]: https://github.com/verse-lab/veil/
[Ilya Sergey]: https://ilyasergey.net/
[VSTTE24]: https://www.soundandcomplete.org/vstte2024.html
[Sebastian Ullrich]: https://sebasti.a.nullri.ch/
[Joachim Breitner]: https://www.joachim-breitner.de/
[lean-pl]: https://lean-lang.org/functional_programming_in_lean/title.html
[lamport-2phase]: https://youtu.be/U4mlGqXjtoA?t=117
[two-phase-tla]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla
[Gray-Lamport04]: https://www.microsoft.com/en-us/research/publication/consensus-on-transaction-commit/
[two-phase-lean]: https://github.com/konnov/leanda/tree/main/twophase/Twophase
[fun-spec]: #3-functional-specification-in-lean
[sys-spec]: #4-system-level-specification-in-lean
[spec-sim]: #5-randomised-simulation-in-lean
[spec-pbt]: #6-property-based-testing-in-lean
[lean monads]: https://lean-lang.org/functional_programming_in_lean/monads.html
[Quint]: https://konnov.phd/quint
[hn]: https://news.ycombinator.com/
[Plausible]: https://github.com/leanprover-community/plausible
[Apalache]: https://github.com/apalache-mc/apalache
[ScalaCheck]: https://scalacheck.org/
[QuickCheck]: https://hackage.haskell.org/package/QuickCheck
[TLC]: https://github.com/tlaplus/tlaplus
[happy to help]: {{ 'contact/' | relative_url }}
[happy-path]: {{ site.baseurl }}/img/two-phase-commit.png
[unhappy-path]: {{ site.baseurl }}/img/two-phase-abort.png