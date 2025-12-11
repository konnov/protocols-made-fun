---
layout: post
title: "Symbolic Testing of TFTP implementations"
date: 2025-12-09
categories: tlaplus
tlaplus: true
math: true
shell: true
typescript: true
---

**Author:** [Igor Konnov][]

**Date:** December 10, 2025

## 1. Introduction

As promised in the [blog post on small-scope hypothesis][small-scope], I am
continuing with the main body of the talk that I presented at the internal
Nvidia FM Week 2025. This work aims at demonstrating how to answer the
following two questions with [Apalache][]:

<p class="highlight-question"><strong><em>
  1. How to test the actual implementation against its TLA<sup>+</sup> specification?
</em></strong></p>

<p class="highlight-question"><strong><em>
  2. How to test the TLA<sup>+</sup> specification against the actual implementation?
</em></strong></p>

For long time, these questions have been mostly ignored by the TLA<sup>+</sup>
community. Over the last 4-5 years, researchers started to look into these two
questions and found out that having a connection between the specification and
the implementation is much more useful than it was initially thought. (The
engineers were telling this to me that all the time!) Check [the prior work
section](#10-prior-work) for the papers and talks on this topic.  Roughly
speaking, the approaches follow the two ideas:

 - **Model-based testing (MBT)**. The TLA<sup>+</sup> specification is used to
 generate test cases that are then executed against the implementation. This is
 an answer to question 1 above. The state exploration is driven by the
 specification. Hence, we are testing, whether the implementation matches the
 inputs and outputs, as produced by the specification.
 
 - **Trace validation (TV)**. The traces collected from the implementation are
 checked against the TLA<sup>+</sup> specification. This is an answer to
 question 2 above. State exploration is driven by the implementation, e.g., by
 executing the existing test suites, or just running the system for some time.
 Hence, we are testing whether the specification matches the inputs and outputs
 of the implementation. Alternatively, we may check whether the implementation
 states may be lifted to the specification states, in order to produce a
 feasible trace in the specification.

If you re-read the description of MBT and TV above, you may notice that there
are two more dimensions of how to do testing:

 - **State-based**. In this case, we have to establish a relation between the
 implementation states and the specification states in each step of the trace.
 This usually done by defining mapping functions, either from the implementation
 states to the specification states, or vice versa. Notice that mapping an
 implementation state to a specification state is usually much easier, as it
 involves *state abstraction* (e.g., dropping some variables). Mapping a
 specification state to an implementation state is more difficult, as it
 involves *state concretization*, e.g., choosing a representative concrete value
 for each abstract value in the specification state. For example, if the
 specification says $x \in [10, 20]$, then we have to choose a concrete value
 for $x$ in this range, e.g., at random.
 
 - **Action-based**. In this case, we have to establish a relation between the
 implementation actions and the specification actions. Again, we would need to
 define mappings. Interestingly, in my experience, defining action mappings is
 way easier than defining state mappings.

## 2. Model-based testing and trace validation

### 2.1. Model-based testing in one picture

Without going into too many details, the following picture illustrates the main
idea of model-based testing. We generate an "interesting" trace with a model
checker, e.g., with [Apalache][]. This trace is fed to the test harness that:
(1) does action concretization, (2) executes the actions against the
implementation. The moment the implementation refuses to replay an action, we
know that there is a divergence. Notice that we often do not even need to query
the system for its current state, as we only care about the actions.

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/mbt.svg" alt="Model-based testing">
</picture>

One downside of this approach is that the model checker can be quickly overwhelmed
by the many possible action interleavings unless the search scope is further
restricted. In my experience, the SMT solver Z3 slows down dramatically when it
must solve two problems simultaneously:

 1. Choose a sequence of actions (a schedule) to explore, and

 1. Find variable assignments (states) that produce a feasible trace for the
    chosen schedule.

When a schedule is fixed, the SMT solver must solve far fewer constraints
because it mainly propagates values through the actions. If the solver must also
pick a schedule, it must backtrack along two axes: (1) schedules and (2) states.
This increases solving times in practice.

To mitigate this, Apalache lets you randomly sample schedules and execute them
symbolically. To enumerate different "interesting" schedules, the user can
define a view operator, which usually projects state variables to more abstract
values. The model checker will then produce traces projected onto those views.
This works significantly better for test generation in practice. However, this
exploration strategy is fixed and cannot be changed without modifying Apalache
itself.

### 2.2. Trace validation in one picture

Trace validation is conceptually simpler than model-based testing. We simply
execute the system under test (SUT) and collect traces. These traces are then
mapped to the abstract states, if necessary, and checked against the
specification.

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/tv.svg" alt="Trace validation">
</picture>

This approach has been tried in multiple projects that use the exhaustive-state
model checker [TLC][] as the back-end solver. See [the prior work
section](#10-prior-work).

Trace validation also has its challenges:
 
 1. We need a good test suite, in order to produce "interesting" traces.
 However, test cases are usually written for the happy-path scenarios. Hence,
 it is easy to miss handling of error cases and faults. [Srinidhi Nagendra et
 al. (2025)][N25] address this issue by fuzzing the tests.
 
 1. Someone has to instrument the SUT to trace the relevant events. In some
 cases, it easy to do, e.g., by tracing message exchanges, as presented by
 [Markus Kuppe et. al. (2024)][K24b] In other cases, it may be quite difficult
 to do, e.g., when we want to dump the internal states of the SUT. In a
 multi-threaded system this may require a global lock and traversing large data
 structures. In a distributed system, this may further require a distributed
 snapshot or using vector clocks.
 
 1. We have to run the whole system to collect traces. It is hard to isolate one
 component, e.g., one network node.

## 3. Interactive symbolic testing with SMT

As we can see, both model-based testing and trace validation in their above
formulation are non-interactive. They both require a complete trace to be
produced first, and there is no feedback loop between the specification and the
implementation.

There is a third way to do conformance testing that leverages SMT solvers, yet
receives feedback from the implementation during the testing. I am not sure how
it is called exactly, so I would call it **interactive symbolic testing**.  I
think the first time I heard about this approach was from [Giuliano Losa][],
when he explained the paper by [Ken McMillan and Leonore Zuck (2019)][MZ19] to
me. The idea is to generate an action with the SMT solver by following the
specification, execute it against the implementation, and then feed the results
back to the SMT solver to generate the next action. This way, we can
systematically explore the protocol specification while getting feedback from
the implementation.

The picture below illustrates this approach, by approximately following the
internal transition executor of Apalache.

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/symbolic-testing.svg" alt="Symbolic testing">
</picture>
 
## 4. The new JSON-RPC API of Apalache

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/apalache-api.svg" alt="Apalache JSON-RPC API">
</picture>

## 10. Prior Work

In this section, I've collected the previous work on model-based testing and
runtime monitoring with TLA<sup>+</sup>:

 - Nagendra et. al. Model guided fuzzing of distributed systems (2025).
   Check [the talk][N25].

 - Cirstea, Kuppe, Merz, Loillier. Validating Traces of Distributed Systems
   Against TLA+ Specifications (2024). Check the
   [arxiv paper](https://arxiv.org/abs/2404.16075).

 - Chamayou et. al. Validating System Executions with the TLA+ Tools (2024).
   See [the talk][K24b].

 - Halterman. Verifiability Gap: Why We Need More From Our Specs and
   How We Can Get It (2020).
   See [the talk](https://www.youtube.com/watch?v=itcj9j2yWQo).
  
 - Davis et al. eXtreme Modelling in Practice (2020).
   See [the talk](https://www.youtube.com/watch?v=IIGzXX72weQ).

 - Kupriyanov, Konnov. Model-based testing with TLA+ and Apalache (2020).
   See [the talk](https://www.youtube.com/watch?v=aveoIMphzW8).
  
 - Pressler. Verifying Software Traces Against a Formal Specification with
   TLA<sup>+</sup> and TLC (2018).
   Check [the paper](https://pron.github.io/files/Trace.pdf).

I am pretty sure that this list is incomplete, so please let me know if you are
aware of any other relevant work.


[Igor Konnov]: https://konnov.phd
[Lean]: https://lean-lang.org/
[TLC]: https://github.com/tlaplus/tlaplus
[Apalache]: https://apalache-mc.org
[TLAPS]: https://proofs.tlapl.us/
[TLA<sup>+</sup>]: https://tlapl.us/
[Z3]: https://github.com/Z3Prover/z3
[GNU parallel]: https://www.gnu.org/software/parallel/
[Apalache JSON-RPC API]: https://github.com/apalache-mc/apalache/tree/main/json-rpc
[small-scope]: {% link _posts/2025-12-02-small-scope.md %}
[N25]: https://www.youtube.com/watch?v=DO8MvouV29M
[K24b]: https://www.youtube.com/watch?v=NZmON-XmrkI
[MZ19]: https://www.mcmil.net/pubs/SIGCOMM19.pdf
[Giuliano Losa]: https://www.losa.fr/