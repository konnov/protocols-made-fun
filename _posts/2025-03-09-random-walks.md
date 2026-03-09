---
layout: post
title: "All you need is a simulator? Nope"
date: 2026-03-09
author: Igor Konnov
categories: testing model-checking
tlaplus: true
math: true
shell: true
python: true
hidden: true
feed: true
---

**Author:** [Igor Konnov][]

**Date:** March 09, 2026

**Punchline: Testing distributed protocols with random simulation and stateful
property-based testing (PBT) is not enough!** Yes, running a simulator for days
is better than doing manual testing or just running unit tests. But **you will
miss states, which may expose bugs**. **Even on very small systems.** I have
been saying exactly this to many software engineers. Many times. However,
whiteboard arguments do not help. As humans, we have a great deal of trust in
probabilities, and our intuitive understanding of randomness is often wrong.
Hence, I am giving you concrete figures and plots in this blog post. I must
admit that my own intuition was also wrong: I expected fewer random walks to be
needed to achieve good coverage. For a quick glance, see [Quick
summary](#quick-summary).

Achieving **complete coverage with random walks is hard**. This is especially
important to know, **if you are using them to produce test cases for your
implementation**. It is also crucial to know, in case you generate an
implementation of a distributed protocol with AI tools and **hope for random
walks/PBT to work as an ultimate guardrail**.

Don't get me wrong. I like PBT and simulators (having written the [Quint][]
simulator). I believe that these tools are must-have tools for testing.  See my
recent blog post on [Property-based testing, adversarial developers, and
LLMs][pbt-llms]. However, they are not the only tools that we need to make sure
that our systems work as expected. This is especially true now, when we do not
have time to properly design and review the AI-generated code.

**Why now?** It has always been difficult to compare search procedures that were
developed by different branches of computer science. Everyone wanted to promote
their technique as the ultimate winner. Want to compare property-based testing
and model checking? Bad luck. Different tools require different inputs. Some are
libraries for programming languages (like [QuickCheck][]), some are tools for
specification languages (like [TLC][] and [Apalache][]).  Now it is much faster
to design frameworks, to experiment with multiple search procedures. It is also
easier to do reproducible experiments with LLMs. Good times, if you know how to
conduct experimental research.

{% include tip.html content="In contrast to the previous blog posts, I do not
provide the artifacts for download. AI slop forks are real. It still takes me
several days to design and conduct the experiments on a beefy machine, as well
as to find the right format to interpret and plot the data. Even with the help
of the frontier models, though they are of great help. It only takes 10-15
minutes to repackage the benchmarks and results with an AI tool, having the
experimental data. Hence, I am sharing my lab book with the customers and
researchers, upon request."
%}

<a id="quick-summary"></a>

## 1. Quick summary for the impatient readers

Look at two groups of figures below. They summarize the results of running
random walks on specifications of three prominent distributed protocols:
two-phase commit, readers-writers, and FPaxos (see [Benchmarks](#benchmarks)).
The figures show the coverage achieved by random walks, with 100% being the
numbers of distinct states (reported by the model checker TLC). In addition, we
plot the running times of the random walks, with the values plotted against the
right y-axis. All running times are on a AMD Ryzen 9 5950X processor (16
physical, 32 logical cores), 128 GB memory.

### 1.1 Coverage for minimal instances

In this set of experiments, we do random walks for the minimal instances of the
benchmarks. We start with the **meaningful default** of 100,000 random walks,
with at most 100 steps per walk. As you can see from Figure 1, only in the case
of two-phase commit and two resource managers, we achieve complete state
coverage. This is not surprising, since this instance has only 56 states. It's
tiny! For two-phase commit with three resource managers and readers-writers with
three actors, we achieve 85-90% coverage. This is also in the reasonable range.
On **FPaxos with two acceptors, we achieve the 77.5% coverage with 100k random
walks**. This is a bit worrying, since the state space is about 37k states.

The good news is that we can push all of the above benchmarks to achieve over
99% coverage. As you can see in the figures, it takes **10 million random walks
to achieve 99% coverage**. In addition to that, **these runs require 1-2
hours**.

**All of the above benchmarks are quite small by the model checking
standards. They have tens of thousands of states. It takes TLC only 1-3 seconds
to explore the state space and check the invariants for each of these
benchmarks.**

<div class="figure-grid">
  <figure>
    <a href="{{ site.baseurl }}/img/random-walks/twophase-n2-coverage.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/random-walks/twophase-n2-coverage.png"
        alt="Coverage of random walks for the two-phase commit benchmark with 2 resource managers">
    </picture></a>
    <figcaption>Figure 1.a: Two-phase commit, 2 RMs.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/random-walks/twophase-n3-coverage.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/random-walks/twophase-n3-coverage.png"
        alt="Coverage of random walks for the two-phase commit benchmark with 3 resource managers">
    </picture></a>
    <figcaption>Figure 1.b: Two-phase commit, 3 RMs.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/random-walks/rw-inst3-coverage.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/random-walks/rw-inst3-coverage.png"
        alt="Coverage of random walks for the readers-writers benchmark with 3 actors">
    </picture></a>
    <figcaption>Figure 1.c: Readers-writers, 3 actors.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/random-walks/fpaxos-inst2-coverage.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/random-walks/fpaxos-inst2-coverage.png"
        alt="Coverage of random walks for the FPaxos benchmark with 2 acceptors">
    </picture></a>
    <figcaption>Figure 1.d: FPaxos, 2 acceptors.</figcaption>
  </figure>
</div>

### 1.2 Slightly larger instances

What happens if we take the instances that are still small, but have 1-2
participants more? Figure 2 shows the results of doing random walks on these
instances.

As you can see, with the meaningful default of 100,000 random walks, we achieve
extremely poor coverage, about 25-30% on the benchmarks up to 2 million states.
**On FPaxos with 4 acceptors, we achieve only 3% coverage after 100,000
random walks**. Really bad!

To see how far we could push the coverage, we did the experiments with 10-100
million random walks. It is clear that **in 1-2 hours of simulation we get to
60-80% coverage**. It is good, but not great. When we push FPaxos with 3
acceptors to 100 million random walks, we get to 94.5% coverage. Nice, though it
took us 7.5 hours to get there. However, **on FPaxos with 4 acceptors, we get a
poor coverage of 60.4% even with 100 million random walks, which took us 8.5
hours to run**. This benchmark has about 11 million states. So it is reasonably
large, but, again, **not that large by the model checking standards**.

Again, **it takes the model checker TLC up to 10 minutes to enumerate all the
states and check the invariants for these instances**, whereas we have been
**running the simulations for hours!** This is especially
striking, given that we are **running optimized simulators in Rust**.

<div class="figure-grid">
  <figure>
    <a href="{{ site.baseurl }}/img/random-walks/twophase-n5-coverage.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/random-walks/twophase-n5-coverage.png"
        alt="Coverage of random walks for the two-phase commit benchmark with 5 resource managers">
    </picture></a>
    <figcaption>Figure 2.a: Two-phase commit, 5 RMs.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/random-walks/rw-inst4-coverage.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/random-walks/rw-inst4-coverage.png"
        alt="Coverage of random walks for the readers-writers benchmark with 4 actors">
    </picture></a>
    <figcaption>Figure 2.b: Readers-writers, 4 actors.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/random-walks/fpaxos-inst3-coverage.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/random-walks/fpaxos-inst3-coverage.png"
        alt="Coverage of random walks for the FPaxos benchmark with 3 acceptors">
    </picture></a>
    <figcaption>Figure 2.c: FPaxos, 3 acceptors.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/random-walks/fpaxos-inst4-coverage.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/random-walks/fpaxos-inst4-coverage.png"
        alt="Coverage of random walks for the FPaxos benchmark with 4 acceptors">
    </picture></a>
    <figcaption>Figure 2.d: FPaxos, 4 acceptors.</figcaption>
  </figure>
</div>

<a id="benchmarks"></a>

## 2. The benchmarks

As benchmarks, we use three specifications of distributed protocols. These are
prominent examples from the repository of [TLA+ Examples][]:

 - **Two-phase commit**. This is the famous two-phase commit. The specification
 is explained in [Consensus on Transaction Commit][GrayLamport06] by Jim Gray
 and Leslie Lamport. You can check the TLA<sup>+</sup> specification in
 [TwoPhase.tla][].
 
 - **Readers-writers**. This is a solution to the [Readers-Writers Problem][].
 The TLA<sup>+</sup> specification by Stephan Merz can be found in
 [ReadersWriters.tla][].
 
 - **FPaxos**. This is [Flexible Paxos][] by Heidi Howard, Dahlia Malkhi, and
 Alexander Spiegelman. The TLA<sup>+</sup> specification can be found in
 [FPaxos.tla][].

All of the above specifications are parameterized in the number of participating
processes. We consider several instances of each benchmark. To give you an idea
of their state space size (the number of reachable states), we compute the
figures with [TLC][]. The reachable states are called *distinct states* in TLC,
whereas *produced states* are the number of states that TLC generates during the
search. Another important metric is the *diameter* of the state space, which is
the length of the longest shortest path between any two reachable states (read
it again!).

As you can see from Table 1, these transition systems are not tiny, but they are
actually small by the model checking standards. Surprisingly, they are
sophisticated enough to challenge random walks! **Distributed protocols are
hard.**

<figure markdown="1">

| Benchmark        | Instance                    | Distinct states  | Produced states | Diameter | TLC times |
| ---------------- | --------------------------- | ---------------- | --------------- | -------- | --------- |
| Two-phase commit | 2 resource managers         | 56               | 154             | 8        | 1 sec     |
|                  | 3 resource managers         | 288              | 1,146           | 11       | 2 sec     |
|                  | 5 resource managers         | 8,832            | 58,146          | 17       | 2 sec     |
| Readers-writers  | 2 readers/writers           | 390              | 935             | 9        | 2 sec     |
|                  | 3 readers/writers           | 21,527           | 59,674          | 13       | 2 sec     |
|                  | 4 readers/writers           | 2,192,020        | 7,069,237       | 17       | 1 min     |
| FPaxos           | 2 acceptors                 | 36,953           | 245,288         | 19       | 4 sec     |
|                  | 3 acceptors                 | 362,361          | 2,697,682       | 25       | 21 sec    |
|                  | 4 acceptors                 | 11,279,393       | 96,056,172      | 31       | 9 min     |

<figcaption>Table 1: The state space size of the benchmarks</figcaption>
</figure>

In the experiments, I am using a custom framework to represent the above
**specifications as programs** that makes it easy to experiment with
different search procedures. To make sure that these specifications faithfully
represent the original TLA<sup>+</sup> specifications, I do the following:

 1. do a code review (obviously),

 1. automatically translate the programmatic specifications to TLA<sup>+</sup>
   and check them with TLC,

 1. run a custom-tailored model checker to compute the number of distinct states
   and check the invariants.

<a id="experimental-results"></a>

<a id="what-are-random-walks"></a>

## 3. What are random walks and state enumeration?

I have mentioned random walks and state enumeration multiple times so far.
Let's clarify what these terms mean. The concept of a random walk is intuitively
simple, though the details matter. Instead of looking at a large specification,
let's look at a simple example of a system that models adding and removing
workers from a pool. This example is inspired by the example in [Parameterize
Your Actions][learntla-parameterize] by Hillel Wayne. We add the variable
`count` to have a meaningful invariant. The specification is shown below. Even
if you do not know TLA<sup>+</sup>, it should be easy to understand.  If you
still have trouble understanding it, just ask an LLM, they are good at
explaining TLA<sup>+</sup> specifications.

<figure markdown="1">

```tla
EXTENDS Integers, FiniteSets

CONSTANTS
    (* The set of workers to choose from. *)
    (* @type: Set(Int);                   *)
    Worker

VARIABLES
    (* The set of active workers.         *)
    (* @type: Set(Int);                   *)
    active,
    (* The number of active workers.      *)
    (* @type: Int;                        *)
    count

(* Add a worker w to the set of active workers, if it is not already active. *)
(* @type: (Int) => Bool;                                                     *)
Add(w) ≜ w ∉ active ∧ active' = active ∪ {w} ∧ count' = count + 1

(* Remove a worker w from the set of active workers, if it is active.        *)
(* @type: (Int) => Bool;                                                     *)
Remove(w) ≜ w ∈ active ∧ active' = active \ {w} ∧ count' = count - 1

(* Initialize the system with no active workers and a count of zero.         *)
Init ≜ active = {} ∧ count = 0

(* In a next state, either add a worker or remove a worker.                  *)
Next ≜ ∃ w ∈ Worker:
          Add(w) ∨ Remove(w)

(* An invariant: `count` matches the cardinality of the active set.          *)
Inv ≜ (count = Cardinality(active))
```

<figcaption>Figure 3: TLA<sup>+</sup> specification for the Workers example.</figcaption>
</figure>

If we fix the set of workers to be `Worker = {1, 2}`, we get a nice labelled
transition system (LTS) of 4 states. The graphical representation of this LTS is
shown below.

<figure markdown="1">

<div><a href="{{ site.baseurl }}/img/random-walks-lts.svg" target="_blank" title="Click to open full-size">
<picture>
  <img class="responsive-img full-width-img"
    src="{{ site.baseurl }}/img/random-walks-lts.svg"
    alt="LTS for the Workers specification of two workers">
</picture>
</a></div>

<figcaption>Figure 4: The labelled transition system for two workers.</figcaption>
</figure>

TLA<sup>+</sup> does not have any built-in notion of randomness or
probabilities.  It is what is usually called a *qualitative* specification.
When evaluating `Next` in a state, we can only evaluate whether a specific
transition is possible under a specific choice of `w` and the action scheduling
decision (whether to execute `Add(w)` or `Remove(w)`). This is the standard
semantics under the definition of behaviors. We can enumerate all reachable
states for the above system by breadth-first search or depth-first search. This
is what the model checker TLC does (it uses breadth-first search). This is what
I will call *state enumeration* in this blog post.

We could also interpret the choice of `w` and the action scheduling decision as
a random choice. Since the above specification is small, we can visualize it as
a [Markov decision process
(MDP)](https://en.wikipedia.org/wiki/Markov_decision_process). The states are
the same as in the LTS, but we also attach probabilities to the transitions.

<figure markdown="1">

<div><a href="{{ site.baseurl }}/img/random-walks-mdp.svg" target="_blank" title="Click to open full-size">
<picture>
  <img class="responsive-img full-width-img"
    src="{{ site.baseurl }}/img/random-walks-mdp.svg"
    alt="MDP for the Workers specification of two workers">
</picture>
</a></div>

<figcaption>Figure 5: The MDP for two workers.</figcaption>
</figure>

Notice that we assign probabilities for choosing the value of `w` and for
choosing the action to execute: `Add(w)` or `Remove(w)`. For example, in the
initial state, we choose `w=1` with probability 0.5, then the action `Add(1)`
with probability 0.5, which gives us a transition to the state where `active =
{1}` and `count = 1` (with probability 0.25). However, if we choose `w=1` and
the action `Remove(1)`, we have to backtrack to the initial state, since the
precondition of `Remove(1)` is not satisfied.

A *random walk* is a path through the MDP. It is a sequence of states that we
get by making random choices at each step. In the above figure, you can see one
walk in blue and one walk in red. To avoid too many backward edges, we have a
retry budget, typically, 3-10 retries per step. We take this simple approach in
our custom framework. It is similar to what the randomized simulator in
[Quint][] is doing, though the Quint simulator is trying a bit more locally
before backtracking. Probabilities are basically used to produce various random
walks. There is no inherent statistical meaning to these probabilities in random
walks. This is very much how stateful property-based testing works, too, though
PBT frameworks usually use biased coins, instead of uniform ones.

{% include tip.html content="TLC also supports random simulation, but it assigns
probabilities differently. Given a state, TLC first computes all successors of
the state and then chooses one of the successors uniformly at random. This would
give us a different MDP that filters out disabled transitions. Both approaches
have their merits and drawbacks. The approach of TLC requires us to enumerate
successors, unless we use reservoir sampling. It would actually work better on
the examples in this blog post, since they have many disabled transitions.
However, in systems that inject faults, this approach has an issue, as the
faulty transitions often dominate the search."
%}

## 4. Which states are missing?

Since we can measure state coverage now, the next question is: What are these
states that we are missing? Maybe these states are not important at all. To
check that, I ran the random walks for the two-phase commit benchmark with 2
resource managers for 10,000 instead of 100,000 runs. Conveniently, exactly one
state was missing from the coverage. As my framework is programmatic, I just
asked Claude to instrument the search to experimentally evaluate the visit
frequencies per run for each reachable state. Figure 6 is quite detailed. Click
on it to see the full-size version.

<figure markdown="1">

  <div><a href="{{ site.baseurl }}/img/two_phase_graph.svg" target="_blank" title="Click to open full-size">
    <picture>
      <img class="responsive-img full-width-img"
        src="{{ site.baseurl }}/img/two_phase_graph.svg"
        alt="Experimental evaluation of the visit frequencies for each state in the two-phase commit benchmark with 2 resource managers">
    </picture>
  </a></div>

  <figcaption>
    Figure 6: Reachability frequencies for the two-phase commit benchmark with
    2 resource managers.
  </figcaption>
</figure>

As we can see, the missing state (with the frequency of 0) is the state where
the transasction manager aborts the transaction, one resource manager also
aborts the transaction, and the other resource manager is in the "prepared"
state. This is an interesting state in this protocol, as the other resource
manager still has the potential to commit the transaction, though it should not
do that.

**Bottom line:** We may miss important states with random walks.

## 5. More coverage plots

Figure 7 shows the coverage evolution for the large instances of the benchmarks.
With this, we can see how increasing the number of random walks helps to
increase the coverage.  It also demonstrates the growing volume of covered and
missing states.

I wanted to share these flame plots with you. I find them cool.

<div class="figure-grid">
  <figure>
    <a href="{{ site.baseurl }}/img/random-walks/twophase-n5-overlay.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/random-walks/twophase-n5-overlay.png"
        alt="Overlaid coverage of random walks for the two-phase commit benchmark with 5 resource managers">
    </picture></a>
    <figcaption>Figure 7.a: Overlaid coverage for two-phase commit, 5 RMs.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/random-walks/rw-inst4-overlay.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/random-walks/rw-inst4-overlay.png"
        alt="Overlaid coverage of random walks for the readers-writers benchmark with 4 actors">
    </picture></a>
    <figcaption>Figure 7.b: Overlaid coverage for readers-writers, 4 actors.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/random-walks/fpaxos-inst3-overlay.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/random-walks/fpaxos-inst3-overlay.png"
        alt="Overlaid coverage of random walks for the FPaxos benchmark with 3 acceptors">
    </picture></a>
    <figcaption>Figure 7.c: Overlaid coverage for FPaxos, 3 acceptors.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/random-walks/fpaxos-inst4-overlay.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/random-walks/fpaxos-inst4-overlay.png"
        alt="Overlaid coverage of random walks for the FPaxos benchmark with 4 acceptors">
    </picture></a>
    <figcaption>Figure 7.d: Overlaid coverage for FPaxos, 4 acceptors.</figcaption>
  </figure>
</div>

 
## 6. Conclusions

**Random walks are not sufficient to achieve complete coverage
except for very small state spaces**. Moreover, **random walks take
significantly longer than the model checker**. This is especially striking,
given that we are **running optimized simulators in Rust**. Another issue with
state coverage by random walks is that **you would not even know that you
achieved complete coverage**. You can measure the speed of discovering new
states, but understanding that the simulator has converged basically requires a
model checker.

Interestingly, random walks behaved badly on FPaxos with four acceptors. This is
a relatively benign benchmark, not having a state explosion like specifications
of Byzantine consensus protocols (PBFT). In PBFT, the minimal configurations
contain 4-6 replicas, depending on the protocol. Hence, **we should expect a
significantly worse coverage by random walks on PBFT**.

Why do engineers keep running randomized experiments? Well, it is relatively
easy to write a simulator. (It is not that easy to write one that actually
works!) I have seen people playing with action distributions in the simulator,
just to drive the search towards "interesting" states. Whenever I was asking,
where the distributions were coming from, they could not explain this.
Simulators are deceptive. You have to understand what you are doing, or,
better, incorporate feedback. The most basic feedback is state coverage, though
we can implement more sophisticated feedback mechanisms.

From our experiments it may look like **state enumeration is all we need**. I
would argue that it is true **as long as the set of reachable states fits into
memory**. We do not have to store the states directly in memory, practical model
checkers store hashes of states. We can go as far as to store 2-3 bits per
state, assuming that collisions are acceptable (still better than random
walks!). Having a machine with 128 GB of memory, we can store roughly 50
billions of states. This is significantly more than the number of states in our
benchmarks.

There are cases where randomness may find bugs, where state enumeration gets
stuck:

 1. **Value domains are quite large.** For example, if we choose values from the
 set of all 64-bit integers, it is not feasible to enumerate all successors even
 for a single state. A random walk can still do some progress without getting
 stuck. One can argue that choosing a value from the set $[0, 2^{64})$
 uniformly at random is shooting in the dark, but sometimes it helps us to find
 bugs, especially if the large set has just a few large equivalence classes.
 Arguably, one should be able to apply data abstraction in this case. Also,
 this is usually the moment when you should consider using a model checker that
 supports symbolic representation of states, like [Apalache][].
 
 2. **Guided search.** If we have an heuristic that guides the search towards
 interesting states, we can achieve better coverage with random walks faster.
 Maybe we use reinforcement learning to learn such a heuristic. Maybe we use an
 LLM to predict which actions are more likely to lead to interesting states.
 The main issue is that it is quite hard to find a direction for the search in
 the state space of distributed protocols.

## Want to talk?
 
<!-- References -->

[contact]: https://konnov.phd/posts/service/
[Igor Konnov]: https://konnov.phd
[LI]: https://www.linkedin.com/in/igor-konnov-at/
[tftp-testing]: {% link _posts/2025-12-15-tftp-symbolic-testing.md %}
[pbt-llms]: {% link _posts/2025-12-22-pbt-adversarial-llms.md %}
[Apalache]: https://apalache-mc.org
[TLC]: https://github.com/tlaplus/tlaplus
[QuickCheck]: https://en.wikipedia.org/wiki/QuickCheck
[Quint]: https://github.com/informalsystems/quint
[TLA+ Examples]: https://github.com/tlaplus/Examples/
[TwoPhase.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla
[GrayLamport06]: https://www.microsoft.com/en-us/research/publication/consensus-on-transaction-commit/
[ReadersWriters.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/ReadersWriters/ReadersWriters.tla
[Readers-Writers Problem]: https://en.wikipedia.org/wiki/Readers%E2%80%93writers_problem
[FPaxos.tla]: https://github.com/fpaxos/fpaxos-tlaplus/blob/main/FPaxos.tla
[Flexible Paxos]: https://fpaxos.github.io/
[learntla-parameterize]: https://learntla.com/topics/tips.html#parameterize-your-actions