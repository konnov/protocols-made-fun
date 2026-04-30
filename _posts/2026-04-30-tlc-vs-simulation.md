---
layout: post
title: "TLC breadth-first search vs random simulation"
date: 2026-04-30
author: Igor Konnov
categories: model-checking simulation
tlaplus: true
math: true
shell: false
python: false
hidden: false
feed: true
---

**Author:** [Igor Konnov][]

**Date:** April 30, 2026

Recently, I wrote a blog post on [random walks][] that compared the state
coverage of random walks for increasingly larger sets of experiments: 100
thousands, 1 million, 10 million, and even 100 million episodes. There, I used
custom-built simulators in Rust to randomly walk through the state spaces of
several TLA<sup>+</sup> benchmarks: two-phase commit, readers-writers, and
FPaxos.

A. Jesse Jiryu Davis noticed my blog post and [wrote a
message][tlaplus-group-message] on the TLA<sup>+</sup> Google group. Since the
random walks in the blog post are not exactly the same as the random simulation
in TLC, we both wondered how the TLC simulation mode compares to the model
checker in terms of coverage and running times. Markus Kuppe shared the options
to collect distinct state coverage in the TLC simulation mode, see the
[discussion][tlaplus-group-message].

The **important distinction** between the [random walks][] and the TLC
simulator is that **a random walk chooses one successor state at each step**,
whereas **TLC enumerates all successor states and then chooses one of them
uniformly at random.** Markus explains the rationale behind this design choice
in TLC:

> ...enumerating all successors is useful for more than just choosing
> the next step: TLC can also check invariants on all generated successor states,
> not only on the one that ends up being sampled. That is a meaningful benefit
> when the goal is to catch bugs, not just drive a walk.

This new blog post explores this direction. To get more details about the
bennchmarks, read the original blog post on [random walks][].

Look at two groups of figures below. They summarize the results of running
random walks on specifications of three prominent distributed protocols:
two-phase commit, readers-writers, and FPaxos (see [Benchmarks](#benchmarks)).
The figures show the coverage achieved by the TLC simulation mode, with 100%
being the numbers of distinct states (reported by TLC). All running times are
given for an AMD Ryzen 9 5950X processor (16 physical, 32 logical cores), 128 GB
memory.

Importantly, the TLC simulations are run on **a single worker**, they are not
running in parallel. We do that, in order to compute the state coverage
precisely. When you look at running times, keep in mind that TLC can run
multiple simulation workers in parallel.

{% include tip.html content="In contrast to the previous blog posts, I do not
provide the artifacts for download. AI slop forks are real. It still takes me
several days to design and conduct the experiments on a beefy machine, as well
as to find the right format to interpret and plot the data. It only takes 10-15
minutes to repackage the benchmarks and results with an AI tool, having the
experimental data. Hence, I am sharing my lab book with the customers and
researchers, upon request."
%}

## 1. Coverage for minimal instances

In this set of experiments, we run **TLC simulations** for the minimal instances
of the benchmarks. We start with the **meaningful default** of 100,000
simulation runs, with at most 100 steps per run. (Mind that the successor set is
computed at each step.) As you can see from Figure 1, the coverage is close to
100%, but it's not complete. Interestingly, 10 million runs give us 99.9%
coverage.

<div class="figure-grid">
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/twophase-n2-coverage.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/twophase-n2-coverage.png"
        alt="Coverage of random walks for the two-phase commit benchmark with 2 resource managers">
    </picture></a>
    <figcaption>Figure 1.a: Two-phase commit, 2 RMs.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/twophase-n3-coverage.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/twophase-n3-coverage.png"
        alt="Coverage of random walks for the two-phase commit benchmark with 3 resource managers">
    </picture></a>
    <figcaption>Figure 1.b: Two-phase commit, 3 RMs.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/rw-inst3-coverage.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/rw-inst3-coverage.png"
        alt="Coverage of random walks for the readers-writers benchmark with 3 actors">
    </picture></a>
    <figcaption>Figure 1.c: Readers-writers, 3 actors.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/fpaxos-inst2-coverage.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/fpaxos-inst2-coverage.png"
        alt="Coverage of random walks for the FPaxos benchmark with 2 acceptors">
    </picture></a>
    <figcaption>Figure 1.d: FPaxos, 2 acceptors.</figcaption>
  </figure>
</div>

## 2. Running times for tiny instances

**All of the above benchmarks are quite small by the model checking
standards. They have tens of thousands of states. It takes TLC only 1-3 seconds
to explore the state space and check the invariants for each of these
benchmarks.**

Figure 2 shows the running times for the above simulation benchmarks. The dashed
lines show the running times for the TLC model checker to explore the complete
state space.  Additionally, the right-hand y-axis shows the slowdown factor of
the simulations compared to the model checker. For example, for the two-phase
commit benchmark with 3 resource managers, the model checker takes about 2
seconds, while 10 million simulations take about 2 hours, which is a slowdown
factor of about 10,000. As you can see, 10 million simulations take hours, where
the model checker needs several seconds.

<div class="figure-grid">
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/twophase-n2-runtime.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/twophase-n2-runtime.png"
        alt="Running times for the two-phase commit benchmark with 2 resource managers">
    </picture></a>
    <figcaption>Figure 2.a: Two-phase commit, 2 RMs.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/twophase-n3-runtime.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/twophase-n3-runtime.png"
        alt="Running times for the two-phase commit benchmark with 3 resource managers">
    </picture></a>
    <figcaption>Figure 2.b: Two-phase commit, 3 RMs.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/rw-inst3-runtime.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/rw-inst3-runtime.png"
        alt="Running times for the readers-writers benchmark with 3 actors">
    </picture></a>
    <figcaption>Figure 2.c: Readers-writers, 3 actors.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/fpaxos-inst2-runtime.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/fpaxos-inst2-runtime.png"
        alt="Running times for the FPaxos benchmark with 2 acceptors">
    </picture></a>
    <figcaption>Figure 2.d: FPaxos, 2 acceptors.</figcaption>
  </figure>
</div>

## 3. Slightly larger instances

What happens if we take the instances that are still small, but have 1-2
participants more? Figure 3 shows the results of running TLC simulations on
these instances.

As you can see, with the meaningful default of 100,000 random walks, we achieve
poor coverage on readers-writers and FPaxos, though the coverage on two-phase
commit is nearly 99%. So this new TLC simulation has much better coverage than
[random walks][], but it has comparable coverage on the readers-writers and
FPaxos benchmarks! You can also switch between this blog post and [random
walks][] to see the difference in coverage between the two approaches.

To stress the message of the previous blog post, these instances are **not that
large by the model checking standards**.

<div class="figure-grid">
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/twophase-n5-coverage.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/twophase-n5-coverage.png"
        alt="Coverage of random walks for the two-phase commit benchmark with 5 resource managers">
    </picture></a>
    <figcaption>Figure 3.a: Two-phase commit, 5 RMs.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/rw-inst4-coverage.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/rw-inst4-coverage.png"
        alt="Coverage of random walks for the readers-writers benchmark with 4 actors">
    </picture></a>
    <figcaption>Figure 3.b: Readers-writers, 4 actors.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/fpaxos-inst3-coverage.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/fpaxos-inst3-coverage.png"
        alt="Coverage of random walks for the FPaxos benchmark with 3 acceptors">
    </picture></a>
    <figcaption>Figure 3.c: FPaxos, 3 acceptors.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/fpaxos-inst4-coverage.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/fpaxos-inst4-coverage.png"
        alt="Coverage of random walks for the FPaxos benchmark with 4 acceptors">
    </picture></a>
    <figcaption>Figure 3.d: FPaxos, 4 acceptors.</figcaption>
  </figure>
</div>

## 4. Running times for larger instances

Again, **it takes the model checker TLC up to 10 minutes to enumerate all the
states and check the invariants for these instances**, whereas we have been
**running the simulations for hours!**.

<div class="figure-grid">
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/twophase-n5-runtime.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/twophase-n5-runtime.png"
        alt="Running times for the two-phase commit benchmark with 5 resource managers">
    </picture></a>
    <figcaption>Figure 4.a: Two-phase commit, 5 RMs.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/rw-inst4-runtime.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/rw-inst4-runtime.png"
        alt="Running times for the readers-writers benchmark with 4 actors">
    </picture></a>
    <figcaption>Figure 4.b: Readers-writers, 4 actors.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/fpaxos-inst3-runtime.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/fpaxos-inst3-runtime.png"
        alt="Running times for the FPaxos benchmark with 3 acceptors">
    </picture></a>
    <figcaption>Figure 4.c: FPaxos, 3 acceptors.</figcaption>
  </figure>
  <figure>
    <a href="{{ site.baseurl }}/img/tlc-vs-simulation/fpaxos-inst4-runtime.png"
       target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/tlc-vs-simulation/fpaxos-inst4-runtime.png"
        alt="Running times for the FPaxos benchmark with 4 acceptors">
    </picture></a>
    <figcaption>Figure 4.d: FPaxos, 4 acceptors.</figcaption>
  </figure>
</div>

## 5. Conclusions

I am not going to repeat the [conclusions from the previous blog
post][random-walks-conclusions]. They are still valid. The new TLC simulation
mode achieves better coverage than the random walks on two-phase commit, but it
has comparable coverage on readers-writers and FPaxos. The running times of the
TLC simulator are worse than the model checker and the random walks.

## Want to talk?
 
<!-- References -->

[contact]: https://konnov.phd?pmf=20250309
[Igor Konnov]: https://konnov.phd
[LI]: https://www.linkedin.com/in/igor-konnov-at/
[random walks]: {% link _posts/2025-03-09-random-walks.md %}
[random-walks-conclusions]: {% link _posts/2025-03-09-random-walks.md %}#6-conclusions
[TLC]: https://github.com/tlaplus/tlaplus
[TLA+ Examples]: https://github.com/tlaplus/Examples/
[tlaplus-group-message]: https://groups.google.com/g/tlaplus/c/iFUAhlsIuQQ/m/t044etF6AwAJ