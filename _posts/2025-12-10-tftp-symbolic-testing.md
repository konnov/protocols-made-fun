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

**Authors:** [Igor Konnov][]

**Date:** December 10, 2025

## 1. Introduction

As promised in the [blog post on small-scope hypothesis][small-scope], I am
continuing with the main body of the talk that I presented at the internal
NVidia FM Week 2025. This work aims at demonstrating how to answer the
following question with [Apalache][]:

<p class="highlight-question"><strong><em>
  How to test the actual implementation against its TLA<sup>+</sup> specification?
</em></strong></p>

Moreover, we want to answer the opposite question as well:

<p class="highlight-question"><strong><em>
  How to test the TLA<sup>+</sup> specification against the actual implementation?
</em></strong></p>

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/mbt.svg" alt="Model-based testing">
</picture>

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/tv.svg" alt="Trace validation">
</picture>

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/tv.svg" alt="Symbolic testing">
</picture>

## 2. The new JSON-RPC API of Apalache

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/apalache-api.svg" alt="Apalache JSON-RPC API">
</picture>


## 10. Prior Work

In this section, I've collected the previous work on model-based testing and
runtime monitoring with TLA<sup>+</sup>:

 - Nagendra et. al. Model guided fuzzing of distributed systems (2025).
   Check [the talk](https://www.youtube.com/watch?v=DO8MvouV29M).

 - Cirstea, Kuppe, Merz, Loillier. Validating Traces of Distributed Systems
   Against TLA+ Specifications (2024). Check the
   [arxiv paper](https://arxiv.org/abs/2404.16075).

 - Chamayou et. al. Validating System Executions with the TLA+ Tools (2024).
   See [the talk](https://www.youtube.com/watch?v=NZmON-XmrkI).

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
