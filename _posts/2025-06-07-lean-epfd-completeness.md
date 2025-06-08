---
layout: post
title: "Proving completeness of an eventually perfect failure detector in Lean4"
date: 2025-06-07
categories: lean
tlaplus: true
quint: true
math: true
lean: true
shell: true
---

**Author:** [Igor Konnov][]

**Tags:** specification lean distributed proofs tlaplus

In the previous [blog post][lean-two-phase-proofs], we looked at proving
consistency of Two-phase commit in [Lean 4][Lean]. This proof followed the
well-trodden path: We found an inductive invariant, quickly model-checked it
with [Apalache][] and proved its inductiveness in Lean. One of the immediate
questions that I got on X/Twitter [was](x-liveness): What about liveness?

Well, liveness of the two-phase commit after the TLA<sup>+</sup> specification
does not seem to be particularly interesting, as it mostly depends on fairness
of the resource managers and the transaction manager. (A real implementation may
be much trickier though.) I was looking for something a bit more challenging
but, at the same time, something that would not take months to reason about.
Since many Byzantine-fault tolerance algorithms work under partial synchrony, it
looked natural to find a protocol that required partial synchrony. [Failure
detectors][fd-wikipedia] seemed to be a good fit. These algorithms are
relatively small, but require plenty of reasoning about time.

Hence, I opened the [book][DP2011] on Reliable and Secure Distributed
Programming by Christian Cachin, Rachid Guerraoui, and Luís Rodrigues and found
the pseudo-code of the eventually-perfect failure detector (EPFD). If you have
never heard of failure detectors, there are a few introductory lectures on
YouTube, e.g., [this one][LINFO2345-5]. Writing a decent TLA<sup>+</sup>-like
specification of EPFD and its temporal properties in Lean took me about eight
hours. Since temporal properties require us to reason about infinite executions,
this required a bit of experimentation with Lean.  Figuring out how to capture
partial synchrony and fairness was the most interesting part of the exercise. I
believe that this approach can be reused in many other protocol specifications.
You can find the protocol specification and the properties in
[Propositional.lean][].

To prove correctness of EPFD, we have to show that it satisfies strong
completeness and strong accuracy. See Section TBD. I chose to start with strong
completeness. The proof in the book is just four (!) lines long. In contrast to
that, my proof of strong completeness in Lean is about 1 KLOC. It consists of 13
lemmas and 2 theorems. As one professor once asked me: *Do you want to convince
a machine that distributed algorithms are correct?* Apparently, it takes more
effort to convince a machine than to convince a human. By a machine, I mean a
proof assistant such as Lean, not an LLM, which would be easy to convince in
pretty much anything. The real reason for that is that we take a lot of things
about computations for granted, whereas Lean requires them to be explained. For
instance, if a process $q$ crashes when the global clock value is $t$, it seems
obvious that no process $p$ can receive a message from $q$ with the timestamp
above $t$. Not so fast, this has to be proven! For the impatient, the complete
proofs can be found in [PropositionalProofs.lean][].

It took me about 35 hours to finish the proof of strong completeness.  I
remember to have a working proof for a *pair* of processes $p$ and $q$ after the
25 hour mark already. However, the property in the book is formulated over all
processes, not just a pair. Proving the property over all processes took me
about additional 10 hours. This actually required more advanced Lean proof
mechanics and solving a few curious proof challenges with crashing processes.
Also, bear in mind that this was literally my first proof of temporal properties
in Lean. I believe that the next protocol should take me less time.

Surprisingly, even though strong completeness is usually thought of as a safety
counterpart of strong accuracy, the proof required quite a bit of reasoning
about temporal properties, not just state invariants. It also helped me a lot to
structure the proofs in terms of temporal formulas, rather than in terms of
arbitrary properties of computations. Of course, it would be interesting to see
how this proof compares to a proof in TLAPS, which is specifically designed to
reason about temporal properties.

## Table of contents

TBD

## 1. Eventually perfect failure detector in pseudo-code

To avoid any potential copyright issues, I am not giving the pseudo-code from
the book. If you want to see the original version, go check [the
book][DP2011][^1], Algorithm 2.7, p. 55. Below is an adapted version, which
simplifies the events, as they are not needed in our proof:

<pre>
<code class="nohighlight">
<strong>upon</strong> Init <strong>do</strong>
  alive := AllProcesses
  suspected := ∅
  delay := InitDelay
  starttimer(delay)

<strong>upon</strong> Timeout <strong>do</strong>
  <strong>if</strong> alive ∩ suspected ≠ ∅ <strong>then</strong>
    delay := delay + InitDelay
  suspected := AllProcesses \ alive
  <strong>send</strong> HeartbeatRequest to all p
  alive := ∅;
  starttimer(delay);

<strong>upon</strong> receive HeartbeatRequest from q <strong>do</strong>
  <strong>send</strong> HeartbeatReply to q

<strong>upon</strong> receive HeartbeatReply from p <strong>do</strong>
  alive := alive ∪ {p};
</code>
</pre>



<a name="end"></a>

[^1]: Christian Cachin, Rachid Guerraoui, and Luís Rodrigues. Reliable and Secure Distributed Programming. Second Edition, Springer, 2011, XIX, 320 pages
[Igor Konnov]: https://konnov.phd
[Lean]: https://github.com/leanprover/lean4
[happy to help]: {{ 'contact/' | relative_url }}
[ben-or-mc]: {% link _posts/2024-11-03-ben-or.md %}
[lean-two-phase]: {% link _posts/2025-04-25-lean-two-phase.md %}
[lean-two-phase-proofs]: {% link _posts/2025-05-10-lean-two-phase-proofs.md %}
[Propositional.lean]: https://github.com/konnov/leanda/blob/main/epfd/Epfd/Propositional.lean
[PropositionalProofs.lean]: https://github.com/konnov/leanda/blob/main/epfd/Epfd/PropositionalProofs.lean
[lean-tp]: https://lean-lang.org/theorem_proving_in_lean4/title_page.html
[leave-comment]: #end
[Apalache]: https://apalache-mc.org/
[x-liveness]: https://x.com/n5xdg1/status/1916289300121240017
[fd-wikipedia]: https://en.wikipedia.org/wiki/Failure_detector
[DP2011]: https://www.distributedprogramming.net/
[LINFO2345-5]: https://www.youtube.com/watch?v=k_mlWOcWOSA