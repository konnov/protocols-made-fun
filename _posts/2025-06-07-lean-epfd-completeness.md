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
in Lean. I believe that the next protocol would require less time.

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
simplifies the events, as we do not have to reason about the interactions
between different protocol layers in the proof. Every process $p \in
\mathit{Proc}$ works as follows:

<pre>
<code class="nohighlight">
<strong>upon</strong> Init <strong>do</strong>
  alive := Proc
  suspected := ∅
  delay := InitDelay
  set_timeout(delay)

<strong>upon</strong> Timeout <strong>do</strong>
  <strong>if</strong> alive ∩ suspected ≠ ∅ <strong>then</strong>
    delay := delay + InitDelay
  suspected := Proc \ alive
  <strong>send</strong> HeartbeatRequest <strong>to</strong> all p ∈ Proc
  alive := ∅;
  set_timeout(delay);

<strong>upon receive</strong> HeartbeatRequest <strong>from</strong> q <strong>do</strong>
  <strong>send</strong> HeartbeatReply <strong>to</strong> q

<strong>upon receive</strong> HeartbeatReply <strong>from</strong> p <strong>do</strong>
  alive := alive ∪ {p};
</code>
</pre>

Intuitively, the operation of a failure detector is very simple.  Initially, a
process $p$ considers all the processes alive and suspects no other process of
being crashed. Initially, it sets a timer to $\mathit{InitDelay}$ time units.
Basically, nothing interesting happens in the time interval $[0,
\mathit{InitDelay})$, except that some processes may crash.

Once a timeout is triggered on a process $p$, it updates the set of the
suspected processes to the set of processes that have not sent a heartbeat to it
in the previous time interval (not alive), resets the set of the alive processes
and sends heartbeat requests to every process, including itself. Additionally,
if $p$ finds out that it prematurely suspected an alive process, it increases
its timeout window by $\mathit{InitDelay}$. Importantly, $p$ also sets a new
timeout for $delay$ time units.

Finally, whenever a process receives a heartbeat request, it sends a reply.
Whenever, a process receives a heartbeat reply from a process $q$, it adds $q$
to the set of alive processes.

The algorithm looks deceivingly simple. However, the pseudo-code is missing
another piece of information, namely, how the distributed system behaves as a
whole. What does it mean for processes to crash? When messages are received, if
at all? It's not even clear how to properly capture this in pseudo-code.
Normally, academic papers leave this part to math definitions. Since we want to
write proofs of correctness, we cannot avoid reasoning about the whole system.
Instead of appealing to intuition, we will capture both the process behavior and
the system behavior in Lean.

## 2. Eventually perfect failure detector in Lean

In contrast to [two-phase commit][lean-two-phase], where we started with a
functional specification, I decided to start with the propositional
specification immediately. A functional specification would be closer to the
implementation details. Perhaps, we will write one in another blog post.

### 2.1. Basic type definitions

Before specifying the behavior of the processes, we have to figure out the basic
types. You can find them in [Basic.lean][]. First, we declare the type `Proc`
that we use for process identities:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/2496533b5cc27fe915f93346c5c9eaadfc613c27/epfd/Epfd/Basic.lean
  lean 17-17
 %}

If you compare it with the type `RM` in [two-phase commit][lean-two-phase], this
time, we require `Proc` to be of `Fintype`. By doing so, we avoid carrying
around the set of all processes. With `Fintype`, we can simply use
`Fintype.univ` for the set of all processes!

Next, we define the types of message tags and messages:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/2496533b5cc27fe915f93346c5c9eaadfc613c27/epfd/Epfd/Basic.lean
  lean 19-35
 %}

Now, most of it should be obvious, except, perhaps, for the field `timestamp`.
What is it? If we look at the original paper on failure detectors by [Chandra
and Toueg][ChandraToueg96], we'll see that they assume the existence of a global
clock. The processes can’t read this clock, but the system definitions refer to
it. Hence, a message's timestamp refers to the value of the global clock at the
moment the message is sent.

Finally, we define a protocol state with the following structure:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/2496533b5cc27fe915f93346c5c9eaadfc613c27/epfd/Epfd/Basic.lean
  lean 51-59
 %}

The first group of fields should be clear. They map process identities to the
corresponding values of the variables in the pseudo-code:

 - `alive[p]!` stores the set of alive processes as observed by a process `p`,
 - `suspected[p]!` stores the set of suspected processes as observed by a process `p`,
 - `delay[p]!` stores the current value of delay by a process `p`,
 - `nextTimeout[p]!` stores the timestamp of the next timeout by a process `p`.
   The timestamp refers to the global clock.

The second group of fields is less obvious. They do not represent the process
states, but rather the rest of the global state of the distributed system:

 - `sent` is the set of all messages sent by the processes,
 - `rcvd` is the set of all messages received by the processes,
 - `clock` is the value of the fictitious global clock,
 - `crashed` is the set of all processes that have crashed.

While the second group of fields is needed to formally capture a state of the
distributed system, we notice that the processes cannot have access to those
fields. Otherwise, detecting failures would be trivial, we would just access the
field `crashed`.

### 2.2. Partial synchrony

TBD


<a name="end"></a>

[^1]: Christian Cachin, Rachid Guerraoui, and Luís Rodrigues. Introduction to Reliable and Secure Distributed Programming. Second Edition, Springer, 2011, XIX, 320 pages
[Igor Konnov]: https://konnov.phd
[Lean]: https://github.com/leanprover/lean4
[Apalache]: https://apalache-mc.org/
[lean-two-phase]: {% link _posts/2025-04-25-lean-two-phase.md %}
[lean-two-phase-proofs]: {% link _posts/2025-05-10-lean-two-phase-proofs.md %}
[Basic.lean]: https://github.com/konnov/leanda/blob/main/epfd/Epfd/Basic.lean
[Propositional.lean]: https://github.com/konnov/leanda/blob/main/epfd/Epfd/Propositional.lean
[PropositionalProofs.lean]: https://github.com/konnov/leanda/blob/main/epfd/Epfd/PropositionalProofs.lean
[lean-tp]: https://lean-lang.org/theorem_proving_in_lean4/title_page.html
[x-liveness]: https://x.com/n5xdg1/status/1916289300121240017
[fd-wikipedia]: https://en.wikipedia.org/wiki/Failure_detector
[DP2011]: https://www.distributedprogramming.net/
[LINFO2345-5]: https://www.youtube.com/watch?v=k_mlWOcWOSA
[ChandraToueg96]: https://dl.acm.org/doi/abs/10.1145/226643.226647
[happy to help]: {{ 'contact/' | relative_url }}
[leave-comment]: #end