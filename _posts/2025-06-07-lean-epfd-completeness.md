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
Since many Byzantine-fault tolerance algorithms work under partial synchrony, a
natural thing to do was to find a protocol that required partial synchrony.
[Failure detectors][fd-wikipedia] seemed to be a good fit to me. These
algorithms are relatively small, but require plenty of reasoning about time.

Hence, I opened the book [DP2011] on Reliable and Secure Distributed Programming
by Christian Cachin, Rachid Guerraoui, and Luís Rodrigues and found the
pseudo-code of the eventually-perfect failure detector (EPFD). If you have never
heard of failure detectors, there are a few introductory lectures on YouTube,
e.g., [this one][LINFO2345-5]. Writing a decent TLA<sup>+</sup>-like
specification of EPFD and its temporal properties in Lean took me about eight
hours. Since temporal properties require us to reason about infinite executions,
this required a bit of experimentation with Lean.  Figuring out how to capture
[partial synchrony][spec-partial-synchrony] and [fairness][spec-fairness] was
the most interesting part of the exercise. I believe that this approach can be
reused in many other protocol specifications.  You can find the protocol
specification and the properties in [Propositional.lean][]. See [Section
2][spec-epfd] for detailed explanations.

To prove correctness of EPFD, we have to show that it satisfies strong
completeness and strong accuracy (see [temporal properties][]). I chose
to start with strong completeness. The proof in the book is just four (!) lines
long. In contrast to that, my proof of strong completeness in Lean is about 1
KLOC. It consists of 13 lemmas and 2 theorems. As one professor once asked me:
*Do you want to convince a machine that distributed algorithms are correct?*
Apparently, it takes more effort to convince a machine than to convince a human.
By a machine, I mean a proof assistant such as Lean, not an LLM, which would be
easy to convince in pretty much anything. The real reason for that is that we
take a lot of things about computations for granted, whereas Lean requires them
to be explained. For instance, if a process $q$ crashes when the global clock
value is $t$, it seems obvious that no process $p$ can receive a message from
$q$ with the timestamp above $t$. Not so fast, this has to be proven! For the
impatient, the complete proofs can be found in [PropositionalProofs.lean][].
See [Section 3][proving-completeness] for detailed explanations.

It took me about 35 hours to finish the proof of strong completeness. I remember
to have a working proof for a *pair* of processes $p$ and $q$ after the 25 hour
mark already. However, the property in the book is formulated over all
processes, not just a pair. Proving the property over all processes took me
about additional 10 hours. This actually required more advanced Lean proof
mechanics and solving a few curious proof challenges with crashing processes,
e.g., [how we define them][crashed processes]. Also, bear in mind that this was
literally my first proof of temporal properties in Lean. I believe that the next
protocol would require less time.

Below is the nice diagram that illustrates the dependencies between the theorems
(green) and lemmas (yellow) that I had to prove, culminating in the theorem
`strong_completeness_on_states`. Notice `forall_FG_implies_FG_forall` is not a
lemma. Actually, it is a general theorem about swapping universal quantifiers
and eventually-always, which could be reused in other proofs. Once I realized
that I had to apply this lemma twice in the proof of
`eventually_always_suspected_meet`, I finished the proof quickly. This is one
more instance of that temporal logic helps us with high-level reasoning.

{% include webp.html
    src="epfd-completeness-deps.png"
    alt="Proof schema" %}

Surprisingly, even though strong completeness is usually thought of as a safety
counterpart of strong accuracy, the proof required quite a bit of reasoning
about temporal properties, not just state invariants. It also helped me a lot to
structure the proofs in terms of temporal formulas, rather than in terms of
arbitrary properties of computations. Of course, it would be interesting to see
how this proof compares to a proof in TLAPS, which is specifically designed to
reason about temporal properties.

If you look at how the lemma statements are written in [Section
3][proving-completeness], you will see that they are all
*temporal formulas*, just written directly using quantifiers $\forall$ and
$\exists$ instead of modal operators like $\square$ and $\Diamond$. To emphasize
this similarity, I wrote alternative statements in TLA<sup>+</sup>. If you know
temporal logic or TLA<sup>+</sup>, just have a look at all these statements:

$$
\begin{align}
   \square (\forall m \in sent: m.ts \le clock) & \\
 \square (p \notin crashed)
   \Rightarrow& \square \Diamond (alive[p] = \emptyset) \\
 \square (p \notin crashed) \land \Diamond (q \in crashed)
   \Rightarrow& \Diamond \square (q \notin alive[p]) \\
 \square (p \notin crashed) \land \Diamond (q \in crashed)
   \Rightarrow& \Diamond \square (q \in suspected[p]) \\
 \square (\forall c \in \mathbb{N}: (q \in crashed \land clock = c)
   \Rightarrow& \square (\forall m \in sent: (m.src = q) \Rightarrow m.ts \le c))
\end{align}
$$

Although a time investment of about a week to prove strong completeness of EPFD
may seem like a lot, this approach has certain benefits in comparison to using
tools like the explicit-state model checker [TLC][] or the symbolic model
checker [Apalache][]:

 1. Re-checking the proofs takes seconds. It's also trivial to integrate
 proof-checking in the GitHub continuous integration.
 
 1. All tools require a spec to be massaged a bit. I always felt bad about not
 being able to formally show that these transformations are sound with a model
 checker. With Lean, it is usually easy.
 
 1. If you manage to decompose your proof goals into smaller lemmas, there is a
 sense of progress. Even though I had to prove 4-5 unexpected lemmas in this
 experiment, I could definitely say whether I was making progress or not. In the
 end, I only proved one lemma that happened to be redundant. With model
 checkers, both explicit and symbolic, it is often frustrating to wait for hours
 or days without clear progress.

Obviously, the downside of using an interactive theorem prover is that someone
has to write the proofs. For a customer, it may make a difference whether they
pay for 2–4 weeks of contract work, or for 1 week of contract work and then wait
3 weeks for a model checker. However, if time is critical, it makes sense to
invest in both approaches.

## Table of contents

TBD

## 1. Eventually perfect failure detector in pseudo-code

To avoid any potential copyright issues, I am not copying the pseudo-code from
the book. If you want to see the original version, go check [DP2011][][^1],
Algorithm 2.7, p. 55. Below is an adapted version, which simplifies the events,
as we do not have to reason about the interactions between different protocol
layers in the proof. Every process $p \in \mathit{Procs}$ works as follows:

<pre>
<code class="nohighlight">
<strong>upon</strong> Init <strong>do</strong>
  alive := Procs
  suspected := ∅
  delay := InitDelay
  set_timeout(delay)

<strong>upon</strong> Timeout <strong>do</strong>
  <strong>if</strong> alive ∩ suspected ≠ ∅ <strong>then</strong>
    delay := delay + InitDelay
  suspected := Procs \ alive
  <strong>send</strong> HeartbeatRequest <strong>to</strong> all p ∈ Procs
  alive := ∅
  set_timeout(delay)

<strong>upon receive</strong> HeartbeatRequest <strong>from</strong> q <strong>do</strong>
  <strong>send</strong> HeartbeatReply <strong>to</strong> q

<strong>upon receive</strong> HeartbeatReply <strong>from</strong> p <strong>do</strong>
  alive := alive ∪ {p}
</code>
</pre>

Intuitively, the operation of a failure detector is very simple.  Initially, a
process $p$ considers all the processes alive and suspects no other process of
being crashed. Also, it sets a timer to $\mathit{InitDelay}$ time units.
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
at all? It's not even clear how to properly write this in pseudo-code.
Normally, academic papers leave this part to math definitions. Since we want to
prove correctness, we cannot avoid reasoning about the whole system. Instead of
appealing to intuition, we capture both the process behavior and the system
behavior in Lean.

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
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Basic.lean
  lean 17-17
 %}

If you compare it with the type `RM` in [two-phase commit][lean-two-phase], this
time, we require `Proc` to be of `Fintype`. By doing so, we avoid carrying
around the set of all processes. With `Fintype`, we can simply use
`Fintype.univ` for the set of all processes!

Next, we define the types of message tags and messages:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Basic.lean
  lean 19-35
 %}

Now, most of it should be obvious, except, perhaps, for the field `timestamp`.
What is it? If we look at the original paper on failure detectors by [Chandra
and Toueg][ChandraToueg96] (CT96), we'll see that they assume the existence of a global
clock. The processes can’t read this clock, but the system definitions refer to
it. Hence, a message's timestamp refers to the value of the global clock at the
moment the message is sent.

Finally, we define a protocol state with the following structure:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Basic.lean
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

If you find this representation of the global state surprising, it's actually
quite common to reason about such a global snapshot of a distributed system in
TLA<sup>+</sup>. Here, we're simply following the TLA<sup>+</sup> methodology,
albeit reproduced in Lean.

### 2.2. Partial synchrony

The algorithm is designed to work under partial synchrony. Unfortunately,
[DP2011][] does not give us a precise definition of what this means. So we go
back to the paper by [Dwork, Lynch, and Stockmeyer][DLS88] (DLS88) who
introduced partial synchrony. There are several kinds of partial synchrony in
the paper. We choose the one that is probably the most commonly used nowadays:
There is a period of time called global stabilization time (GST), after which
every correct process $p$ receives a message from a correct process $q$ no later
than $\mathit{MsgDelay}$ time units after it was sent by $q$. Both
$\mathit{GST}$ and $\mathit{MsgDelay}$ are unknown to the processes, and may
change from run to run. It is also important to fix the guarantees about the
messages that were sent before $\mathit{GST}$. We assume that they are received
by $\mathit{GST} + \mathit{MsgDelay}$ the latest.

Now we can write a formal definition of what it means for a message to be
received on time under partial synchrony:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Basic.lean
  lean 61-65
 %}

Both [DLS88][] and [DP2011][] mention that in practice partial synchrony means
that the periods of asynchrony and synchrony alternate. [DLS88][] mention that
for their consensus algorithms one should be able to compute the time of
convergence after GST. I am not actually sure how it would work in case of
failure detectors, as it is impossible to predict how long it takes a process to
crash. Hence, in our model, there is no alternation of asynchrony and synchrony.
After GST, communication becomes synchronous, in the sense that every message is
delivered not later than $\mathit{MsgDelay}$ time units after it was sent.

### 2.3. Specifying the actions

Now we are ready to specify the actions of a distributed system that follows the
algorithm. You can find all definitions in [Propositional.lean][].

We start with the protocol parameters and the variables `s` and `s'` that
we use throughout the definitions:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 20-36
 %}

Below is the definition of receiving a heartbeat request:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 38-55
 %}

As you can see, the definition of `rcv_heartbeat_request` captures the behavior
of the whole system, when `dst` handles a heartbeat request. In particular,
`dst` cannot be in the crashed state when it is receiving the message, the
message has to be timely, etc. Similar to TLA<sup>+</sup>, we specify that
certain fields preserve their values. Actually, we could update the structure
`s'` instead of writing down multiple equalities over the fields. However, it
would make the proofs more cumbersome. I could not find a simple way to express
something like TLA<sup>+</sup>'s `UNCHANGED` over multiple variables.

Interestingly, I accidentally swapped `src` and `dst` in the initial version of
`reply` in `rcv_heartbeat_request`. I only found that when trying to prove one
of the lemmas towards strong completeness.

Similar to `rcv_heartbeat_request`, we specify `rcv_heartbeat_reply`:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 57-73
 %}

The definition of `timeout` is the longest one, as a lot of things happen on
timeout:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 75-105
 %}

As you can see, the sequential logic from the pseudo-code is compressed into
multiple equalities, very much in the spirit of TLA<sup>+</sup>. Our proofs are
complex enough, so it's good that we do not have to deal with sequential
execution inside actions. If this is not convincing enough, we could write
sequential code and prove that it refines the corresponding propositional
definition.

We have defined the three actions, as in the pseudo-code (the definition of
`init` comes later). Are we done? Not quite. Since we're specifying the behavior
of the entire distributed system, not just individual processes, we need two
more actions.

The first additional action is `crash`:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 107-120
 %}

Yes, we have to specify what it means for a process to crash, as there is no
built-in semantics of crashing in Lean.

What is left? Remember that we had the fictitious global clock? We have to
advance it from time to time:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 122-134
 %}

I have cut a corner in the definition of `advance_clock` by incrementing it,
instead of advancing it by a positive delta. This works since we declared the
clock to be a natural number rather than a rational or real. Incrementing the
clock instead of advancing it by delta simplifies the proofs a bit.

Finally, we define the initialization and the transition relation as follows:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 136-165
 %}

Notice the `noncomputable` qualifier in front of `init_map`. Lean requires it,
as we are converting `Finset.univ` to a list. If we want to write an executable
specification, we have to work around this, perhaps, by passing the list of all
process identities to the initializer.

So far, our definitions looked very much like a typical specification in
TLA<sup>+</sup>, even though we had to use Lean's data structures such as finite
sets and hash maps, instead of TLA<sup>+</sup>'s sets and functions. I believe
that there is an advantage in keeping this resemblance. First, if we choose to
translate this specification to TLA<sup>+</sup>, e.g., to use the model
checkers, it is not hard. (Actually, I did that; it was almost no-brainer with
Copilot). Second, we can reuse the standard specification idioms from
TLA<sup>+</sup>.

### 2.4. Specifying the temporal properties

In [two-phase commit][lean-two-phase-proofs], we were only concerned with state
invariants and, thus, only had to reason about lists of actions. In the case of
failure detectors, we have to reason about temporal properties. In general,
temporal properties require us to reason about infinite behaviors. Surprisingly,
it is quite easy to specify properties of infinite behaviors in Lean. We just
use a function `seq` of natural numbers to `ProtocolState`.

Here is how we specify strong completeness of the failure detector:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 182-189
 %}

The above definition may seem to be a bit loaded. The left part of `→` requires
that the set `Crashed` indeed contains all the processes that crashed in the
run. The set `Crashed` happened to be hard to define. More on that later.  The
right part of `→` says that there is a point `k` in `seq`, so that starting with
$k$, every further state $seq (i + k)$ satisfies $q \notin (seq (i +
k)).suspected[p]!$ for a correct $p$ and a crashed $q$.

If you know temporal logic, e.g., as defined in TLA<sup>+</sup>, the right-hand
side of `→` could be written like (`<>` is usually called "eventually" and `[]`
is called "always"):

```tla
<>[](∀ p q: Proc, p ∉ C ∧ q ∈ C → q ∈ suspected[p])
```

Similar to `is_strongly_complete`, this is how we specify strong accuracy:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 200-207
 %}

Again, in temporal logic it would look like:

```tla
<>[](∀ p q: Proc, p ∉ crashed ∧ q ∉ crashed → q ∉ suspected[p])
```

**Don't we need a framework for temporal logic?** Well, actually not. Instead of
`[]` and `<>`, we can simply use `∀` and `∃` over indices. There is even a
deeper connection between linear temporal logic and first-order logic with
ordering, shown by [Hans Kamp][]. For example, see a recent [Proof of Kamp's
theorem][Rabinovich12] by Alexander Rabinovich. Temporal formulas are often
easier to read. So I prefer to accompany properties in Lean with temporal
properties in the documentation.

### 2.5. Specifying fairness and fair runs

Now that we have described the system behavior, can we proceed with the proofs?
Not so fast. If you have ever tried to prove liveness, you know that we have to
restrict our analysis to *fair* system executions.

For instance, our definition of `next` allows the scheduler to always choose
`advance_clock` as the next action. So we would end up with a sequence that
consists of states that only have the increasing clock values. Is it an
interesting sequence? Not really. We have not even had a chance to try other
actions. Usually, such executions are called unfair. We want to restrict our
liveness analysis to fair executions.

To save you guess work, here are the three kinds of conditions we want from a
fair execution in our failure detector:

 1. For every message $m$ that is sent, the message destination receives it on
 time, unless it crashes before the message $m$ expires. This is the constraint
 right from [partial synchrony](#22-partial-synchrony).
 
 1. If a process $p$ has a scheduled timeout, $p$ should process the timeout
 before the global clock advances too far, unless $p$ crashed before the timeout
 had to be handled. While this may sound obvious, this requirement is crucial
 for the failure detector.
 
 1. The global clock must advance infinitely often. Indeed, it is possible to
 construct a sequence of states that have the global clock increased only
 finitely many times. This effect is usually called *zenoness*, after [Zeno's
 paradoxes][Zeno]. We want to avoid such executions. If you do not believe this
 is possible, look carefully at the definition `rcv_heartbeat_request`.  It can
 receive the same message multiple times! Sure, we could eliminate this behavior
 by receiving every message at most once. It would be harder to do that in a
 more complex protocol. Just requiring non-zenoness is much simpler.

Lean has no idea about distributed algorithms and fair executions. We can get
some inspiration from TLA<sup>+</sup>. Unfortunately, fairness in
TLA<sup>+</sup> is a bit too complicated. If we wanted to transfer this approach
to our proofs, we would have to figure out how to write our fairness constraints
with strong fairness, weak fairness, and `ENABLED`.

To avoid this complex ceremony, we recall that our actions have very simple
structure. Essentially, every protocol state is constructed by executing one
of the six actions:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 218-224
 %}

Our key idea here is that we could explicitly force some of the actions to be
taken in a fair execution. To this end, we refine our transition relation `next`
with `next_a`:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 229-242
 %}

Of course, we would have to prove equivalence of `next` and `next_a`. Actually,
we have to account for the case `Init`, where we just require $s' = s$. This is
easy to do in Lean. Below is the theorem statement. Check
[PropositionalProofs.lean][] for the actual proof:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 925-929
 %}

Now, instead of reasoning just about sequences of protocol states, we can
reason about sequences of states and actions. Formally, we introduce the
definition of a *trace* and related definitions:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 247-266
 %}

Not every trace can be produced by the failure detector protocol. We define what
it means for a trace to be a run of the protocol, not necessarily a fair one,
and what it means for a trace to be a fair run of the protocol:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 305-330
 %}

Having all these definitions, we proceed with our fairness constraints. The
simplest one is `is_fair_clock`:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 300-303
 %}

Essentially, `is_fair_clock` says that we observe `AdvanceClock` in a trace
infinitely often.  In TLA<sup>+</sup>, it would be written like
`<>[]<advance_clock>_vars`. If you don't know what it means, just skip it.

Further, we define `is_fair_timeout` as follows:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 289-295
 %}

Finally, `is_reliable_communication` has the longest definition:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/Propositional.lean
  lean 273-284
 %}

Now we are ready for the proofs!

## 3. Proving strong completeness in Lean

The main theorem that we want to prove is `strong_completeness_on_states`, which
basically delegates the work to `strong_completeness` over fair traces:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 899-911
 %}

The below figure summarizes the lemmas (yellow) and theorems (green) that I had
to prove, in order to show `strong_completeness_on_states`.

{% include webp.html
    src="epfd-completeness-deps.png"
    alt="Proof schema" %}

If you want to understand the proofs, you should inspect
[PropositionalProofs.lean][] with the Lean extension for VSCode. I will only
give you human-readable summaries as well as my observations about how I wrote
these proofs.

### 3.1. Shorthand temporal definitions

I found it convenient to define shorthands for the temporal properties that are
used throughout the proofs. For instance, below is the definition of
`never_crashes`:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 27-30
 %}

This property can be visualized as follows:

<table class="timeline-table">
  <tr>
    <th>Time →</th>
    <td>0</td>
    <td>1</td>
    <td>2</td>
    <td>3</td>
    <td>4</td>
    <td>5</td>
  </tr>
  <tr>
    <th>crashed:</th>
    <td>{}</td>
    <td>{}</td>
    <td>{}</td>
    <td>{}</td>
    <td>{}</td>
    <td>{}</td>
  </tr>
  <tr>
    <th></th>
    <td>✅</td>
    <td>✅</td>
    <td>✅</td>
    <td>✅</td>
    <td>✅</td>
    <td>✅</td>
  </tr>
</table>
<p class="timeline-valid">[](p ∉ crashed) holds</p>

The negation of `never_crashes` is `eventually_crashes`:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 32-35
 %}

<table class="timeline-table">
  <tr>
    <th>Time →</th>
    <td>0</td>
    <td>1</td>
    <td>2</td>
    <td>3</td>
    <td>4</td>
    <td>5</td>
  </tr>
  <tr>
    <th>crashed:</th>
    <td>{}</td>
    <td>{}</td>
    <td>{}</td>
    <td>{p}</td>
    <td>{p}</td>
    <td>{p}</td>
  </tr>
  <tr>
    <th></th>
    <td>❌</td>
    <td>❌</td>
    <td>❌</td>
    <td>✅</td>
    <td>✅</td>
    <td>✅</td>
  </tr>
</table>
<p class="timeline-valid">&lt;&gt;(p ∈ crashed) holds</p>

We also need `eventually_never_alive`:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 37-42
 %}

<table class="timeline-table">
  <tr>
    <th>Time →</th>
    <td>0</td>
    <td>1</td>
    <td>2</td>
    <td>3</td>
    <td>4</td>
    <td>5</td>
  </tr>
  <tr>
    <th>alive[p]:</th>
    <td>{q}</td>
    <td>{q}</td>
    <td>{q}</td>
    <td>{}</td>
    <td>{}</td>
    <td>{}</td>
  </tr>
  <tr>
    <th></th>
    <td>❌</td>
    <td>❌</td>
    <td>❌</td>
    <td>✅</td>
    <td>✅</td>
    <td>✅</td>
  </tr>
</table>
<p class="timeline-valid">&lt;&gt;[] (q ∉ alive[p]) holds</p>

We also need `q_is_always_suspected` and `eventually_q_is_always_suspected`:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 44-57
 %}

<table class="timeline-table">
  <tr>
    <th>Time →</th>
    <td>0</td>
    <td>1</td>
    <td>2</td>
    <td>3</td>
    <td>4</td>
    <td>5</td>
  </tr>
  <tr>
    <th>suspected[p]:</th>
    <td>{}</td>
    <td>{}</td>
    <td>{}</td>
    <td>{q}</td>
    <td>{q}</td>
    <td>{q}</td>
  </tr>
  <tr>
    <th></th>
    <td>❌</td>
    <td>❌</td>
    <td>❌</td>
    <td>✅</td>
    <td>✅</td>
    <td>✅</td>
  </tr>
</table>
<p class="timeline-valid">&lt;&gt;[] (q ∈ suspected[p]) holds</p>

Finally, we need the definition of the set of crashing processes:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 59-64
 %}

### 3.2. Warming up with simple temporal lemmas

Before discussing hard-to-prove lemmas, let's have a look at a few very simple
ones. To start with, we can easily show that the global clock never decreases in
a single step. The proof is basically done by the `simp` tactic:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 100-114
 %}

Very much similar to `clock_is_monotonic_in_one_step`, we can prove that the set
of the crashed processes can only grow in a single step:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 116-131
 %}

We use these simple lemmas to prove that $clock$ never decreases in a fair run,
and once a process has crashed, it always remains crashed. In both cases, the
proof is done by simple induction over the indices in a fair run. For example,
here is the lemma `crashed_is_monotonic_in_fair_run`, together with its proof:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 162-185
 %}

Further, we prove another useful lemma: Given a clock value $t$, eventually
the global clock reaches the value $t$:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 187-197
 %}

You can check the [full proof of
eventually_clock_is_t](https://github.com/konnov/leanda/blob/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean#L187-L233).
It is not a long one, but it requires a bit of linear arithmetic to reason about
indices and clock constraints.

### 3.3. Proving completeness for two processes

Before we dive into the results for all processes, we focus on just two
processes in a fair run `tr`:

 - a process `p` that never crashes in `tr`,
 - a process `q` that eventually crashes in `tr`.

Since the Lean proofs are quite detailed, I provide the lemmas with short
human-readable proofs. Actually, I had to write proof schemas on paper, before
developing detailed proofs. The math-like proofs below are summaries of the
detailed Lean proofs, as my pen & paper proofs had several flaws.

#### 3.3.1. Main lemma: Eventually q is always suspected by p

To show strong completeness for $p$ and $q$, we prove the following key lemma:

**Lemma** `eventually_crashes_implies_always_suspected`. If $q$ crashes at some
time $j$ and $p$ never crashes, then there exists $k$ such that for all $i \ge
k$, we have $q \in \text{suspected}[p]$ at $i$.

Using the TLA<sup>+</sup> notation, we could write this lemma in temporal logic:

$$
\square (p \notin crashed) \land \Diamond (q \in crashed)
  \Rightarrow \Diamond \square (q \in suspected[p])
$$

This is how the lemma is formulated in Lean:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 716-722
 %}

You can check the [detailed proof in
Lean](https://github.com/konnov/leanda/blob/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean#L709-L722).
The proof is about 100 LOC long. I have asked ChatGPT to summarize the proof
similar to a mathematician's proof.  It looked very convincing, but the AI has
hallucinated a lot, by inventing additional lemmas and mixing process names.
Instead, here is my proof summary, 100% organic:

**Proof.** Since $q$ eventually crashes, we apply Lemma
`eventually_crashes_implies_never_alive` (see
[below](#332-eventually-q-is-never-alive-for-p)) to show that there is an index
$k$ such that for all $i \ge k$, we have $q \notin alive[p]$ at $i$. Now, we may
still have $q \in suspected[p]$ at $k$. Hence, we apply the fairness constraint
`is_fair_timeout` to show that there is an index $j > k$ such that $p$ timeouts
at $j$. By the definition of `timeout`, we have $q \in suspected[p]$ at $j + 1$,
as the action `timeout` updates `suspected[p]` with `Finset.univ \ alive[p]`,
and $q \notin alive[p]$ at $j$.

It remains to show that $q \in suspected[p]$ at an arbitrary $i > j$. We do this
by induction on $i$. All actions except `Timeout` preserve the value of the
field `suspected`, so we have $q \in suspected[p]$. In case of `Timeout r`, we
consider two cases: (1) $r \ne p$, and (2) $r = p$. When $r \ne p$, the value of
$suspected[p]$ does not change.  When $r = p$, we again invoke the conclusion
that $q \notin alive[p]$ at $i$. Similar to the above reasoning about the action
`timeout`, we conclude $q \in suspected[p]$ at all $i > j$. $\blacksquare$

#### 3.3.2. Eventually q is never alive for p

As you have noticed, we invoked Lemma `eventually_crashes_implies_never_alive`.
This is how it looks like in a human-readable form:

**Lemma** `eventually_crashes_implies_never_alive`. If $q$ crashes at some
time $j$ and $p$ never crashes, then there exists $k$ such that for all $i \ge
k$, we have $q \notin \text{alive}[p]$ at $i$.

Using the TLA<sup>+</sup> notation, we could write this lemma in temporal logic:

$$
\square (p \notin crashed) \land \Diamond (q \in crashed)
  \Rightarrow \Diamond \square (q \notin alive[p])
$$

This is how the lemma is formulated in Lean, the [detailed
proof in Lean](https://github.com/konnov/leanda/blob/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean#L538-L545)
is 170 LOC:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 538-544
 %}

**Proof.** Since $q$ eventually crashes, there is an index $i_{crash}$, so
$q \in crashed$ at $i_{crash}$. Let's denote with $t_{crash}$ the clock value at
$i_{crash}$. However, $p$ may still receive heartbeats from $q$ that were sent
in the past. Hence, we choose the time point $t_{magic}$:

$$
t_{magic} = max(\mathit{GST} + \mathit{MsgDelay}, t_{crash} + \mathit{MsgDelay}) + 1
$$

We invoke Lemma `eventually_clock_is_t` to show that eventually the global clock
reaches the value $t_{magic}$. Further, we invoke Lemma
`eventually_alive_is_empty` (see
[below](#333-non-crashing-p-resets-alive-infinitely-often)) to show that
eventually $alive[p] = \emptyset$ after that point. Hence, we have an index
$i_{empty}$ with the following constraints at:

 1. $alive[p] = \emptyset$ at $i_{empty}$,
 
 1. $q$ has crashed and no heartbeats from $q$ can longer arrive, as the global
 clock is past $\mathit{GST} + \mathit{MsgDelay}$,

The rest of the proof goes by induction over $i \ge i_{empty}$.  We have already
shown the inductive base. The inductive step is proven by contradiction: Assume
that there is an index $i + 1$, where $alive[p] \ne \emptyset$.  We do case
analysis on the action that produces the state at $i + 1$. There are two
interesting cases:

 1. A process $r$ times out. If $r \ne p$, the $r$ keeps the value of
 $alive[p]$.  If $p$ times out, it resets $alive[p]$ to $\emptyset$. In both
 cases, $alive[p] = \emptyset$.
 
 1. A process $\mathit{dst}$ receives a heartbeat reply $m$ from a process
 $\mathit{src}$. The cases of $dst \ne p$ or $src \ne q$ are trivial, as the
 predicate $q \in alive[p]$ does not change in those cases. The case of $src =
 q$ and $dst = p$ is the hardest one. First, we apply Lemma
 `crashed_process_does_not_send` (see below) to show that the message timestamp
 $m.ts$ is not greater than $t_{crash}$. Second, we apply Lemma
 `clock_is_monotonic_in_fair_run` to show that $clock \ge t_{magic}$ at point
 $i$. Third, we apply the constraint `isMsgTimely` from the definition of
 `rcv_heartbeat_reply`. We arrive at the following combination of linear
 constraints that do not have a solution:

$$
\require{cases}
\begin{cases}
  \mathit{m.ts} &\le t_{crash}\\
  clock &\ge t_{magic}\\
  clock &\ge m.ts\\
  clock &\le max(GST, m.ts) + \mathit{MsgDelay}
\end{cases}
$$

This inductive argument finishes the proof. $\blacksquare$
 
#### 3.3.3. Non-crashing p resets alive infinitely often

We invoked Lemma `eventually_alive_is_empty` in the previous section. This is
how this lemma looks like in a human-readable form:

**Lemma** `eventually_alive_is_empty`. If $p$ never crashes, then for every
$k > 0$,
there is $i \ge k$ such that we have $\text{alive}[p] = \emptyset$ at $i$.

Using the TLA<sup>+</sup> notation, we could write this lemma in temporal logic:

$$
\square (p \notin crashed)
  \Rightarrow \square \Diamond (alive[p] = \emptyset)
$$

This is how the lemma is formulated in Lean, the [detailed
proof in Lean](https://github.com/konnov/leanda/blob/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean#L241)
is 30 LOC:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 241-248
 %}

**Proof.** Since $p$ never crashes, we apply the fairness constraint
`is_fair_timeout` to the index $k$. Hence, there exists an index $i$,
so that $p$ times out at $k + i$. When processing the action `timeout`,
process $p$ resets $alive[p]$ to the empty set. $\blacksquare$
 
#### 3.3.4. A crashed process q stops sending messages

We invoked Lemma `crashed_process_does_not_send` in the proof of
`eventually_crashes_implies_never_alive`. This is how this lemma looks like in a
human-readable form:

**Lemma** `crashed_process_does_not_send`. If $q$ is crashed at $k$ and the
clock value at $k$ equals to some $c$, then for every $i \ge 0$ and every
message $m \in sent$ at $k + i$, if $m.src = q$, then $m.ts \le c$.

Using the TLA<sup>+</sup> notation, we could write this lemma in temporal logic:

$$
\square (\forall c \in \mathbb{N}: (q \in crashed \land clock = c)
  \Rightarrow \square (\forall m \in sent: (m.src = q) \Rightarrow m.ts \le c))
$$

This is how the lemma is formulated in Lean, the [detailed
proof in Lean](https://github.com/konnov/leanda/blob/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean#L419)
is 110 LOC:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 419-425
 %}

Although this lemma seems to be obvious, the proof is relatively long. It is
mostly technical.

**Proof.** The proof is done by induction on $i$. It invokes two other lemmas:
  
  1. Lemma `crashed_is_monotonic_in_fair_run` that we discussed before, and
  
  1. Lemma `no_sent_from_the_future` (see
  [below](#335-no-message-sent-from-the-future)), which states that no message
  can have a timestamp above the current value of the global clock.

The induction goes by case analysis on the action that is executed at point $i$.
There are two interesting cases that extend the set of sent messages $sent$:

 1. A timeout by process $r$. Since $q$ crashed at $k$, it remains crashed at
 $k+i$. Hence, $q$ cannot timeout, and, thus, $r \ne q$. Therefore, the new
 heartbeat requests in $sent$ do not have $q$ as their source.
 
 1. Receiving a heartbeat request by process $r$. Again, $q$ is crashed at
 $k+i$, and $r \ne q$. Therefore, the new heartbeat replies in $sent$ do not
 have $q$ as their source. $\blacksquare$

#### 3.3.5. No message sent from the future

Lemma `no_sent_from_the_future` plays an important role in the proof of
`crashed_process_does_not_send`. This is how this lemma looks like in a
human-readable form:

**Lemma** `no_sent_from_the_future`. For every point $i \ge 0$ and every
message $m \in sent$ at $i$, it holds that $m.ts \le clock$.

Using the TLA<sup>+</sup> notation, we could write this lemma in temporal logic:

$$
  \square (\forall m \in sent: m.ts \le clock)
$$

This is how the lemma is formulated in Lean, the [detailed
proof in Lean](https://github.com/konnov/leanda/blob/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean#L303)
is 110 LOC:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 303-308
 %}

**Proof.** The proof is done by induction on $i$ and case analysis on the
action executed at $i$. The proof is quite mechanical. We basically show that
either the set $sent$ does not change, whereas the value of $clock$ does not
decrease, or the new messages have their timestamp set to $clock$. Such messages
are sent in `timeout` and `rcv_heartbeat_request`. $\blacksquare$

Most likely, a human reader would immediately infer this lemma without much
thought. However, the lemma’s proof works only because we’re using the global
clock value $clock$ when sending messages. If we used local clocks for
timestamps, the lemma would no longer hold.

#### 3.3.6. Other lemmas

The proof of `no_sent_from_the_future` invokes another lemma called
`inductive_inv`.  It provides us with a general proof of inductive invariants in
the context of our protocol. I expected more proofs to use `inductive_inv`, but
it happened that the other proofs required additional temporal reasoning beyond
simple inductive invariants.

Finally, we have another lemma called `when_clock_is_positive_step_is_non_init`.
It is just a technical lemma to work around a corner case that could not be
solved by the tactic `omega`. You can check [this
lemma](https://github.com/konnov/leanda/blob/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean#L279).
There is really nothing interesting in it.

Overall, when we go down the dependency tree of our lemmas, the proofs in the
top require quite a bit of creative thinking. The proofs in the bottom like
`crashed_process_does_not_send` and `no_sent_from_the_future` are quite
mechanical. They are long but they do not require much thinking. It would be
great if those proofs could be derived automatically.

### 3.4. From 2 to N processes

With [main lemma][], we have proven strong completeness for a pair of processes.
Actually, we could just stop there. However, I decided to go the last mile and
prove strong completeness for arbitrary sets of processes, exactly as the
properties are written in [DP2011][]. The last mile happened to be harder than I
anticipated. Nevertheless, the findings and the proof technique are quite
interesting.

#### 3.4.1. Defining the crashed processes

When I was writing a proof on paper, I was writing something along these lines:

> Given a fair run, let us define the set `Crashed` that contains exactly those
processes that crash in the run.

Hence, I tried to write a definition like this in Lean:

```lean
def crashed_set (tr: Trace Proc) :=
  { p: Proc | ∃ i ∈ Nat, p ∈ (tr i).s.crashed }
```

Lean produced an a bit obscure error: "failed to synthesize Membership ?m.10217 Type".

So I thought, OK, it seems to be hard to define a potentially infinite set
that uses a proposition over an infinite sequence. Let's try finite sets:

```lean
def crashed_set (tr: Trace Proc) :=
  Finset.univ.filter (fun p => ∃ i ∈ ℕ, p ∈ (tr i).s.crashed)
```

The same error. What is going on? If we rewrite the definition like this, it
works (obviously, it does not do what we want though):

```lean
def crashed_set (tr: Trace Proc) :=
  Finset.univ.filter (fun p => p ∈ (tr 0).s.crashed)
```

Ugh. It looks like Lean does not like that we have to prove existence of a
member of an infinite set to filter a finite set. It would be fine to use
that in a proposition, but not in a definition. Well, this kind of makes sense.
We cannot just compute `crashed_set`, as we cannot predict when processes crash!
Lean is a bit strict about random mathy stuff.

Interestingly though, given a fair run, we should be able to define the set of
the crashed processes. This set is bounded from above with the finite set
`Finset.univ` of type `Finset Proc`. Also, as we showed in
`crashed_is_monotonic_in_fair_run`, the set of crashed processes can only grow,
not shrink. Hence, in theory, we should be able to define `crash_set` as the
fixpoint of the operator that transforms $s_i$ into $s_{i+1}$ in our run. We
should be able to apply [Knaster-Tarski][] theorem. Conversations with ChatGPT
about Knaster-Tarski in Lean opened a new rabbit hole.

This was getting too hard, all of a sudden. So I have decided that it was not
worth the effort. If I had a conversation like that with a customer, they would
tell me to stop right there. Hence, I decided that the properties should simply
have two parameters:

 - The set `(Crashed: Finset Proc)`, and
 - a proof that it's exactly the set of the crashing processes.

This is why our [temporal properties][] have these two parameters.

#### 3.4.2. Where do the suspected sets meet?

Recall that we have proven the main lemma for two processes, and it looks like
this:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 716-722
 %}

The yet-to-prove theorem `strong_completeness` looks like this:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 850-856
 %}

The challenge here is that the theorem claims existence of a single index $k$
for all processes, whereas we get different indices when applying the lemma.
Intuitively, we should be just able to pick the maximum index among them. This
starts to smell like the above problem with the crashing sets. On the other
hand, choosing the maximum among the values of a finite set should be possible.
This made me think about [Well-founded induction][]. Intuitively, we should be
able to start with the empty set, add elements one-by-one and pick the maximum
of two numbers at each inductive step: the maximum of the smaller set, and the
value for the new element. This is what [`Finset.induction`][Finset.induction]
can do for us!

Another way to see the issue is by comparing these two temporal formulas in
TLA<sup>+</sup>:

$$
\begin{align}
  \forall p, q:\ \Diamond \square (&p \notin crashed \land q \in crashed
    \Rightarrow q \in suspected[p]) \tag{1}\\
  \Diamond \square (\forall p, q:\ &p \notin crashed \land q \in crashed
    \Rightarrow q \in suspected[p]) \tag{2}
\end{align}
$$

Hence, to go from Equation (1) to Equation (2), we have to move two quantifiers
$\forall p$ and $\forall q$ inside $\Diamond \square (\dots)$. This observation
together with `Finset.induction` gave me this nice theorem:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/TemporalLemmas.lean
  lean 17-26
 %}

The proof of the theorem is not hard, but it is 60 LOC. So you can [check it
online](https://github.com/konnov/leanda/blob/a96eb677d7f514e8d6ac1cdd6970643f2488b442/epfd/Epfd/TemporalLemmas.lean#L22).

By using this theorem twice, we finally arrive at the final lemma:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 810-845
 %}

With this lemma, we finally prove `strong_completeness`:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/24e84d9f9a16831df31fc6f5577ce96ec56df55e/epfd/Epfd/PropositionalProofs.lean
  lean 850-856
 %}

The
[proof](https://github.com/konnov/leanda/blob/a96eb677d7f514e8d6ac1cdd6970643f2488b442/epfd/Epfd/PropositionalProofs.lean#L850-L851)
is just a technical application of `eventually_crashes_implies_always_suspected`
and `eventually_always_suspected_meet`.  It is 40 LOC of unfolding definitions
and repacking them into the right format.

# Conclusions

This was probably the longest blog post I have ever written. It almost feels
like an academic paper. I don't expect many people to read all of it. If you
have read the whole blog post and reached the conclusions, leave me a comment! I
really want to know, whether anyone manages to read the whole writeup.

<a name="end"></a>

## Footnotes

[^1]: Christian Cachin, Rachid Guerraoui, and Luís Rodrigues. Introduction to Reliable and Secure Distributed Programming. Second Edition, Springer, 2011, XIX, 320 pages
[Igor Konnov]: https://konnov.phd
[Hans Kamp]: https://en.wikipedia.org/wiki/Hans_Kamp
[Knaster-Tarski]: https://en.wikipedia.org/wiki/Knaster%E2%80%93Tarski_theorem
[Well-founded induction]: https://en.wikipedia.org/wiki/Well-founded_relation
[Lean]: https://github.com/leanprover/lean4
[Apalache]: https://apalache-mc.org/
[TLC]: https://github.com/tlaplus/tlaplus
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
[DLS88]: https://dl.acm.org/doi/abs/10.1145/42282.42283
[Rabinovich12]: https://drops.dagstuhl.de/storage/00lipics/lipics-vol016-csl2012/LIPIcs.CSL.2012.516/LIPIcs.CSL.2012.516.pdf
[Finset.induction]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Insert.html
[Zeno]: https://en.wikipedia.org/wiki/Zeno%27s_paradoxes
[spec-epfd]: #2-eventually-perfect-failure-detector-in-lean
[spec-partial-synchrony]: #22-partial-synchrony
[temporal properties]: #24-specifying-the-temporal-properties
[spec-fairness]: #25-specifying-fairness-and-fair-runs
[proving-completeness]: #3-proving-strong-completeness-in-lean
[main lemma]: #331-main-lemma-eventually-q-is-always-suspected-by-p
[crashed processes]: #341-defining-the-crashed-processes
[happy to help]: {{ 'contact/' | relative_url }}
[leave-comment]: #end