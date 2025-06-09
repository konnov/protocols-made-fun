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

Hence, I opened the [book][DP2011] (DP2011) on Reliable and Secure Distributed
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

Below is the nice diagram that illustrates the dependencies between the theorems
(green) and lemmas (yellow) that I had to prove, culminating in the theorem
`strong_completeness_on_states`. Notice `forall_FG_implies_FG_forall` is not a
lemma. Actually, it is a general theorem about swapping universal quantifiers
and eventually-always, which could be reused in other proofs.

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

To avoid any potential copyright issues, I am not giving the pseudo-code from
the book. If you want to see the original version, go check
[DP2011][][^1], Algorithm 2.7, p. 55. Below is an adapted version, which
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

### 2.2. Partial synchrony

The algorithm is designed to work under partial synchrony. Unfortunately,
[DP2011][] does not give us a precise definition of what it means. So we
go back to the paper [Dwork, Lynch, and Stockmeyer][DLS88] (DLS88) who
introduced partial synchrony. There are several kinds of partial synchrony in
the paper. We choose the one that is probably the most commonly used nowadays:
There is a period of time called global stabilization time (GST), after which
every correct process $p$ receives a message from a correct process $q$ no later
than $\mathit{MsgDelay}$ time units after it was sent by $q$. Both
$\mathit{GST}$ and $\mathit{GST}$ are unknown to the processes, and may change
from run to run. It is also important to fix the guarantees about the messages
that were sent before $\mathit{GST}$. We assume that they are received by
$\mathit{GST} + \mathit{MsgDelay}$ the latest.

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
of the whole system, when `dst` processes a heartbeat request. In particular,
`dst` cannot be crashed when receiving the message, the message has to be
timely, etc.  Similar to TLA<sup>+</sup>, we specify that certain fields
preserve their values.  Actually, we could update the structure `s'` instead of
writing down multiple equalities over the fields. However, it would make the
proofs more cumbersome. I could not find a simple way to express something like
TLA<sup>+</sup>'s `UNCHANGED` over multiple variables.

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
`init` comes later). Are we done? Not quite. Since we are specifying the
behavior of the distributed system, not just the behavior of individual
processes, we need two more actions.

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
side of `→` could be written like:

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
ordering, shown by Kamp. For example, see a recent [Proof of Kamp's
theorem][Rabinovich12] by Alexander Rabinovich. Of course, temporal formulas are
often less bulky. So I prefer to accompany properties in Lean with temporal
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
analysis to fair executions.

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
[PropositionalProofs.lean][] with the Lean extension for VSCode. I am going to
highlight only my observations about how I wrote these proofs.

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
one. To start with, we can easily show that the global clock never decreases in
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

We use these simple lemmas to prove that clock never decreases in a fair run,
and once a process has crashed, it always stays crash. In both cases, the proof
is done by simple induction over the indices in a fair run. For example, here is
the lemma `crashed_is_monotonic_in_fair_run`, together with its proof:

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
It is not a long one, but it require a bit of linear arithmetic to reason about
indices and clock constraints.


<a name="end"></a>

[^1]: Christian Cachin, Rachid Guerraoui, and Luís Rodrigues. Introduction to Reliable and Secure Distributed Programming. Second Edition, Springer, 2011, XIX, 320 pages
[Igor Konnov]: https://konnov.phd
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
[Zeno]: https://en.wikipedia.org/wiki/Zeno%27s_paradoxes
[happy to help]: {{ 'contact/' | relative_url }}
[leave-comment]: #end