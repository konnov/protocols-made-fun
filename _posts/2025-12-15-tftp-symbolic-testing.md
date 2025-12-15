---
layout: post
title: "Interactive Symbolic Testing of TFTP with TLA+ and Apalache"
date: 2025-12-15
categories: tlaplus
tlaplus: true
math: true
shell: true
typescript: true
hidden: true
feed: false
---

**Author:** [Igor Konnov][]

**Date:** December 15, 2025

*Note: I mostly stopped using LLMs for proof-reading my texts. Enjoy my typos
and weird grammar!*

**Abstract.** As promised in the [blog post on small-scope
hypothesis][small-scope], I am continuing with the main body of the talk that I
presented at the internal Nvidia FM Week 2025. This blog post is rather long. If
you do not want to read the whole post, here are the most exciting new
developments:

 - A new JSON-RPC server API for [Apalache][], which allows external tools and
 AI-generated scripts to drive the symbolic execution of TLA<sup>+</sup>
 specifications and interact with the solver.  Read the section on [The new
 JSON-RPC API of Apalache](#4-the-new-json-rpc-api-of-apalache).
 
 - A new approach to conformance testing of TLA<sup>+</sup> specifications and
 real implementations, called **interactive symbolic testing**. This approach is
 inspired by the work of [McMillan and Zuck (2019)][MZ19] on testing of the QUIC
 protocol with IVy and SMT. Read the section on [Interactive symbolic testing with
 SMT](#3-interactive-symbolic-testing-with-smt).
 
 - A case study on testing multiple open-source implementations of TFTP,
 including unexpected (but not harmful) deviations from the protocol. This case
 study includes the experience report on using Claude to bootstrap the harness
 for testing TFTP implementations against the TLA<sup>+</sup> specification.
 Read the section on [Bootstrapping the testing harness with
 Claude](#7-bootstrapping-the-testing-harness-with-claude) and [Testing against
 adversarial behavior](#9-testing-against-adversarial-behavior).

In this blog post, I am using TLA<sup>+</sup>. The same tooling and results
equally apply to [Quint][].

**Contents:**

1. [Introduction](#1-introduction)
2. [Model-based testing and trace validation](#2-model-based-testing-and-trace-validation)
3. [Interactive symbolic testing with SMT](#3-interactive-symbolic-testing-with-smt)
4. [The new JSON-RPC API of Apalache](#4-the-new-json-rpc-api-of-apalache)
5. [Case study: TFTP protocol](#5-case-study-tftp-protocol)
6. [Initial TLA<sup>+</sup> specification of TFTP](#6-initial-tla-specification-of-tftp)
7. [Bootstrapping the testing harness with Claude](#7-bootstrapping-the-testing-harness-with-claude)
8. [Debugging the TLA<sup>+</sup> specification with the implementation](#8-debugging-the-tla-specification-with-the-implementation)
9. [Testing against adversarial behavior](#9-testing-against-adversarial-behavior)
10. [The specification as a differential testing oracle](#10-the-specification-as-a-differential-testing-oracle)
11. [Prior Work](#10-prior-work)
12. [Conclusions](#11-conclusions)

## 1. Introduction

This work aims at demonstrating how to answer the following two questions with
[Apalache][]:

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
engineers were telling this to me all the time!) Check [the prior work
section](#10-prior-work) for the papers and talks on this topic.  Roughly
speaking, the approaches follow the two ideas:

 - **Model-based testing (MBT)**. The TLA<sup>+</sup> specification is used to
 generate test cases that are then executed against the implementation. This is
 an answer to question 1 above. The state exploration is driven by the
 specification. Hence, we are testing, whether the implementation matches the
 inputs and outputs, as produced by the specification.
 
 - **Trace validation (TV)**. The traces are collected from the implementation
 and checked against the TLA<sup>+</sup> specification. This is an answer to
 question 2 above. State exploration is driven by the implementation, e.g., by
 executing the existing test suites, or just by running the system for some
 time. Hence, we are testing whether the specification matches the inputs and
 outputs of the implementation. Alternatively, we may check whether the
 implementation states may be lifted to the specification states, in order to
 produce a feasible trace in the specification.
 
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
 [Markus Kuppe et. al. (2024)][K24b]. In other cases, it may be quite difficult
 to do, e.g., when we want to dump the internal states of the SUT. In a
 concurrent system this may require a global lock and traversing large data
 structures. In a distributed system, this may further require a distributed
 snapshot or using vector clocks.
 
 1. We have to run the whole system to collect traces. It is hard to isolate one
 component, e.g., one network node.

## 3. Interactive symbolic testing with SMT

As we can see, both model-based testing and trace validation in their above
formulation are non-interactive. They both require a complete trace to be
produced first, and **there is no feedback loop between the specification and
the implementation**.

There is a third way to do conformance testing that leverages SMT solvers, yet
receives feedback from the implementation during the testing. I will call it
**interactive symbolic testing**. I think the first time I heard about this
approach was from [Giuliano Losa][], when he explained the paper by [Ken
McMillan and Leonore Zuck (2019)][MZ19] to me. If you have not read this paper
yet, I highly recommend doing so. On the naming side, McMillan and Zuck call
their approach "specification-based testing". I find this name to be a bit
non-descriptive, as MBT is also specification-based.

The idea is to generate an action with the SMT solver by following the
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

To implement this approach to testing with Apalache, we would have to find a way
for Apalache and the test harness to communicate. My experience with development
of Apalache shows that **fixing exploration strategies inside the model checker
is not a good idea**. People always want to tweak them a bit for their purposes.
Given this observation, [Thomas Pani][] and I have decided to implement a simple
server API for Apalache that would allow external tools to drive the symbolic
execution of TLA<sup>+</sup> specifications.

## 4. The new JSON-RPC API of Apalache

[Thomas][Thomas Pani] and I wanted to have a lightweight API that we could use
from any programming language without writing too much boilerplate code. At this
point, every engineer would whisper: hey, you need gRPC, I've got some. Well, we
tried gRPC in the integration of [Apalache][] with [Quint][]. It is hard to call
gRPC lightweight.

So we have decided to go with [JSON-RPC][] this time, which is a very simple
protocol that works over HTTP/HTTPS. Implementing a JSON-RPC server is quite
straightforward.  Since Apalache is written in Scala, which is JVM-compatible,
we can use the well-known and battle-tested libraries. Perhaps, a bit
unexpectedly for a Scala project, I've decided to implement this server with
[Jetty][] for serving the HTTP requests and [Jackson][] for JSON serialization.
(The reason is that we have already burnt ourselves with fancy but poorly
supported libraries in Scala.) The resulting server is lightweight and fast.
Moreover, it can be tested with command-line tools like [curl][].

The state-chart diagram of the Apalache JSON-RPC server for a single session is
shown below.

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/apalache-api.svg" alt="Apalache JSON-RPC API">
</picture>

To see a detailed description of this API, check [Apalache JSON-RPC][].  Just to
give you the taste of it, here is how you start the server without having
anything installed but Docker:

```shell
$ docker pull ghcr.io/apalache-mc/apalache
$ docker run --rm /tmp:/var/apalache -p 8822:8822 \
    ghcr.io/apalache-mc/apalache:latest \
    server --server-type=explorer
```

Now, we create a new Apalache session with a TLA<sup>+</sup> specification (in a
separate tab):

```shell
$ SPEC=`cat <<EOF | base64
---- MODULE Inc ----
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Init == I:: x = 0
Next == (A:: (x < 3 /\\ x' = x + 1)) \\/ (B:: (x > -3 /\\ x' = x - 1))
Inv3 == Inv:: x /= 0
\* @type: () => <<Bool, Bool, Bool>>;
View == <<x < 0, x = 0, x > 0>>
=====================
EOF`
$ curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"loadSpec","params":{"sources": [ "'${SPEC}'" ],
       "invariants": ["Inv3"], "exports": ["View"]},"id":1}'
```

Is not that amazing? No protobuf, no code generation, just pure shell and
readable JSON.

Having the specification loaded, we load the predicate `Init` into the solver
context, which is encoded as transition 0:

```shell
$ curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"assumeTransition","params":{"sessionId":"1",
       "transitionId":0,"checkEnabled":true},"id":2}'
```

Assuming that the previous call returned `ENABLED`, we switch to the next
step, which applies the effect of `Init` to the current symbolic state:

```shell
$ curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"nextStep","params":{"sessionId":"1"},"id":3}'
```

Now, we can check the invariant `Inv3` against all states that satisfy `Init`:

```shell
$ curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"checkInvariant",
       "params":{"sessionId":"1","invariantId":0},"id":3}'
```

Since invariant `Inv3` is violated by the initial state, the server returns
`VIOLATED`, along with a counter-example trace:

```json
{
  "jsonrpc": "2.0",
  "id": 3,
  "result": {
    "sessionId": "1",
    "invariantStatus": "VIOLATED",
    "trace": {
      "#meta": {
        "format": "ITF",
        "varTypes": { "x": "Int" },
        "format-description": "https://apalache-mc.org/docs/adr/015adr-trace.html",
        "description": "Created by Apalache on Thu Dec 11 16:56:47 CET 2025"
      },
      "vars": [ "x" ],
      "states": [ {
          "#meta": { "index": 0 },
          "x": { "#bigint": "0" }
      } ]
    }
  }
}
```

The trace is encoded in the [ITF format][ITF], which is a simple JSON-based
format for TLA<sup>+</sup> and Quint traces.

Had the invariant been violated on a deeper trace, we would have to assume more
transitions by calling `assumeTransition` and `nextStep` multiple times.

If you want to access this API from Python right away, use two helper libraries:

  - [apalache-rpc-client][] for interacting with the JSON-RPC server of
  Apalache, and
  
  - [itf-py][] for serializing and deserializing ITF traces.

## 5. Case study: TFTP protocol

To experiment with interactive symbolic testing and the new JSON-RPC API, I
wanted to choose a relatively simple network protocol that had multiple
implementations. After several sessions with ChatGPT, I ended up with the
Trivial File Transfer Protocol (TFTP) as a reasonable target for this small
project.

The Wikipedia page on [TFTP][] gives us a good overview of the protocol. In
short, TFTP is a simple protocol to transfer files over UDP. It supports reading
and writing files from a remote server. It is mostly used for booting from the
network. The protocol is simple enough to be specified in TLA<sup>+</sup>
without too much effort, yet it has enough complexity to make the testing effort
interesting. Actually, I've only specified reading requests (RRQ) and no writing
requests (WRQ) to keep the scope manageable.

You can find more detailed specifications in the original [RFC 1350][], as well
as in its extensions [RFC 2347][], [RFC 2348][], and [RFC 2349][]. RFC 1350
defines a simple non-negotated version of the protocol. Below is an example of
such an interaction between the client and the server. Notice that the client
first sends a read request (RRQ) to the server on the control port 69, which
responds with the first data block (DATA) on a newly allocated ephemeral port.
The client acknowledges (ACK) the received data block on the same ephemeral
port.  This continues until the server sends the last data block, which is
smaller than the maximum block size (512 bytes by default).

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/rrq1350.svg"
    alt="Read request and transfer as per RFC 1350">
</picture>

Further, [RFC 2347][] defines an option negotiation phase that happens right after the
read request. The client and the server may negotiate options like block size,
timeout, and transfer size. [RFC 2348][] defines the block size option, while
[RFC 2349][] defines the transfer size option. Below is an example interaction with
option negotiation:

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/rrq2347.svg"
    alt="Read request and transfer as per RFC 2347">
</picture>

The cool thing about TFTP is that it has multiple open-source implementations of
TFTP clients and servers in different programming languages. Here are some of
them:

 - [tftp-hpa][] is the canonical implementation of TFTP for Linux (and UNIX?) in C.
 
 - [atftpd][] is advanced TFTP, which is intended for fast boot in large
 clusters, also in C.
 
 - [dnsmasq][] is a lightweight DNS and DHCP server that also includes a TFTP
 server, in C.
 
 - [rs-tftpd][] (Rust) is an implementation of a TFTP server in Rust.
 
 - [gotfpd][] (Go) is an implementation of a TFTP server in Go.
 
 - busybox also has its minimalistic implementation for file reads.

## 6. Initial TLA<sup>+</sup> specification of TFTP

In the first stage of this experiment, I read the RFCs and wrote a
TLA<sup>+</sup> specification of the TFTP protocol. At that stage, I did not
introduce packet loss, duplication, or reordering. I just wanted to have a
simple working specification that I could use for testing the implementations.
**This stage took me just two days.** Well, I have been writing plenty of
TLA<sup>+</sup> specifications in the past.

You can check this initial specification in the [initial commit][] of the
[testing repo][]. The main body of the specification lives in `tftp.tla`,
which imports several several auxiliary modules:

 - `typedefs.tla` defines the types of the data structures and the basic
 constructors for these data structures. Since I am using Apalache, the
 specification needs type definitions. Luckily, these days, I just write the
 type definitions in comments and let Claude generate the auxilliary operators
 such as constructors and accessors. If you already have an untyped
 specification, Claude is good at figuring out the types in the agent mode. Just
 use [this prompt][types-prompt].
 
 - `util.tla` defines common utility definitions such as `Min`, `Max`, and
 option conversions.
 
Finally, `MC2_tftp.tla` defines a protocol instance of two clients and one
server. If you stumble upon the definitions that end with `View` there, ignore
them. They are not essential for this blog post. I used them to experiment with
more advanced symbolic exploration scripts.

If you are not familiar with TLA<sup>+</sup>, or your TLA<sup>+</sup> skills are
rusty, I recommend giving one of the definitions and this prompt to ChatGPT. It
actually explains TLA<sup>+</sup> quite well:

```
Assume that I am a software engineer. I don't know TLA+ but know Golang or Rust.
Explain me this TLA+ snippet using my knowledge: ...
```

To see the kinds of actions this initial specification had, have a look at the
definition of `Next` in `tftp.tla`:

{% github_embed
  https://raw.githubusercontent.com/konnov/tftp-symbolic-testing/6fb00d1878b7e37a629868ac25b853d95b16cbdc/spec/tftp.tla
  tlaplus 470-499
 %}

{% include tip.html content="Do not spend too much time on reading this
initial specification. I misunderstood several thigs about TFTP from the
RFCs, which I fixed later. Especially, the timeouts are completely wrong
in this initial version. Good that the actual implementations helped me to
find these mistakes!"
%}

**Falsy invariants**. As I always do, I also specified "falsy invariants" to
produce interesting examples. For example, using the invariant
`RecvThreeDataBlocksEx` below, I can easily produce a trace where a client
receives three data blocks from the server.

```tla
\* Check this falsy invariant to see an example of a client receiving 3 blocks.
RecvThreeDataBlocksEx ==
    ~(\E p \in DOMAIN clientTransfers:
        Len(clientTransfers[p].blocks) >= 3)
```

If you want to try it right way without installing anything, just do this with
docker:

```shell
$ git clone git@github.com:konnov/tftp-symbolic-testing.git
$ git checkout 6fb00d1878b7e37a629868ac25b853d95b16cbdc
$ docker pull ghcr.io/apalache-mc/apalache
$ docker run --rm -v `pwd`:/var/apalache ghcr.io/apalache-mc/apalache \
  check --inv=RecvThreeDataBlocksEx MC2_tftp.tla
```

**Trace visualization.**
Since Apalache emits traces in the [ITF format][ITF], which has a very simple
schema in JSON, it was easy for me to convince Claude to produce a Python script
that would convert ITF traces to human-readable state charts in Mermaid. Here is
just an example of such a trace produced by Apalache when checking the invariant
`RecvThreeDataBlocksEx` in Mermaid:

```
sequenceDiagram
    participant ip10_0_0_3_port65000 as 10.0.0.3:65000
    participant ip10_0_0_1_port10000 as 10.0.0.1:10000
    participant ip10_0_0_1_port69 as 10.0.0.1:69

    ip10_0_0_3_port65000->>ip10_0_0_1_port69: RRQ(file1, blksize=0, timeout=4)
    ip10_0_0_1_port10000->>ip10_0_0_3_port65000: DATA(blk=1, 512B)
    ip10_0_0_3_port65000->>ip10_0_0_1_port10000: ACK(blk=1)
    ip10_0_0_1_port10000->>ip10_0_0_3_port65000: DATA(blk=2, 512B)
    ip10_0_0_3_port65000->>ip10_0_0_1_port10000: ACK(blk=2)
    ip10_0_0_1_port10000->>ip10_0_0_3_port65000: DATA(blk=3, 0B)
    ip10_0_0_3_port65000->>ip10_0_0_1_port10000: ACK(blk=3)
```

This is how it looks like when rendered by [Mermaid][]:

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/tftp3.svg"
    alt="Visualized trace of TFTP client receiving three data blocks">
</picture>

**Note on abstractions.** Similar to the [McMillan and Zuck][MZ19], I tried
to avoid unnecessary abstractions and approximations in the specification.  If
you look at the type definition of a TFTP packet in
[`typedefs.tla`](https://github.com/konnov/tftp-symbolic-testing/blob/6fb00d1878b7e37a629868ac25b853d95b16cbdc/spec/typedefs.tla),
you will see that all fields except `data` are modeled as strings and integers:

{% github_embed
  https://raw.githubusercontent.com/konnov/tftp-symbolic-testing/6fb00d1878b7e37a629868ac25b853d95b16cbdc/spec/typedefs.tla
  tlaplus 18-36
 %}

Thinking about it now, I could even model `data` as a sequence of bytes, but it
was obvious to me that only the length of `data` matters for the protocol logic.

## 7. Bootstrapping the testing harness with Claude

Now, we have the initial TLA<sup>+</sup> specification of TFTP and the standard
implementation [tftp-hpa][], which is the default `tftpd` server on Linux.

I wanted to avoid running the TFTP server on my laptop. What if I accidentally
find a bug that corrupts my file system? So I have decided to run the server and
the client harnesses in Docker containers. This way, I could easily reset the
SUT and have an isolated network for the TFTP server and clients.

Below is the architecture of the test harness that I had in mind. It's quite a
bit overengineered for testing TFTP. I also wanted to experiment with Docker
networking and managing multiple containers for potential future projects.

```
┌──────────────────────────────────────────────────────────────────┐
│                        Host Machine                              │
│                                                                  │
│  ┌────────────────────────────────────────────────────────────┐  │
│  │ harness.py                                                 │  │
│  │  - Coordinates symbolic execution                          │  │
│  │  - Manages Apalache server                                 │  │
│  │  - Controls Docker containers                              │  │
│  │  - Generates and saves test runs                           │  │
│  └────────┬────────────────────────┬──────────────────────────┘  │
│           │                        │                             │
│           ▼                        ▼                             │
│  ┌─────────────────┐     ┌──────────────────────────┐            │
│  │ Apalache Server │     │  Docker Manager          │            │
│  │  (port 8822)    │     │  - Network: 172.20.0.0/24│            │
│  └─────────────────┘     └──────────┬───────────────┘            │
│                                     │                            │
└─────────────────────────────────────┼────────────────────────────┘
                                      │
                         ┌────────────┴──────────────┐
                         │   Docker Network          │
                         │   (172.20.0.0/24)         │
                         │                           │
         ┌───────────────┼───────────────────────────┼─────────────┐
         │               │                           │             │
         ▼               ▼                           ▼             │
  ┌─────────────┐ ┌─────────────┐          ┌─────────────┐         │
  │ TFTP Server │ │  Client 1   │          │  Client 2   │         │
  │ 172.20.0.10 │ │ 172.20.0.11 │          │ 172.20.0.12 │         │
  │             │ │             │          │             │         │
  │ tftp-hpa    │ │ Python      │          │ Python      │         │
  │ Port: 69    │ │ TCP: 15001  │          │ TCP: 15002  │         │
  │ Data:1024-27│ │ (control)   │          │ (control)   │         │
  └─────────────┘ └─────────────┘          └─────────────┘         │
         ▲               │                           │             │
         │               │    UDP TFTP packets       │             │
         └───────────────┴───────────────────────────┘             │
                                                                   │
                         Docker Containers                         │
                                                                   │
                         tftp-test-harness:latest                  │
                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

**LLMs will do the work?** As you could have guessed, I had no interest in
writing the Docker files and the test harness from scratch. Having heard from so
many people that LLMs are so amazing, I have decided to give Claude a try at
generating the test harness.

Hence, I spent about four hours writing a very detailed prompt for Claude that
explained how I want the test harness to look like (the above architecture
diagram is actually generated by Claude from my prompt).

**Pushing the button!** So I've run Claude in the agent mode with my prompt and
went for a coffee break. You can see the first generated version in [this
commit](https://github.com/konnov/tftp-symbolic-testing/commit/063da7d2b79c07dfb64225da852440c98b76c41e3).
The result looked so exciting and amazing until I looked at `CHECKLIST.md`:

```
## Notes

- The framework is complete and production-ready
- Remaining work is mostly about connecting components
- Each task is independent and can be tackled separately
- Estimated effort: 4-8 hours for core integration (tasks 1-4)
- Additional 2-4 hours for polish and testing (tasks 5-8)
```

What is going on? Claude left me homework? I was also baffled by the hourly
estimates: Are these Claude hours or my hours? In the hindsight, the estimate
was surprisingly accurate. It took me about 1.5 days to make this code do the
first test run that made the harness exchange UDP packets with the TFTP server.

Then I looked at `harness.py`, which was supposed to be "complete and
production-ready". Guess what? The main loop was left as a TODO!

```python
        # TODO: Implement actual TFTP operation execution
        # This would involve:
        # - Querying Apalache for the transition details
        # - Sending commands to the TFTP client in Docker
        # - Collecting UDP packet responses
        # - Parsing the responses
```

The overall structure was there, but the most important pieces were left as
TODOs. Fine. It did the tedious part at least. So I started to chat with Claude
again to implement the missing pieces. If you look at the commit history, you
will see plenty of spaghetti code generated by Claude. In the end, it became a
bit better after my guidance, but I had to rewrite it at some point.

Even though I am making jokes about LLMs here, I must say that Claude really
helped me to debug the Docker setup and produce the python code for
communicating over UDP in modern Python. I could easily lose a couple of days
there.

Of course, the exploration logic was totally broken. After all, there is not
much for LLMs to learn from. We are doing something new here!

**1.5 days later.** Something was working, but even the happy path was not
there. So I had to do the baby steps with Claude. Here are just a few examples
from my Copilot chat:

> Let's implement sending the RRQ packet over the wire.

> ...

> Now I am receiving a response like below. This is good! What I want you to
> do next. Decode the response and construct the expected packet for the TLA+
> specification. Save this as the expectation that we will use in the next step.

> ...

> You should not construct a TLA+ expression. Rather, convert the packet to an
> ITF value using itf-py.

> ...

> Can you implement this case for receiving OACK from the server and sending ACK
> by the client to the server.

**2 more days later.** I had the happy path working. At this point, I was tired
of reading the harness logs. So I needed some form of visualization for each
run. Obviously, I wanted to have the same kind of Mermaid diagrams as before.

So I asked Claude to generate a script that would reconstruct the sequence
diagram from the harness logs. Well, it took me longer than expected. At some
point, Claude was producing quite convoluted log parsers with regular
expressions and python loops. Of course, it needs a human to define a simple log
format instead.

Below is an example of such a test run, visualized from the log by the generated
script in Mermaid:

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/tftp-happy.svg"
    alt="Trace visualization of the testing run">
</picture>

If you look at the above diagram carefully, you will notice that server responses
come in two flavors:

 1. The dashed arrows indicate that the client has received the UDP packet from
    the UDP socket.

 1. The solid arrows indicate that the UDP packet was successfully replayed
    with the TLA<sup>+</sup> specification.

## 8. Debugging the TLA<sup>+</sup> specification with the implementation

At that point, the tests started to produce actual interactions between the
TLA<sup>+</sup> specification (as solved by Apalache and Z3) and the real TFTP
server. This brought a lot of surprises! I am going to present some of them
below.

In this debugging session, I am keeping the scorecard of how many times the
TLA<sup>+</sup> specification was wrong versus how many times the implementation
(tftp-hpa) was wrong. The scorecard at this point looks like this:

| Spec bugs     | Implementation bugs     |
|---------------|-------------------------|
| 0             | 0                       |

Actually, tftp-hpa is a quite mature implementation, so I was not expecting any
bugs there. Keep reading to see what I found.

### 8.1. Sending errors on read request

The first surprise came from my misunderstanding of how exactly TFTP is supposed
to reply to a malformed read request (RRQ). Since a client sends RRQ to the
control port 69 of the server, I thought that the server would reply with an
error packet (ERROR) from the port 69, instead of introducing a new ephemeral
port.

This is what [RFC 2347][] says about option negotiation:

> ...the server should simply omit the option from the OACK, respond with an
> alternate value, or send an ERROR packet, with error code 8, to terminate the
> transfer.

No explanation about the port from which the ERROR packet is sent. Well, my
understanding was wrong. The server always allocates a new ephemeral port for
sending the ERROR packet. This kind of makes sense, as the implementation simply
forks on a new request. One score to the implementation:

| Spec bugs     | Implementation bugs     |
|---------------|-------------------------|
| 1             | 0                       |

{% include tip.html content="Actually, as I found later, the spec was not
always wrong, as the busybox implementation always uses port 69!"
%}

### 8.2. The server may send duplicate packets

Well, I knew that, but was lazy to write an action in the specification that would
handle duplicate packets. So the server retransmitted a DATA packet, which produced
a deviation in the TLA<sup>+</sup> specification. Another score to the
implementation:

| Spec bugs     | Implementation bugs     |
|---------------|-------------------------|
| 2             | 0                       |

Formally speaking, this action does not affect protocol safety, so it is
tempting to simply skip duplicates. However, in conformance testing, we have to
handle all possible actions of the implementation, even if they produce stuttering
steps in the theory of TLA<sup>+</sup>.

### 8.3. Input-output conformance does not work with UDP!

The next issue was quite interesting. When I read the papers on input-output
conformance testing from the 1990s, there was always an assumption that the
system under test (SUT) is input-enabled. This means that the SUT can always
accept any input at any time and respond to it, possibly, with an error message.
This assumption makes sense for synchronous systems (such as vending machines?),
where the tester can wait for the SUT to be ready to accept the input.

However, TFTP is not like that at all. The client may send an ERROR packet at
any point in time, and the server does not have to reply to it! This is exactly
a deviating test run I saw produced by the harness.

So instead of waiting for a reply from the server on each client action, the
test harness has to optimistically send the next UDP packet and then retrieve
the UDP packets from the server (remember that they live in Docker!).

This is where Claude was useful again. It helped me to collect the UDP packets
on the Docker client. Before taking the next step, the harness would retrieve
the buffered UDP packets from the Docker clients and replay these packets in the
TLA<sup>+</sup> specification, in arbitrary order.

This makes our testing approach a bit more sensitive to the timing of extracting
the buffered UDP packets, but it worked for TFTP.

| Spec bugs     | Implementation bugs     |
|---------------|-------------------------|
| 3             | 0                       |

### 8.4. The server recycles an ephemeral port on ERROR

Another interesting deviation happened when the server recycled an ephemeral
port. [RFC 1350][] explains how the server allocates ephemeral ports:

> In order to create a connection, each end of the connection chooses a TID for
> itself, to be used for the duration of that connection. The TID's chosen for a
> connection should be randomly chosen, so that the probability that the same
> number is chosen twice in immediate succession is very low.”

Well, in our test run, the event of low probability happened:

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/tftp-fix5.svg"
    alt="Recycling ephemeral ports on error">
</picture>

Actually, this theme of reusing the same ephemeral port happened multiple times
in the following debugging iterations. It is probably the most problematic
aspect of the protocol, as there is no notion of a session in TFTP. Another
score to the implementation:

| Spec bugs     | Implementation bugs     |
|---------------|-------------------------|
| 4             | 0                       |

### 8.5. The server recycles an ephemeral port on success

Guess what? A very similar thing happened on a successful file transfer as well.
Here is a pruned version of the trace that shows this behavior (the initial
sequence of RRQ-OACK-DATA-ACK is omitted for brevity):

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/tftp-fix6.svg"
    alt="Recycling ephemeral ports on success">
</picture>

This behavior seems to be consistent with [Section 6 of RFC 1350][], though it
seems to be ambiguous to me. Anyway, another score to the implementation:

| Spec bugs     | Implementation bugs     |
|---------------|-------------------------|
| 5             | 0                       |

### 8.6. Mixing the protocol versions

TFTP essentially has two versions: the original version defined in RFC 1350 and
the extended version with option negotiation defined in RFC 2347. In combination
with packet duplication, this produced a very interesting deviation. I've not
saved the full trace, but here is what happened. The server processes an RRQ
with options and sends an OACK, as per RFC 2347. After that, the TLA<sup>+</sup>
specification of the server receives an earlier RRQ without options and sends a
DATA packet in response, as per RFC 1350. This corrupts the internal state of
the server in the specification.

Obviously, this is caused by non-determinism in the TLA<sup>+</sup>
specification, which allows the protocol to behave according to both protocol
versions at the same time. I had to fix the specification by disallowing the
server to behave according to RFC 1350, when it receives an RRQ with options.
One score to the implementation:

| Spec bugs     | Implementation bugs     |
|---------------|-------------------------|
| 6             | 0                       |

### 8.7. More deviations on the specification side

At some point, I got tired of collecting the precise deviations. They still can
be recovered from the commit log though. Here are some of the further deviations
on the specification side that I fixed:

 - The client must send `tsize = 0` in RRQ.

 - The server should send default timeout if it's not specified in the options.

 - The server may send invalid (e.g., outdated) packets.

 - My understanding of TFTP timeouts was wrong. I thought that a timeout was
 meant to closes a transfer session. Instead, timeouts in TFTP are just
 triggering packet retransmissions. The number of retries is not specified in
 the RFCs. In practice, tftp-hpa seems to retry 5 times before giving up.

 - The server specification should store transfers for  triplets `(clientIP,
 clientPort, serverPort)` instead of pairs `(clientIP, clientPort)`.

In the end, the implementation scored another 7 points, before tests started to
work.

| Spec bugs     | Implementation bugs     |
|---------------|-------------------------|
| 13            | 0                       |
 

In the end, it looks like my TLA<sup>+</sup> specification was a bit sloppy, in
comparison to the mature implementation of `tftp-hpa`. I have not designed this
protocol and did not give much thought to it. Obviously, the engineers have
spent much more time about its behavior.

## 9. Testing against adversarial behavior

At some point I thought: My clients are too well-behaved! They never lose,
duplicate, or reorder packets. What if they start to misbehave within the
protocol boundaries? Would I be able to find bugs in the implementation? Yes, I
did. Keep reading.

Hence, I have added one more action that simply lets a client retransmit a
previously sent packet in `Next`:

{% github_embed
  https://raw.githubusercontent.com/konnov/tftp-symbolic-testing/refs/heads/main/spec/tftp.tla
  tlaplus 691-692
 %}

Below is the action `ClientSendDup`. It does not change the specification state
at all. However, it produces an action that retransmits a packet in the harness:

{% github_embed
  https://raw.githubusercontent.com/konnov/tftp-symbolic-testing/refs/heads/main/spec/tftp.tla
  tlaplus 642-649
 %}

You can find the complete specification [here][final-spec].

**Protocol deviation.** It mostly worked as expected. However, a few traces were
reporting deviations. Here is one of them. It's pretty long. Look for an
explanation below.

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/tftp-malformed-ack.svg"
    alt="The implementation diverging from the specification">
</picture>

The last UDP packet is an acknowledgment for block 1 from the server. If
you think about the protocol, the server should never send an ACK in the
sessions associated with read requests (RRQ). ACK packets are only sent by the
clients.  Yet, this is what was happening. To double check this, I've asked
Claude to capture the traffic in pcap files in the Docker containers. Indeed,
Wireshark was showing the ACK packet from the server. Moreover, the packet was
malformed. It looked like the option acknowledgment (OACK) packet, but had the
first bytes of an ACK packet. Sounds like memory corruption!

Here is the core sequence of events that produced this behavior (a few details
removed):

 1. The client sends `RRQ("file1", blksize=NN)` to the server (172.20.0.10:69).
 
 1. The server sends a few OACK packets to the client.
 
 1. The client erroneously sends `ACK(1)` to the server, which is a duplicate
 packet from an earlier transfer. It could be simply a delayed packet though.
 
 1. The server responds with `ACK(1)` of length 64, which is basically the
 `OACK` packet with the first 4 bytes coming from `ACK(1)`.

**Investigation.** Luckily, the source code is readily available. I've looked
into the function `tftp_sendfile` of `tftp-hpa` that handles read requests.
Indeed, the option negotiation loop receives the option acknowledgment packet
`OACK` and waits for an `ACK` from the client. There are two cases:

 - When it receives an `ACK` for block 0, it breaks out of the loop and continues with sending data blocks. **This is the happy path.**

 - When it receives an acknowledgment for a block other than 0, block, it simply
 continues the loop, retransmitting `OACK`. The issue is that **the code uses
 the same buffer** for sending `OACK` and receiving `ACK` packets via different
 pointers! Hence, it later sends an `OACK` packet that is corrupted with the
 contents of the `ACK` packet. **I don't think I would have found this by code
 review!**
 
Just for fun, I checked it with Claude. It could not identify this issue. The
trick is that the same buffer is pointed to by two different pointers, so Claude
is not clever enough to track this aliasing. When I explained the issue to
Claude, it was ecstatic: You have found a critical!

I've continued looking for the blast radius of this bug. Even though it somewhat
of memory corruption, it cannot crash the server, as the code is still writing
to the same buffer, allocated by the server itself. All it can do is to produce
malformed packets. Hence, it could probably crash a sloppy client, but would not
do much harm to a well-behaved client and itself. Moreover, if a client crashes
in such a case, anybody else on the network could have sent the malformed ACK as
well.

So this is a bug (from the specification p.o.v.), but it does not result in a
vulnerability. In any case, it was a deviation from the protocol specification.
Finally, one point to the specification!

| Spec bugs     | Implementation bugs     |
|---------------|-------------------------|
| 13            | 1                       |

**Contacting the author.** To be on the safe side, before writing this blog
post, I've contacted the author of tftp-hpa. As I expected, he also replied that
TFTP is an unencrypted unauthenticated protocol, so we should not expect much
security there.

## 10. The specification as a differential testing oracle

After finding the above implementation bug, I have decided to test other TFTP
implementations as well. This is where Claude was super useful again. I just
asked it to generate Dockerfiles for other implementations, which it did
quickly. It happened that a similar issue existed in another implementation. I
could not figure out the root cause in the source code of that other
implementation, as it is a bit harder to read than `tftp-hpa`. Hence, not giving
the details here.

Except this second deviation, the other implementations worked fine. Overall,
the specification scored another point:

| Spec bugs     | Implementation bugs     |
|---------------|-------------------------|
| 13            | 2                       |

What I find really interesting here. Whenever I talk to engineers about formal
specifications, they tell me that they would like to do **differential testing**
instead of writing specifications. Meaning that they would like to compare the
behavior of one implementation against another implementation. However,
differential testing is not magic. It requires test inputs to compare the
implementations. Hence, **if the test suite is missing adversarial test cases,
both implementations may pass the tests**, even though they are both wrong.

What we did here with the TLA<sup>+</sup> specification is something more than
just differential testing. First, we have debugged the specification against
`tftp-hpa`, so we have extracted its expected behavior into a relatively small
and precise formal specification. Second, we have used this specification to
produce the tests for another implementation!

## 10. Prior Work

In this section, I've collected the previous work on model-based testing and
trace validation with TLA<sup>+</sup>:

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

## 11. Conclusions

This was a lot of text! Thank you for reading it till the end. It may look like
this project took me eternity to complete. In reality, it took me about two
weeks of part-time work to do it from the start to the end. I could probably do
some parts of it faster, if I did not rely too much on Claude for generating the
test harness. To be fair, I also had to add a few features to the new Apalache
API, as I was still experimenting with it.

What I find interesting in the approach outlined here is that it presents a
(relatively) lightweight way to testing real-world protocols. Thinking of
fuzzing in this context, I don't think a standard fuzzer would have found the
above deviations in TFTP. Indeed, the implementation was not crashing. Nor it
was accessing memory out of bounds. It was just producing malformed packets
occasionally. To detect this, we needed a test oracle that would tell us,
whether a deviation happened. Writing such an oracle manually would be tedious and
error-prone. Instead, we have used a formal specification as a precise and
unambiguous oracle.



[Igor Konnov]: https://konnov.phd
[Thomas Pani]: https://blltprf.xyz
[Lean]: https://lean-lang.org/
[TLC]: https://github.com/tlaplus/tlaplus
[Apalache]: https://apalache-mc.org
[Quint]: https://github.com/informalsystems/quint
[TLAPS]: https://proofs.tlapl.us/
[TLA<sup>+</sup>]: https://tlapl.us/
[TFTP]: https://en.wikipedia.org/wiki/Trivial_File_Transfer_Protocol
[RFC 1350]: https://www.rfc-editor.org/rfc/rfc1350
[RFC 2347]: https://www.rfc-editor.org/rfc/rfc2347
[RFC 2348]: https://www.rfc-editor.org/rfc/rfc2348
[RFC 2349]: https://www.rfc-editor.org/rfc/rfc2349
[Z3]: https://github.com/Z3Prover/z3
[GNU parallel]: https://www.gnu.org/software/parallel/
[Jetty]: https://jetty.org/
[Jackson]: https://github.com/FasterXML/jackson
[JSON-RPC]: https://www.jsonrpc.org/
[curl]: https://curl.se/
[Apalache JSON-RPC]: https://github.com/apalache-mc/apalache/tree/main/json-rpc
[ITF]: https://apalache-mc.org/docs/adr/015adr-trace.html
[itf-py]: https://github.com/konnov/itf-py/
[apalache-rpc-client]: https://github.com/konnov/apalache-rpc-client/
[small-scope]: {% link _posts/2025-12-02-small-scope.md %}
[N25]: https://www.youtube.com/watch?v=DO8MvouV29M
[K24b]: https://www.youtube.com/watch?v=NZmON-XmrkI
[MZ19]: https://www.mcmil.net/pubs/SIGCOMM19.pdf
[Giuliano Losa]: https://www.losa.fr/
[tftp-hpa]: https://kernel.googlesource.com/pub/scm/network/tftp/tftp-hpa/
[atftpd]: https://github.com/madmartin/atftp
[dnsmasq]: http://www.thekelleys.org.uk/dnsmasq/doc.html
[rs-tftpd]: https://github.com/altugbakan/rs-tftpd
[gotfpd]: https://github.com/pin/tftp
[testing repo]: https://github.com/konnov/tftp-symbolic-testing
[initial commit]: https://github.com/konnov/tftp-symbolic-testing/tree/6fb00d1878b7e37a629868ac25b853d95b16cbdc
[final-spec]: https://github.com/konnov/tftp-symbolic-testing/tree/main/spec
[types-prompt]: https://github.com/apalache-mc/apalache/blob/main/prompts/type-annotation-assistant.md
[Mermaid]: https://www.mermaidchart.com/
[Section 6 of RFC 1350]: https://www.rfc-editor.org/rfc/rfc1350#section-6