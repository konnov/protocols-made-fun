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

To implement this approach to testing with Apalache, we would have to find a way
for Apalache and the test harness to communicate. My experience with development
of Apalache shows that **fixing exploration strategies inside the model checker
is not a good idea**. People always want to tweak them a bit for their purposes.
Given this observation, [Thomas Pani][] and I have decided to try to implement a
simple JSON-RPC API for Apalache that would allow external tools to drive the
symbolic execution of TLA<sup>+</sup> specifications.

## 4. The new JSON-RPC API of Apalache

[Thomas][Thomas Pani] and I wanted to have a lightweight API that we could use
from any programming language without writing too much boilerplate code. At this
point, every engineer would whisper: hey, you need gRPC, I've got some. Well, we
tried gRPC in the integration of [Apalache][] with [Quint][]. Too much hassle
for my taste.

So we have decided to go with [JSON-RPC][], which is a very simple protocol that
works over HTTP/HTTPS. Implementing a JSON-RPC server is quite straightforward.
Since Apalache is written in Scala, which is JVM-compatible, we can use the
well-known and battle-tested libraries. Perhaps, a bit unexpectedly for a Scala
project, I've decided to implement this server with [Jetty][] and [Jackson][]
for JSON serialization. (The reason is that we have already burnt ourselves with
fancy but poorly supported libraries in Scala.) The resulting server is
lightweight and fast. Moreover, it can be tested with command-line tools like
[curl][].

The state-chart diagram of the Apalache JSON-RPC server for a single session is
shown below.

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/apalache-api.svg" alt="Apalache JSON-RPC API">
</picture>

To see a detailed description of this API, check [Apalache JSON-RPC][].
Just to give you a taste, here is how you can create a new Apalache session with
a TLA<sup>+</sup> specification:

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

Having the specification loaded, we load the predicate `Init` into the SMT
context, which is encoded as transition 0:

```shell
$ curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"assumeTransition","params":{"sessionId":"1",
       "transitionId":0,"checkEnabled":true},"id":2}'
```

Assuming that the previous called returned `ENABLED`, we switch to the next
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

Since invariant `Inv3` is violated by the initial state, the server will return
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
format for TLA<sup>+</sup> traces.

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

The Wikipedia page on [TFTP][] gives a good overview of the protocol. In short,
TFTP is a simple protocol to transfer files over UDP. It supports reading and
writing files from a remote server. The protocol is simple enough to be
specified in TLA<sup>+</sup> without too much effort, yet it has enough
complexity to make the testing interesting. Actually, I've only specified
reading requests (RRQ) and no writing requests (WRQ) to keep the scope
manageable.

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

The cool thing about TFTP is that there are multiple open-source implementations
of TFTP clients and servers in different programming languages. Here are some
of them that ChatGPT helped me to find:

 - [tftp-hpa][] is the canonical implementation of TFTP for Linux systems in C.
 
 - [atftpd][] is advanced TFTP, which is intended for fast boot in large
 clusters, also in C.
 
 - [dnsmasq][] is a lightweight DNS and DHCP server that also includes a TFTP
 server, in C.
 
 - [rs-tftpd][] (Rust) is an implementation of a TFTP server in Rust (because
 there must be a library in Rust).
 
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
 constructors for these data structures. Since I am using Apalachec, it requires
 type definitions. Luckily, these days, I just write the type definitions in
 comments and let Claude generate the auxilliary operators such as constructors
 and accessors.
 
 - `util.tla` defines common utility definitions such as `Min`, `Max`, and
 options conversions.
 
Finally, `MC2_tftp.tla` defines a protocol instances of two clients and one
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

As I always do, I also specified "falsy invariants" to produce interesting
examples. For example, using the invariant `RecvThreeDataBlocksEx` below, I can
easily produce a trace where a client receives three data blocks from the
server.

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

Since Apalache emits traces in the [ITF format][ITF], it was easy for me to
convince Claude to produce a Python script that would convert ITF traces to
human-readable state charts in Mermaid. Here is just an example of such a trace
produced by Apalache when checking the invariant `RecvThreeDataBlocksEx` in
Mermaid:

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

This is how it looks like when rendered by Mermaid:

<picture>
  <img class="responsive-img"
    src="{{ site.baseurl }}/img/tftp3.svg"
    alt="Visualized trace of TFTP client receiving three data blocks">
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