---
layout: post
title: "Small scope hypothesis revisited"
date: 2025-12-02
categories: tlaplus
tlaplus: true
math: true
shell: true
---

**Author:** [Igor Konnov][]

**Tags:** specification tlaplus tlc

A couple of weeks ago, I gave a talk at the internal Nvidia FM Week 2025. Many
thanks to [Markus Kuppe][] for the organization and invitation! I am going to
write a longer blog post about interactive spec conformance testing with
Apalache later. Today, I want to talk a bit about the question posed by Markus
(to find the question, continue reading).

Let's talk about the small scope hypothesis. As formulated by Jackson in the
[technical report][TR-735] (1997), this hypothesis reads as follows:

<p class="highlight-question"><strong><em>
    "...most errors can be demonstrated by counterexamples within a small scope."
</em></strong></p>

As you will see below, my example fits into this hypothesis quite well. However,
having spoken to many engineers over the years, I believe that there is a
mismatch between what engineers understand by "small scope" and what
verification engineers understand by "small scope".

In this blog post, I've decided to try a **new format**. Since everyone is using
LLMs nowadays, I will follow the protocol. I will present the example and the
problem of finding a small scope. Then, it is your turn to decide how this blog
post should continue. If someone gives me an interesting example or insight in a
[comment][leave-comment], I will update this blog post accordingly.

## 1. Example 1: Buggy circular buffer

### 1.1. The specification

I started the talk with a TLA<sup>+</sup> specification of a **buggy** circular
buffer. You can find the full specification, the model checking models, and the
TLC configuration files [here][cyclic-tla]. The specification looks as follows:

{% github_embed
  https://raw.githubusercontent.com/konnov/cyclic-buffer-challenge/refs/heads/main/tla/BuggyCircularBuffer.tla
  tlaplus 1-72
 %}

Since I wanted to experiment with different buffer sizes and potential buffer
elements, I have introduced two parameters in the specification:

 - `BUFFER_SIZE` is the size of the cyclic buffer, and
 - `BUFFER_ELEMS` is the set of possible buffer elements.

Now, my previous experience with introducing TLA<sup>+</sup> to engineers
suggests that there are two ways to set these parameters:

 1. **The Engineer's way:** Set the parameters to relatively small yet
 reasonable values. For example, `BUFFER_SIZE = 10` and `BUFFER_ELEMS = 0..255`.
 These are not the minimal possible values, but they kind of make sense: The
 buffer should hold up to 10 bytes. Obviously, `BUFFER_ELEMS` are
 set to the minimal possible type in their programming language of choice, e.g.,
 `char` in C, or `u8` in Rust.

 1. **The Verification Engineer's way:** Start with the smallest possible values
 of the parameters, e.g., `BUFFER_SIZE = 2` and `BUFFER_ELEMS = {0, 1}`. The
 idea is to check the specification in the smallest possible scope first. If there
 are no bugs found, increase the parameters gradually until you reach the
 reasonable values.

### 1.2. Checking the specification Engineer's way

To check the specification the Engineer's way, I have created the
TLA<sup>+</sup> model [MC10u8_BuggyCircularBuffer.tla][] with `BUFFER_SIZE = 10`
and `BUFFER_ELEMS = 0..255`. For technical reasons, we also need the TLC config
file [MC.cfg][]. Follow the links to see the details.  Further, I've run TLC on
this model to check the invariant `SafeInv`:

```shell
$ java -cp tla2tools.jar "-XX:+UseParallelGC" tlc2.TLC \
  -config MC.cfg MC10u8_BuggyCircularBuffer.tla
```

I wanted to see how far TLC could go, so I gave it a machine with 128 GB of RAM
and 32 cores. TLC has explored around 3 billion states in about 40 minutes.
After consuming 400 GB of disk space, it has run out of disk space and
terminated. No bug was found. Is this surprising? Not really. In this
configuration, TLC has to enumerate $(2^8)^{10} * 10 * 10 * 10 \approx 2^{100}$
states.

Obviously, anyone who used TLC for some time would have asked the same question
as Markus did:

<p class="highlight-question"><strong><em>
  What about the small scope hypothesis? Can we use smaller parameters?
</em></strong></p>

The answer to this question is basically the second approach, which I called the
Verification Engineer's way.

{% include tip.html content="Apalache finds an invariant violation in 3
seconds, when running bounded model checking with the command `check`.
However, I do not want to distract us from the main point of this blog post."
%}

### 1.3. Checking the specification Verification Engineer's way

This time, we use the instance [MC2u1_BuggyCircularBuffer.tla][]
that has `BUFFER_SIZE = 2` and `BUFFER_ELEMS = {0, 1}`.
Let's run TLC on this instance to check the invariant `SafeInv`:

```shell
$ java -cp tla2tools.jar "-XX:+UseParallelGC" tlc2.TLC \
  -config MC.cfg MC2u1_BuggyCircularBuffer.tla
...
Error: Invariant SafeInv is violated.
...
10 states generated, 10 distinct states found, 5 states left on queue.
```

Yay! Just after visiting 10 states, TLC has found a violation of the invariant!

So if we pick the right small scope, exhaustive model checking with TLC finds
the bug quite fast. In this example, it is hard to find a small scope that would
not reveal the bug. Of course, when we know that the bug exists, it is easy to
experiment with different values of the parameters and find the bug.

### 1.4. Checking the specification randomly

Surprisingly, if we forget about exhaustive enumeration, TLC finds an
invariant violation for `BUFFER_SIZE = 10` and `BUFFER_ELEMS = 0..255` in less
than a second. To do this, we run TLC with the option `-simulate`, which simply
picks successor states at random:

```shell
$ java -cp tla2tools.jar "-XX:+UseParallelGC" tlc2.TLC \
  -simulate -config MC.cfg MC10u8_BuggyCircularBuffer.tla
...
Error: Invariant SafeInv is violated.
...
```

This effectiveness of randomized search is actually not a one-off thing.
The Quint simulator [find the bug][quint-simulation] in less than a second.
Similarly, the Rust property-based testing with [proptest][] finds the bug
almost immediately.

Interestingly, **we did not have to tune the scope to be as tiny as possible**,
as we did for exhaustive model checking. Maybe this is why some engineers want
to use property-based testing for every problem?

## 2. Thinking about the small scope hypothesis

In Example 1, we indeed found several assignments to `BUFFER_SIZE` and
`BUFFER_ELEMS` that revealed an invariant violation. Actually, this bug is so
simple that almost any assignment to the parameters would reveal it. We could
even set `BUFFER_SIZE = 1` and `BUFFER_ELEMS = {0}` to find the bug! If you want
to push it further, think, whether `BUFFER_ELEMS = {}` would allow us to find an
invariant violation.

In fact, if we go back to [Alloy][], the way Alloy restricts the scope is quite
different from what we did in Example 1. Alloy limits the number of elements of
each type in the specification. For example, if we had specified the circular
buffer in Alloy, we could restrict the search scope as follows:

 - All integers, including `BUFFER_SIZE` and buffer indices, have the bit width
 of 4.
 
 - The number of unique buffer elements is $2^8$.

As a result, Alloy would consider all possible values of `BUFFER_SIZE` from 0 to
15, all possible values of buffer elements from 0 to 255, as well as all
possible combinations of buffers of size up to 15. This is a much more flexible
way to restrict the search space.  In case of TLC, we did not have this
flexibility: We had to give concrete values to `BUFFER_SIZE` and `BUFFER_ELEMS`.

{% include tip.html content="Apalache has data generators, which are closer to
the Alloy scopes in spirit, though they work slightly different from Alloy."
%}

Hence, we have to distinguish between small scopes and small parameter
assignments in TLC. After thinking about this question a bit more, I've asked
myself:

<p class="highlight-question"><strong><em>
  Are there examples of specifications that have a small scope for a specific
  invariant violation, but it is hard to find concrete parameter assignments
  within this scope?
</em></strong></p>

Even though my intuition says "yes", there must be plenty of such examples, I
could not come up with with non-artificial examples immediately. On top of my
head, I can think of the following directions to look for such examples:

  - Examples from **abstract interpretation**. If we have non-trivial math with
  overflows and underflows, it might be hard to find concrete assignments that
  would trigger these overflows and underflows.
  
  - Examples from **graph theory**. For instance, [non-planar graphs][planar]
  must contain subgraphs that are subdivisions of $K_5$ or $K_{3,3}$ (see
  Kuratowski's theorem on [planar graphs][planar]). So if a bug shows up only in
  non-planar graphs, there must be a small scope that reveals the bug.  However,
  our concrete graph would have to contain a subdivision of $K_5$ or $K_{3,3}$,
  which is far from an arbitrary graph. Unfortunately, I do not know any
  concurrent or distributed algorithm that would have something to do with
  planar or non-planar graphs.

## 3. Your turn

It is your turn to decide how this blog post should continue. If someone gives
me an interesting example or insight in a [comment][leave-comment], I will
update this blog post accordingly.


<!-- references -->
  
[Igor Konnov]: https://konnov.phd
[Markus Kuppe]: https://github.com/lemmy
[TLC]: https://github.com/tlaplus/tlaplus
[cyclic-tla]: https://github.com/konnov/cyclic-buffer-challenge/tree/main/tla
[MC10u8_BuggyCircularBuffer.tla]: https://github.com/konnov/cyclic-buffer-challenge/blob/main/tla/MC10u8_BuggyCircularBuffer.tla
[MC2u1_BuggyCircularBuffer.tla]: https://github.com/konnov/cyclic-buffer-challenge/blob/main/tla/MC2u1_BuggyCircularBuffer.tla
[MC.cfg]: https://github.com/konnov/cyclic-buffer-challenge/blob/main/tla/MC.cfg
[Alloy]: https://alloytools.org/
[nitpick]: https://dl.acm.org/doi/abs/10.1145/226295.226322
[evaluating-ssh]: https://groups.csail.mit.edu/sdg/pubs/2002/SSH.pdf
[TR-735]: https://dspace.mit.edu/bitstream/handle/1721.1/149864/MIT-LCS-TR-735.pdf
[apalache-bmc]: https://github.com/konnov/cyclic-buffer-challenge/tree/main/tla#bounded-model-checking-with-apalache
[quint-simulation]: https://github.com/konnov/cyclic-buffer-challenge/tree/main/quint#randomized-simulation
[proptest]: https://github.com/konnov/cyclic-buffer-challenge/tree/main/rust/proptest
[planar]: https://en.wikipedia.org/wiki/Planar_graph
[happy to help]: {{ 'contact/' | relative_url }}
[leave-comment]: #end