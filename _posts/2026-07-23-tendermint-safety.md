---
layout: post
title: "Proving safety of Tendermint consensus with Apalache and AI"
date: 2026-07-23
author: Igor Konnov
categories: distributed consensus proving
tlaplus: true
lean: false
math: true
shell: false
python: true
hidden: false
feed: true
---

*This text is artisanally typed using Das Keyboard, with occasional suggestions
by Copilot (most of them ignored anyways). The figures are generated with
ChatGPT 5.5.*

If you read my [previous blog post][ben-or-proofs-blogpost], you know that I was
impressed by the ability of the frontier AI tools to write complete proofs of
safety for the Ben-Or's consensus using Lean 4 and TLAPS. Not everything went
smoothly. Also, I gave the tools an inductive invariant in TLA<sup>+</sup> as a
starting point. This inductive invariant was almost correct, except that it
needed a fix in one of the lemmas for the general case of $T \ge 1$.

As in the [previous blog post][ben-or-proofs-blogpost], here I used Claude Code
Opus 4.8 and Codex GPT 5.5. I refer to them as "C1" and "C2", without disclosing
which is which. I have not tried Fable and GPT 5.6 in this case study.

**Next stop: Tendermint**.
Ben-Or published [his paper][ben-or] in 1983. It does not look like this
algorithm has a modern implementation, though implementations of randomized BFT
consensus protocols exist. Hence, I thought of trying the same approach with a
modern BFT consensus protocol that runs in the wild.
[Tendermint][tendermint-paper] is the most obvious candidate for this
case study. It has a [formal specification][tendermint-acc-spec] in
TLA<sup>+</sup>, which I wrote with Zarko Milosevic in 2020, back at Informal
Systems. This specification even has lemmas for an [inductive
invariant][tendermint-acc-inductive] in TLA<sup>+</sup>.

This blog post completes my Gestalt with the Tendermint specification. Back in
2019-2020, I checked the specification for small parameter values such as $N=4$,
$T = 1$, and $F \in \{0, 1\}$. Since the Cosmos blockchain (powered by
Tendermint) was running hundreds of validators, Ethan Buchman (co-founder of
Cosmos and CEO of Informal Systems) was asking me, whether we could transfer the
results to $N$ in the range of hundreds. Back then, it meant either doing
further research on [threshold automata][], or writing a proof of safety in
TLAPS. Again, this did not fit the company's business priorities. Now, this is
done in just a week of work with AI tools.

Did I just ask Claude Code or Codex to write a proof of safety for Tendermint?
Well, there was an obstacle to that. In 2022, [Rodrigo Otoni][] found that
[Apalache][] was [reporting counterexamples to
inductiveness][tendermint-indinv-issue] for our invariant `TypedIndInv`, which
was supposed to be inductive. Since the inductiveness check was taking hours, it
was not included in the Github CI workflows, so we missed the moment, when it
stopped working. It's hard to tell what happened back then. The [Tendermint
implementation][tendermint-project] was going through upgrades, but then
repository was reverted at some point. Perhaps, the reverted specification was
not the latest one. Also, we fixed several soundness issues in Apalache since
2020.  Maybe, the invariant was not inductive in the first place.  Moreover, the
time effort for fixing the invariant was not clear, and fixing it was not the
business priority anymore.

In the following sections, I give a bit more details about the process of fixing
the inductive invariant and generating the proofs.

## 1. Repairing the inductive invariant

In any case, to write the proofs, I had to fix the inductive invariant first.  A
few years ago, fixing the inductive invariant meant the following:

 1. Run Apalache,

 1. stare at the counterexample,
 
 1. think about the consensus protocol and why the invariant was not strong
 enough,
 
 1. improve the invariant and repeat.

Obviously, the part of the process that included "staring at the counterexample"
was not automated at all.

This time, I decided to avoid the pain and feed examples from Apalache into C1,
in order to strengthen the invariant. This does not require any additional tool
support from Apalache. The tool can already generate example behaviors, not just
counterexamples to invariants. This is an often overlooked feature of Apalache.

As a first step, I was running Apalache to generate example states that satisfy
`TypedInvInv`. Then, I was asking C1, whether these states presented feasible
states that were reachable from the initial states as defined with `Init`. This way,
C1 added seven additional lemmas.

Once the states looked feasible, I started to produce counterexamples to
inductiveness of `TypedIndInv` with Apalache. C1 identified the key fix to the
problematic lemma by changing one of the thresholds and excluding nil values:

```diff
- \* if T + 1 processes precommit on the same value in a round,
- \* then in the future rounds there are less than 2T + 1 prevotes for another value
+ \* if 2T + 1 processes precommit on the same valid value in a round,
+ \* then in the future rounds there are less than 2T + 1 prevotes for another value.
PrecommitsLockValue ==
      \A r \in Rounds:
-         \A v \in ValidValues \union {NilValue}:
+         \A v \in ValidValues:
              \/ LET Precommits == {m \in msgsPrecommit[r]: m.id = v}
                 IN
-                    Cardinality(Senders(Precommits)) < THRESHOLD1
+                    Cardinality(Senders(Precommits)) < THRESHOLD2
              \/ \A fr \in { rr \in Rounds: rr > r }:  \* future rounds
-                    \A w \in (ValuesOrNil) \ {v}:
+                    \A w \in (ValidValues \ {v}):
                         LET Prevotes == {m \in msgsPrevote[fr]: m.id = w}
                         IN
                             Cardinality(Senders(Prevotes)) < THRESHOLD2
```

After the key fix, C1 added three more lemmas to strengthen the invariant, and
then Apalache was not reporting any counterexamples anymore. The whole process
of fixing the inductive invariant took about **2 calendar days**.

**Details**. Actually, before fixing the inductive invariant, I decreased the
scope of the specification to the original Tendermint. The [existing TLA+
specification][tendermint-acc-spec] has additional features such as evidence
collection and the accountability invariant. I did not want to run into the
rabbit hole of reasoning about the evidence sets. Hence, the file
[tendermint-single-indinv.tla][tendermint-single-indinv] contains the
specification of the original Tendermint without the additional features, as
well as the fixed inductive invariant. The TLA<sup>+</sup> specification is
generated from two specifications in a Python DSL: [tendermint-single.py][] and
[tendermint-single-indinv.py][tendermint-single-indinv.py]. This is not really
relevant for this story though, as the AI tools work well with TLA<sup>+</sup>
as well as with the Python DSL. Moreover, once the invariant was fixed, the AI
tools effortlessly transferred the fix to the original TLA<sup>+</sup>
specification.

## 2. Generating TLAPS proofs

Once the inductive invariant was fixed, I asked C1 to bootstrap the proofs of
inductiveness of `TypedIndInv`. After that, I was switching between C1 and C2,
when they were reaching the 5h limits.  In contrast to the Ben-Or's consensus,
the proof process for Tendermint was relatively uneventful. Perhaps, C1 and C2
know way too much about Tendermint.  The only interesting assumption was that
the proof required exactly $N = 3 \cdot T + 1$. In total, it took me about **5
calendar days** to have working proofs.  You can find the complete proofs in
[tendermint-single-indinv-proofs.tla][tendermint-single-indinv-proofs]. **The
proofs are about 4.6 KLOC**. One can argue that the inductive invariant
constitutes the core of the proof. The definitions related to **the inductive
invariant** are **about 400 LOC**.

As always, it was fun to read Claude's status updates on the proof progress:

> I've verified this wall exhaustively enough to characterize it precisely. Let
> me stop grinding and give you a straight assessment rather than more thrashing.

> The orientation normalization dissolved the congruence wall.


The statements of the main theorems mirror the technique of inductive
invariants:

{% github_embed
  https://raw.githubusercontent.com/konnov/apalache-examples/refs/heads/main/tendermint/tendermint_single_indinv_proofs.tla
  tlaplus 199-200
 %}

{% github_embed
  https://raw.githubusercontent.com/konnov/apalache-examples/refs/heads/main/tendermint/tendermint_single_indinv_proofs.tla
  tlaplus 4603-4605
 %}

{% github_embed
  https://raw.githubusercontent.com/konnov/apalache-examples/refs/heads/main/tendermint/tendermint_single_indinv_proofs.tla
  tlaplus 4694-4695
 %}

The assumptions section is where we should be really careful. It easy to
constrain the problem to a much simpler one. For example, in one of my
experiments, the LLMs constrained the problem to $N = 4 \land T = 1$, which
would make the proofs as strong as the model checking results by Apalache.
Obviously, we want to prove the theorems for the general case.

These are our assumptions:

{% github_embed
  https://raw.githubusercontent.com/konnov/apalache-examples/refs/heads/main/tendermint/tendermint_single_indinv_proofs.tla
  tlaplus 38-93
 %}

As you can see, $N > 3 \cdot T$ is redundant in the presence of $N = 3 \cdot T +
1$. The assumption of $N = 3 \cdot T + 1$ is consistent with the
[paper][tendermint-paper]. The case of $N > 3 \cdot T + 1$ has a simple
counterexample to agreement, and Apalache finds such a counterexample. If we
want to make it work for $N > 3 \cdot T + 1$, we have to change `THRESHOLD2`
from $2 \cdot T + 1$ to $N - T$.

**Stabilizing the proofs**.
Surprisingly, I found that the generated proofs were going through on the
virtual machines, where I run C1 and C2, but they were failing on my host
machine. Surprisingly, it was taking SMT longer on my host machine to prove
certain goals than on the virtual machines. I asked C1 and C2 to stabilize the
proofs.

## 3. Conclusions

I believe we only start to see what is possible at the intersection of
TLA<sup>+</sup> and AI tools. Obviously, the AI tools help with usability a lot.
Running TLA<sup>+</sup> tools and writing TLAPS proofs is way easier now.

When it comes to Tendermint, the obvious next steps would be:

 1. Extend the specification and the proofs with multiple heights (blocks),

 1. Extend the specification and the proofs with timeouts and liveness properties.

If you are interested in specification and verification of consensus protocols
or other protocols, [contact me][contact].

## Want to talk?
 
<!-- References -->

[contact]: https://konnov.phd?pmf=20260427&utm_source=protocols_made_fun&utm_medium=referral&utm_campaign=pmf_site
[Igor Konnov]: https://konnov.phd?utm_source=protocols_made_fun&utm_medium=referral&utm_campaign=pmf_site
[Rodrigo Otoni]: https://rodrigo7491.github.io/
[tla2026]: https://conf.tlapl.us/2026-etaps/
[Apalache JSON-RPC]: https://github.com/apalache-mc/apalache/tree/main/json-rpc
[Apalache]: https://apalache-mc.org
[ben-or-blogpost]: {% link _posts/2024-11-03-ben-or.md %}
[ben-or-proofs-blogpost]: {% link _posts/2026-06-26-proofs-are-closer.md %}
[ben-or-inductive]: {% link _posts/2024-11-03-ben-or.md#5.-checking-unbounded-executions-via-an-inductive-invariant %}
[zookeeper-testing]: {% link _posts/2026-05-26-zookeeper-testing.md %}
[ben_or.py]: https://github.com/wunderspec/wunderspec/blob/main/examples/ben_or.py
[tftp-testing]: {% link _posts/2025-12-15-tftp-symbolic-testing.md %}
[LI]: https://www.linkedin.com/in/igor-konnov-at/
[Apalache]: https://apalache-mc.org
[Ben-or-defs]: https://github.com/konnov/leanda/blob/main/Ben-Or/BenOr/Defs.lean
[Ben-or-inductive.tla]: https://github.com/konnov/apalache-examples/blob/main/ben-or83/Ben_or83_inductive.tla
[Ben-or-lean-proofs]: https://github.com/konnov/leanda/tree/main/Ben-Or
[Ben-or-tla-proofs]: https://github.com/konnov/apalache-examples/blob/main/ben-or83/Ben_or83_proofs.tla
[ben-or]: https://dl.acm.org/doi/10.1145/800221.806707
[tendermint-acc-spec]: https://github.com/cometbft/cometbft/blob/6ba279560e3aa6a1eb0739c6af9bc3b8bbb24563/spec/light-client/accountability/TendermintAcc_004_draft.tla
[tendermint-acc-inductive]: https://github.com/cometbft/cometbft/blob/6ba279560e3aa6a1eb0739c6af9bc3b8bbb24563/spec/light-client/accountability/TendermintAccInv_004_draft.tla
[tendermint-paper]: https://arxiv.org/abs/1807.04938
[tendermint-indinv-issue]: https://github.com/apalache-mc/apalache/issues/2067
[tendermint-project]: https://github.com/tendermint/tendermint
[tendermint-single-indinv]: https://github.com/konnov/apalache-examples/blob/main/tendermint/tendermint_single_indinv.tla
[tendermint-single-indinv-proofs]: https://github.com/konnov/apalache-examples/blob/main/tendermint/tendermint_single_indinv_proofs.tla
[tendermint-single.py]: https://github.com/wunderspec/wunderspec/blob/main/examples/tendermint_single.py
[tendermint-single-indinv.py]: https://github.com/wunderspec/wunderspec/blob/main/examples/tendermint_single_indinv.py
[cav2026]: https://conferences.i-cav.org/2026/accepted/
[threshold automata]: https://lmcs.episciences.org/10824