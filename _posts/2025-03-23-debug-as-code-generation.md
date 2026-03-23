---
layout: post
title: "Specification debugging as code generation"
date: 2026-03-23
author: Igor Konnov
categories: testing model-checking
tlaplus: false
math: false
shell: false
python: false
hidden: false
feed: true
---

**Author:** [Igor Konnov][]

**Date:** March 23, 2026

This is an anecdote about another useful application of Codex and Claude Code in
the middle of a testing project. It is another example of using LLMs to make
distributed systems easier to test and debug, instead of generating piles of
slop.

## Context

I am currently developing a test harness for an implementation of distributed
consensus, cannot disclose the details yet. Think of the approach presented in
[TFTP Symbolic Testing][tftp-testing] but for a more complex distributed system.
It involves five state machines, each for a different subprotocol of the system.
The submachines are composed into a single machine. We generate the protocol
specifications and the test harness with Claude Code and Codex. This test
harness produces input events for the protocol implementation with [Apalache][]
and replays the output events from the implementation, checking that they
conform to the protocol specification with Apalache. Pretty cool. This is
**AI-assisted protocol extraction and testing**.

It took me a few days to bootstrap this project, designing the proper interfaces
and the harness architecture. After sheparding the AI tools for dozens of
iterations, I got a harness that communicates with the implementation. Whenever,
it surfaces a mismatch, the LLM looks into the source code, the specification,
and the test harness, and investigates the mismatch. When it identifies the root
cause and proposes a fix, I take a careful look at the proposed fix, and if it
looks good, I apply it. Sometimes, the LLM identifies a completely wrong root
cause. However, after a few iterations, we end up with the right root cause and
the right fix. This is a very efficient way to extract the protocol
specification from the actual implementation, and it is much faster than doing
it manually.

This specification-testing-refinement loop worked quite well for multiple
iterations. Sometimes, I could even leave this agentic loop running for several
hours unattended, though protocol extraction often requires human supervision.
At some point, however, the harness and the implementation started to produce a
sequence of events that was rejected by the specification, or, to be more
precise, by the model checker following the specification. Codex and Claude
tried to identify the root cause and fix it. They introduced multiple fixes, but
the mismatch persisted. I basically lost a whole day looking at the LLM outputs
and prompting them. At some point, I looked at the git log and realized that
**we were going in circles**. What was worse, every fix was introducing a
workaround and generally the harness started to degrade. So we went down the
rabbit hole of slop. In the rest of this post, I will just call both Claude and
Codex "the LLM", as I don't remember which one did what, and it doesn't matter
for the story.

At this point, I realized that the AI feedback loop stopped working, and the
human had to seriously intervene. The LLMs could describe what was happening, we
had a concrete state from the model checker, but a single transition that
**must have been enabled** in this state was not enabled. If you worked with
formal verification tools, you know that **this is the situation we all dread**.
It is a clear sign of **the specification being overconstrained**. The model
checker is doing its job, and it is correctly rejecting the transition. The
issue is that the specification requires an impossible combination somewhere,
like **x = 2 and x = 3**. In this case, the model checker cannot produce a
counterexample, or anything meaningful, because the constraints are
contradictory. (There is a line of research on UNSAT cores, but it's hard to
apply in practice in TLA<sup>+</sup>.)

If you wrote the specification yourself, you can usually stare at it and find
the combination of contradicting constraints. However, in this case, the
specification was written by the LLM! Of course, I looked at it. Things looked
fine. The LLM agreed with me that the transition should be enabled.

## Debug an overconstrained specification like a human would

The LLMs were stuck. So I decided to explain them how I usually debug
overconstrained specifications. First, I asked the LLM to use `git bisect` to
find the last working commit. It crunched for 10-15 minutes and found the last
working one. Comparing the git diffs did not help though.

The next usual step is to comment out some parts of the specification, and see
whether the transition becomes enabled. If it does, then we know that one of the
problematic constraints is in the commented-out part. We did this exercise for
about 1 hour. The agentic loop was amazing. The LLM was doing everything
automatically.  In the end, we still could not find the root cause.

**I was surprised how well Codex and Claude were running Apalache and
transforming the TLA<sup>+</sup> specification. They neither required skills,
nor MCP.** They simply ran the model checker, parsed its output and parsed the
produced counterexamples. Being a CLI tool finally paid off for Apalache!

## Turn specification debugging into code generation

I could stare at the specification and look for a mismatch. In the hindsight,
that would not help me, as the issue was outside of the subprotocol
specification. So I thought: LLMs fail to identify the issue, but they can
generate code in minutes. **Can I turn this debugging problem into a code
generation problem?**

Hence, I told the LLM to take the pieces of my specification framework, extract
the random simulator, write an ad hoc simulator that drives the system into the
exact problematic state, do random exploration from there, look for the disabled
assumptions. Since my framework is written in Python, it was quite an easy task
for the LLM. **In 5 minutes, it ran the ad hoc simulator**. **In 2-3 more
minutes, we had the root cause!** Indeed, there were two contradicting
constraints. It was hard to identify them by looking at the specification, as
one of them was in the subprotocol specification, and the other one was in the
system specification. Obviously, I extended `AGENTS.md` with an instruction to
avoid introducing constraints at both levels.

This approach worked, since my specification is not just a TLA<sup>+</sup>
specification. It is actually Python code. It can be executed. But it can also
generate a TLA<sup>+</sup> specification. As a result, the LLM can easily
interact with the Python code, wrap it into a large ad-hoc simulator, and run
it. At the same time, the model checker uses the generated TLA<sup>+</sup>
specification to reason about it. Moreover, the LLM also benefits from having
two different perspectives in the form of the Python code and TLA<sup>+</sup>.

If you find this hint useful, leave a comment below.

## Want to talk?
 
<!-- References -->

[contact]: https://konnov.phd/posts/service/
[Igor Konnov]: https://konnov.phd
[LI]: https://www.linkedin.com/in/igor-konnov-at/
[tftp-testing]: {% link _posts/2025-12-15-tftp-symbolic-testing.md %}
[Apalache]: https://apalache-mc.org
