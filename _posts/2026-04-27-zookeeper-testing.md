---
layout: post
title: "Extracting formal specifications from Apache ZooKeeper with AI tools and Apalache"
date: 2026-04-27
author: Igor Konnov
categories: testing model-checking
tlaplus: true
math: false
shell: false
python: true
hidden: false
feed: true
---

**Author:** [Igor Konnov][]

**Date:** April 27, 2026

*This text is artisanally typed using a keyboard. The
figures are generated with ChatGPT 5.5. By AI tools, I refer to Codex GPT 5.4
and Claude Code Sonnet/Opus 4.6.*

Recently, I gave a talk at the [TLA+ Community Meeting 2026][tla2026]. As people
in the audience probably expected, I talked about the new [Apalache JSON-RPC][]
and how it can be used to test real distributed protocols. As the first example,
I presented the case study on [symbolic testing of TFTP protocol][tftp-testing],
which was published in December 2025. As the second example, I presented a case
study on symbolic testing of [Apache ZooKeeper][Apache ZooKeeper].

In case of TFTP, **the main hypothesis was that AI tools can accelerate the
process of writing test harnesses for protocol testing**. In October 2025, I
used Copilot and Sonnet 4.5. The answer was "yes", though the AI tools in 2025
required plenty of manual intervention. Back then, I wrote the TLA<sup>+</sup>
specification of TFTP by hand. I also had to refine it manually, in about 20-25
iterations. As a reward, the test harness helped me to find a few bugs in the
real implementations. I still had to triage the bugs manually though.

The next step was to ask the following question:

<div style="font-size: 1.3em; text-align: center;">
<p style="font-size: 1.3em;"><strong>Can AI tools extract formal specifications
from the source code and write test harnesses?</strong></p>
</div>

In March-April 2026, I ran Claude Code Sonnet/Opus 4.6 and Codex GPT 5.4 to
**check this hypothesis on the example of Apache ZooKeeper**.
This case study is the subject of this blog post. I already hinted at this work
in [Debug as Code Generation][debug-code].  To this end, I have been running
this loop:

  <figure>
    <a href="{{ site.baseurl }}/img/zk-testing/extraction-loop.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/zk-testing/extraction-loop.png"
        alt="Extraction loop">
    </picture></a>
    <figcaption>Figure 1: Formal specification extraction loop with AI tools and Apalache.</figcaption>
  </figure>

In general, it looks like **the answer is "yes, but"**. Over the last days, the
extraction-checking stopped finding new mismatches between the behavior of a
running ZooKeeper replica and the extracted formal specification and harness. So I do
not have new logs to feed into Codex and Claude Code, and it is good time to
reflect on this.

Look carefully at Figure 1. Even though my AI agents had a lot of freedom in
coming up with their plans and implementing them, **I did not let the agents run
wild**.  I keep reading claims about "autonomous agents" and "agentic loops",
where agents simulate unhealthy human management loops. I still had to read the
triage reports and implementation plans. Several times, had not I caught an
agent in planning to introduce really bad workarounds in the specification, we
would have gone down the rabbit hole of slop. Every iteration had a separate
commit, so we could keep track of regressions in the specification and harness.
Having said that, I admit that my reviews were high-level and intuitive, not
Github-level reviews.

**Did I burn thousands of dollars on this?** Nope. I did this case study with
two lowest-tier subscriptions to Codex and Claude Code, which cost me **about
$80 for two months** in total (given the latest news about [Claude price
changes][claude-price-change] and [Copilot price changes][copilot-price-change],
this becomes more expensive). Most of the time went into running the experiments
on my workstation: AMD Ryzen 9 5950X processor (16 physical, 32 logical cores),
128 GB RAM. The cool thing about my testing architecture is that the machine was
running 10-15 episodes of 300 steps in parallel on 10-20 cores, totalling in
30000-90000 steps in a single campaign.  Hence, the AI tools had to triage 1-30
counterexamples at once, before starting a new campaign.

{% include tip.html content="As I mentioned earlier, I stopped accompaying my
blog posts with complete artifacts. AI slop forks are real. It takes me time to
design and conduct the experiments on a beefy machine, as well as to find the
right format to interpret and explain the data. Even with the help of the
frontier models, though they are of great help. It only takes 10-15 minutes to
repackage the benchmarks and results with an AI tool, having the experimental
data. Hence, I am sharing my lab book with the customers and researchers, upon
request."
%}

## 1. What worked well

**Extracting formal specifications.** As I learned with [TFTP
testing][tftp-testing], AI tools need a good predefined
architecture. Hence, I spent some time capturing this architecture in
`AGENTS.md` and `CLAUDE.md`. The formal specification is composed of several
modules, each corresponding to a subprotocol of ZooKeeper:

 - **process** captures the normal lifecycle of a ZooKeeper replica: `start`,
    `on_started`, `on_stopped`. Crashes and restarts are handled by
    the **system** module.
 - **tcp** captures the standard TCP lifecycle: `connect`, `accept`, `disconnect`,
    `half_close`, `reset`, `refused`.
 - **fle** captures the Fast Leader Election protocol, which is used by ZooKeeper to
    elect a leader among the replicas: `send_notification`, `rcv_notification`,
    `become_leader`, `become_follower`, `restart_election`.
 - **zab** captures the ZooKeeper Atomic Broadcast protocol and its clients. It has 22
    actions, including `proposal`, `ack_proposal`, `commit`, `diff`, `trunc`, `snap`,
    `client_connect`, `client_ping`,  `client_create`, `client_set_data`, etc.
 - **system** composes the above modules and adds failures.

These modules were written by the AI tools, by following the high-level
architecture. To get the flavor of the specification, look at one action from
the specification of ZAB, all generated by AI tools, hands off the keyboard:

```python
@action(inline=False)
def send_diff(c: Context[ZabState], leader: Expr, follower: Expr, next_turn: Expr):
    """Leader sends DIFF to a follower (requires quorum of epoch_acked)."""
    s = c.state
    c.assume(follower != leader)
    c.assume(_proc_up(s, leader))
    # The leader must have completed its election before registering in
    # epoch_leader.  Without this guard a FOLLOWING replica whose
    # fle_current_vote happens to be targeted by another follower can
    # act as a second leader for the same epoch, violating leadership2.
    c.assume(s.fle_role[leader] == LEADING)
    c.assume(_follower_targets_leader(s, follower, leader))
    c.assume(s.zab_sync[follower] == SYNC_EPOCH_ACKED)
    c.assume(_has_quorum_of_sync_state(s, leader, "epoch_acked"))
    c.assume(_can_send_diff(s, leader, follower))
    # Leader-initiated
    c.assume(_turn_matches_iut_actor(s, leader, next_turn))
    next_s = s.edit()
    next_s.zab_sync[follower] = SYNC_DIFF_SENT
    next_s.zab_state[leader] = SYNCHRONIZATION
    next_s.zab_accepted_epoch[leader] = s.zab_current_epoch[leader]
    next_s.zab_persisted_accepted_epoch[leader] = s.zab_current_epoch[leader]
    # By this point ACKEPOCH quorum has formed (see epoch_acked guard above),
    # which means ZK's Leader.lead() has already called setCurrentEpoch on
    # disk. Bump the currentEpoch shadow here to match that disk write.
    next_s.zab_persisted_current_epoch[leader] = s.zab_current_epoch[leader]
    next_s.epoch_leader[s.zab_current_epoch[leader]] = (
        s.epoch_leader[s.zab_current_epoch[leader]].union(Set(leader))  # type: ignore
    )
    s.zab_action = ZabAction.SendDiff(  # type: ignore
        ZabDiff(leader=leader, follower=follower)
    )
```

As you can see, this is Python code, not TLA<sup>+</sup>. I noticed that the AI
tools are quite good at writing Python. Hence, they write the specification in a
Python DSL, which is automatically translated to TLA<sup>+</sup>. The test
harness is also written in Python, and it uses the [Apalache JSON-RPC][] to
interact with the Apalache model checker. **If you are interested in the details
of this Python DSL, [contact me][contact]**.

The fragment of the above action in TLA<sup>+</sup> looks like [this][zabdiff].
The complete generated specification looks much more hairy. If you are still
curious, check its snapshot in [this gist][zkspec].

In the table below, you can see the statistics of the formal specification.
Since the TLA<sup>+</sup> specification is generated from the Python code,
this specification is monolithic and has no submodules.

| Module  | Actions | Python LOC   | TLA<sup>+</sup> LOC   |
|---------|--------:|-------------:|-----------:|
| process | 5       | 90           |          - |
| tcp     | 6       | 220          |          - |
| fle     | 5       | 1605         |          - |
| zab     | 22      | 2256         |          - |
| system  | 9       | 1603         |          - |
| **Total**  |      | **5774**     | **3065**   |

The test harness is also written in Python. It is composed of several modules,
which are listed in the table below.

| Subsystem            | Modules                                                    | Lines         |
|----------------------|------------------------------------------------------------|--------------:|
| Orchestration        | main.py, scheduler.py, runner.py                           | 3462          |
| Validation           | oracle.py, serde.py                                        | 2493          |
| Networking / wire    | comms.py, client_wire.py, quorum_wire.py, election_wire.py | 3063          |
| Data model / support | events.py, queues.py, config.py, fixed_tree.py, log.py     | 867           |
| Tooling              | log_to_mermaid.py                                          | 414           |
| **Total**            |                                                            | **10299**     |


## 2. What worked not so well

I have little idea about what the protocol is doing.

## 3. Checking invariants and producing examples

## 4. Reproducing known bugs

## 5. Is this a poor man's CEGAR loop?

  <figure>
    <a href="{{ site.baseurl }}/img/zk-testing/cegar.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/zk-testing/cegar.png"
        alt="Classical CEGAR loop">
    </picture></a>
    <figcaption>Figure 2: Classical CEGAR loop.</figcaption>
  </figure>



## Want to talk?
 
<!-- References -->

[contact]: https://konnov.phd?pmf=20260427
[Igor Konnov]: https://konnov.phd
[tla2026]: https://conf.tlapl.us/2026-etaps/
[Apalache JSON-RPC]: https://github.com/apalache-mc/apalache/tree/main/json-rpc
[tftp-testing]: {% link _posts/2025-12-15-tftp-symbolic-testing.md %}
[LI]: https://www.linkedin.com/in/igor-konnov-at/
[Apalache]: https://apalache-mc.org
[Apache ZooKeeper]: https://zookeeper.apache.org/
[zkspec]: https://gist.github.com/konnov/38af0cbd45b68da819cd76f70859ed94
[zabdiff]: https://gist.github.com/konnov/38af0cbd45b68da819cd76f70859ed94#file-system-tla-L2272-L2311
[debug-code]: {% link _posts/2026-03-23-debug-as-code-generation.md %}
[claude-price-change]: https://www.theregister.com/2026/04/22/anthropic_removes_claude_code_pro/
[copilot-price-change]: https://github.blog/news-insights/company-news/changes-to-github-copilot-individual-plans/