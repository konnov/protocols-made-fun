---
layout: post
title: "Extracting formal specifications from Apache ZooKeeper with AI tools and Apalache"
date: 2026-05-26
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

**Date:** May 26, 2026

*This text is artisanally typed using a keyboard, with occasional suggestions by
Copilot. The figures are generated with ChatGPT 5.5. The plots are produced by
AI-generated scripts from the experimental data. By AI tools, I refer to Codex
GPT 5.4/5.5 and Claude Code Sonnet/Opus 4.6/4.7.*

Recently, I gave a talk on "*Interactive symbolic testing with TLA<sup>+</sup>,
Apalache, and LLMs*" at the [TLA+ Community Meeting 2026][tla2026]. If you
prefer watching talks, see [the talk recording][tla2026-recording]. I talked
about the new [Apalache JSON-RPC][] and how it can be used to test real
distributed protocols. As the first example, I presented the case study on
[symbolic testing of TFTP protocol][tftp-testing], which was published in
December 2025. As the second example, I presented a case study on symbolic
testing of [Apache ZooKeeper][Apache ZooKeeper], which is the subject of this
blog post. I also talked about this as ongoing work at [D-CON 2026][] (thanks to
[Uwe Nestmann][] for inviting me!).

In case of TFTP, **the main hypothesis was that AI tools can accelerate the
process of writing test harnesses for protocol testing**. In October 2025, I
used Copilot and Sonnet 4.5. The answer was "yes", though the AI tools in 2025
required plenty of manual intervention and literally drained my energy. Back
then, I wrote the TLA<sup>+</sup> specification of TFTP by hand. I also had to
refine it manually, in about 20-25 iterations. As a reward, the test harness
helped me to find a few bugs in the real implementations. I still had to triage
the bugs manually though.

*Footnote*: Actually, the real question for me was not whether AI tools could
help the engineers to write a test harness. In my experience, engineers avoid
writing test harnesses as much as they can. So the real question was whether the
AI tools could do the job that engineers avoid doing.

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

In general, it looks like **the answer is "yes, but"**. The extraction-checking
loop stopped finding new mismatches between the behavior of a running ZooKeeper
replica and the extracted formal specification and harness. So I do not have
new logs to feed into Codex and Claude Code, and it is good time to reflect on
this.

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

What I believe is the killer feature of this approach is that **it does not need
any pre-existing test suites**. We do not mutate the existing tests. The model
checker **finds new tests**, including timeouts, crashes, TPC disconnects, etc.
Moreover, this approach requires **zero code instrumentation**. We do not have
to add any hooks or logging to the implementation. **The test harness operates at
the TCP boundary**.

**Did I burn thousands of dollars on this?** Not at all. I did this case study
with two lowest-tier subscriptions to Codex and Claude Code, which cost me
**about $80 for two months** in total. (Given the news about [Claude price
changes][claude-price-change] and [Copilot price changes][copilot-price-change],
this becomes more expensive). Most of the time went into running the testing
experiments on my workstation: AMD Ryzen 9 5950X processor (16 physical, 32
logical cores), 128 GB RAM. The cool thing about my testing architecture is that
the machine was running 10-15 episodes of 300 steps in parallel on 10-20 cores,
totalling in 30000-90000 steps in a single campaign.  Hence, the AI tools had to
triage 1-30 counterexamples at once, before starting a new campaign.

Since we now live in a hype-driven world, I want to stress that **this is still
an experiment**. I am pretty sure that [Ouyang et. al.][multi-grained] had much
more time to write their TLA<sup>+</sup> specifications of ZooKeeper and to
conduct their experiments.

If you read the blog post carefully, you will probably find some points that
could be investigated further. I have decided to time box this experiment and
report about it where it is.

{% include tip.html content="As I mentioned earlier, I stopped accompaying my
blog posts with complete artifacts. AI slop forks are real. It takes me time to
design and conduct the experiments on a beefy machine, as well as to find the
right format to interpret and explain the data. It only takes 10-15 minutes to
repackage the benchmarks and results with an AI tool, having the experimental
data. Hence, I am sharing my lab book with the customers and researchers, upon
request."
%}

**Want to skip the long text?** [Jump to the
conclusions](#conclusions).

## 1. The effort

This experiment took about two months, from March 2026 to April 2026. The git
repository has 336 commits in total. Except for several initial commits, each
new commit corresponds to a new iteration of the extraction-checking loop.

You can see the statistics in the figures below:

 - Figure 2 shows the number of commits per day.
 - Figure 3 shows the number of lines added and deleted in the whole repository.
 - Figure 4 shows the number of lines added and deleted in the specification files.
 - Figure 5 shows the number of lines added and deleted in the test harness (zoomonkey).

You can see that the commit volume decays with time. This is a sign of
convergence. The first week has the most commits and the most code added and
deleted. This was the bootstrapping phase. It's also interesting to observe a
big splash around the first-second week of April. This is where we start to
reach a new class of behaviors that did not match the implementation.

  <figure>
    <a href="{{ site.baseurl }}/img/zk-testing/git_stats_commits.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/zk-testing/git_stats_commits.png"
        alt="Git stats">
    </picture></a>
    <figcaption>Figure 2: Commit statistics in this experiment.</figcaption>
  </figure>

  <figure>
    <a href="{{ site.baseurl }}/img/zk-testing/git_stats_lines.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/zk-testing/git_stats_lines.png"
        alt="Git stats">
    </picture></a>
    <figcaption>Figure 3: Addition/deletion statistics in this experiment.</figcaption>
  </figure>

  <figure>
    <a href="{{ site.baseurl }}/img/zk-testing/git_stats_spec.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/zk-testing/git_stats_spec.png"
        alt="Git stats">
    </picture></a>
    <figcaption>Figure 4: Addition/deletion statistics in the specification files.</figcaption>
  </figure>

  <figure>
    <a href="{{ site.baseurl }}/img/zk-testing/git_stats_zoomonkey.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/zk-testing/git_stats_zoomonkey.png"
        alt="Git stats">
    </picture></a>
    <figcaption>Figure 5: Addition/deletion statistics in the test harness.</figcaption>
  </figure>

## 2. Extracting formal specifications

As I learned with [TFTP testing][tftp-testing], AI tools need a good predefined
architecture. Hence, I spent some time capturing this architecture in
`AGENTS.md` and `CLAUDE.md`. The formal specification is composed of several
modules, each corresponding to a subprotocol of ZooKeeper:

 1. **Module process** captures the normal lifecycle of a ZooKeeper replica: `start`,
    `on_started`, `on_stopped`. Crashes and restarts are handled by
    the **system** module.
 2. **Module tcp** captures the standard TCP lifecycle: `connect`, `accept`, `disconnect`,
    `half_close`, `reset`, `refused`.
 3. **Module fle** captures the Fast Leader Election protocol, which is used by ZooKeeper to
    elect a leader among the replicas: `send_notification`, `rcv_notification`,
    `become_leader`, `become_follower`, `restart_election`.
 4. **Module zab** captures the ZooKeeper Atomic Broadcast protocol and its clients. It has 22
    actions, including `proposal`, `ack_proposal`, `commit`, `diff`, `trunc`, `snap`,
    `client_connect`, `client_ping`,  `client_create`, `client_set_data`, etc.
 5. **Module system** composes the above modules and adds failures.

These modules were written by the AI tools, by following the high-level
architecture, hands off the keyboard. To get the flavor of the specification,
look at one action from the specification of ZAB:

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
interact with the model checker. **If you are interested in the details of this
Python DSL, [contact me][contact]**.

The fragment of the above action in TLA<sup>+</sup> looks like [this][zabdiff].
The complete generated specification looks much more hairy. If you are still
curious, check its snapshot in [this gist][zkspec].

In the table below, you can see the statistics on the formal specification.
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

## 3. Generating the test harness

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

The interesting design choice here is that the test harness runs a **single
replica of ZooKeeper**. We call this replica **implementation under test**
(IUT). The whole distributed system exists only in the formal specification and
its behavior. This is conceptually similar to a [Digital Twin][] of the real
distributed system.

Since most of the behavior exists only in the specification, this approach is
sensitive to **quick and accurate** choice of events. I believe that a random
simulator would not help us much here, as it would keep crunching through a very
large set of unproductive events.

This is where the new [Apalache JSON-RPC][] comes into play. The test harness
chooses the next action to execute and asks the symbolic model checker to find
the action parameters that would enable it. It also calls Apalache to check the
state invariants and find out whether the implementation's output matches the
specification. Since the complexity of SMT solving grows with the number of
steps very quickly, we use the new method [compact][] to prune the symbolic
context and keep it manageable.

## 4. Running the test harness

Running the test harness looks quite boring:

```sh
$ ./scripts/run-parallel.sh 8 -- --replicas 3 --episodes 20 --steps 500 \
  --failure-rate 0.2 --fle-rate 0.05 --fallback-rate 0.1 --decay 0.8 --crashes 0
```

It basically runs 20 episodes of 500 steps in parallel, with 3 replicas and a
number of parameters to control the test scenario generation. The script is
using [GNU Parallel][] to run the episodes in parallel. Since each test runs **a
single actual replica** and simulates the rest of the distributed system with
the specification, running multiple experiments in parallel is easy. We only
have to make sure that different experiments get assigned different ports.

Every episode produces a detailed log of events. If it finds an invariant
violation or a mismatch between the behavior of the real replica and the
specification, it produces a trace in the [ITF format][]. These logs and traces
are read by the AI tools to triage the mismatches and to improve the
specification and the test harness.

Similar to [tftp-testing][], I have a script to convert the logs into a sequence
chart in Mermaid. However, for a system of this complexity, these diagrams are
hard to digest. Instead, I produce a high-level figure of the test campaign that
shows the events in all episodes in one big picture. See Figure 6. Click on it
to see the full-size version and examine it in detail.

  <figure>
    <a href="{{ site.baseurl }}/img/zk-testing/episodes-summary.png" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/zk-testing/episodes-summary.png"
        alt="Episodes summary">
    </picture></a>
    <figcaption>Figure 6: Episodes summary of the test campaign (view the full-size image by clicking).</figcaption>
  </figure>

If you look at the events in the figure, you will see that the most episodes
have productive events such as ZAB proposals, commits, diffs, snapshots, client
operations, etc. However, a few episodes degrade into permanent leader election,
where the implementation-under-test keeps sending FLE notifications. Basically,
the two simulated replicas keep working together and exclude the IUT from the
quorum.

## 5. Triaging conformance mismatches

Back in October 2025, Copilot + Sonnet 4.5 were quite bad at triaging
specification mismatches. Now, the frontier models are quite good at it. This is
definitely an improvement in the frontier models.  I also believe that my effort
of definining a good architecture for the test harness paid off this time. Below
are fragments of a triage report by Claude Code Opus 4.7:

<div markdown="1" class="ai-output-frame">

A single oracle-reported spec violation landed in the 2026-04-24 parallel
sweep. The dump files live at:

- logs/20260424_071307/episode_009_step_160_spec_violation.itf.json
- logs/20260424_071307/episode_009_step_160_spec_violation_trace.itf.json

Configuration: inst03 (PERSIST_IUT_STATE=True), 3 replicas,
permutation {1: 2, 2: 3, 3: 1}, IUT is spec replica 1 / dynamic id 2.
Violation reason: output_queue_violation — the oracle could not validate
the IUT's zab_follower_info output after 10 drain passes.

Episode timeline (relevant subset)

 1. Replica 1 starts at 10:32; long FLE churn; becomes follower; emits
 zab_follower_info at 10:41 with accepted_epoch=0 — spec accepts
 (transition 31). No zab_leader_info ever validated in this episode.
 2. At 10:58 replica 1 is stopped (tester action, not crash). On-disk
 acceptedEpoch at that moment: still 0 (follower never received
 LEADERINFO, never persisted).
 3. At 11:06:52 replica 1 restarts. inst03 preserves the data directory,
 so on-disk acceptedEpoch is read back as 0.
 4. At 11:12:34 IUT emits fle_become_leader(r1) (transition 27). Spec
 speculatively bumps zab_accepted_epoch[1] to 1 via
 candidate_epoch_capped in spec/system.py:665.
 5. At 11:12:42 scheduler picks simulated→IUT zab_follower_info
 (transition 31 on the simulated follower side). Spec's
 send_followerinfo (spec/zab.py:900) atomically observes leader-side
 quorum (1 IUT + 1 simulated ≥ majority of 3) and bumps
 zab_persisted_accepted_epoch[1] at spec/zab.py:972 — the comment
 at line 1068 acknowledges this is the earliest-disk-write model of
 Leader.getEpochToPropose().
 6. At 11:12:48 tcp_disconnect r1 ↔ r3 (quorum).
 7. At 11:12:50 IUT emits fle_restart_election(r1) (transition 30). Spec
 rolls back zab_accepted_epoch[1] to
 zab_persisted_accepted_epoch[1] per commit aee611c
 (spec/system.py:648-693) — which is already 1 due to step 5, so the
 rollback is a no-op on the live field and the shadow stays at 1.
 8. At 11:14:16 replica 1 (now FOLLOWING r2 in both spec and IUT) emits
 zab_follower_info(accepted_epoch=0). Spec expects 1. Blocked.

 Root cause

 The spec assumes Leader.getEpochToPropose()'s disk write has completed
 atomically the moment any FOLLOWERINFO arrival would establish quorum —
 that's the design of the zab_persisted_accepted_epoch[leader] bump in
 send_followerinfo (spec/zab.py:972). In this trace the IUT's leader
 thread either never processed the simulated FOLLOWERINFO at all (the
 incoming quorum connection to r1 was disrupted around that time — the
 TCP disconnect at 11:12:48 is between r1 and r3, but similar disruption
 to the r2–r1 quorum path around 11:12:42–48 would leave
 getEpochToPropose() blocked), or processed it but was interrupted
 before the disk write completed. Either way, the IUT's on-disk
 acceptedEpoch stayed at 0 while the spec's shadow went to 1.

 The aee611c rollback is correctly applied but operates on the live
 epoch field only; by design it restores live from shadow, so when the
 shadow itself is stale-high, restart_election can't recover. This is
 the new Family-A sub-variant noted in the earlier audit: speculative
 advance of the persisted shadow, not just the live epoch.

</div>

Several things are impressive here:

 1. **The test harness stopped a replica and dropped a TCP connection at the
 right moments**, so the replica did not have a chance to persist the new
 accepted epoch.  It did not happen often, but the parallel campaign was diverse
 enough to trigger this scenario. To be fair, the initial version of the test
 harness would not be able to trigger this scenario. **I had to teach the AI
 tools to properly diversify the test scenarios**.
 
 2. **Claude figured this out in a matter of minutes**. It would be hard for me to
 figure this out.

 3. **It also proposed a fix.**

## 6. Checking invariants and producing examples

Since the AI tools write the specification and the test harness, we have to
evaluate the quality of the specification and the harness together. To this end,
we do two things:

 1. Add state invariants to evaluate safety.
 2. Add state examples to illustrate reachability of interesting states.

### 6.1. State invariants

To our luck, ZooKeeper already has several [TLA<sup>+</sup>
specifications][zookeeper-tla-spec] for earlier versions. I let the AI tools
harvest these specifications for invariants.

For example, these are the shortest invariants these tools wrote:

```python
@invariant
def leadership1(s: SystemState):
    return s.REPLICA.forall(
        lambda i: s.REPLICA.forall(
            lambda j: (
                _is_established_leader(s, i)
                & _is_established_leader(s, j)
                & (s.zab_accepted_epoch[i] == s.zab_accepted_epoch[j])
            ).implies(i == j)
        )
    )

@invariant
def leadership2(s: SystemState):
    return Set(Val(1), ..., Val(s.MAX_EPOCH)).forall(
        lambda epoch: s.epoch_leader[epoch].size <= Val(1)
    )

@invariant
def fle_wait_finalize_sound(s: SystemState):
    return s.REPLICA.forall(
        lambda replica: (
            _fle_invariant_replica_live(s, replica) & s.fle_wait_finalize[replica]
        ).implies(
            _fle_has_proposed_recv_quorum(s, replica)
            | _fle_has_local_ooe_quorum(s, replica)
        )
    )
```

Their TLA<sup>+</sup> translations look like this:

```tla
Leadership1 ==
    \A i142 \in REPLICA: \A j143 \in REPLICA:
        (/\ /\ /\ (fle_role[i142] = "LEADING")
               /\ \/ (zab_state[i142] = "synchronization")
                  \/ (zab_state[i142] = "broadcast")
            /\ /\ (fle_role[j143] = "LEADING")
               /\ \/ (zab_state[j143] = "synchronization")
                  \/ (zab_state[j143] = "broadcast")
         /\ (zab_accepted_epoch[i142] = zab_accepted_epoch[j143])) => ((i142 = j143))

Leadership2 ==
    \A epoch144 \in (1)..(MAX_EPOCH): (Cardinality(epoch_leader[epoch144]) <= 1)
```

The translation of `fle_wait_finalize_sound` is a bit longer, you can check it
in the
[FleWaitFinalizeSound](https://gist.github.com/konnov/38af0cbd45b68da819cd76f70859ed94#file-system-tla-L535-L559).

We have 11 invariants in total. The other 8 invariants are more complex. These
invariants are checked by the test harness with Apalache. We can also check them
against the generated TLA<sup>+</sup> specification.

### 6.2. Reachability examples

I usually write "falsy invariants" to check reachability of interesting states.
Again, the AI tools are quite good at writing such "examples". For instance:

```python
@example
def at_least_one_committed(s: SystemState):
    return s.REPLICA.exists(
        lambda replica: s.zab_last_committed[replica].index >= Val(1)
    )
```

This example is translated to the following TLA<sup>+</sup> invariant:

```tla
AtLeastOneCommitted ==
    ~(\E replica63 \in REPLICA: (zab_last_committed[replica63].index >= 1))
```

To see an instance of this example, I ran a test campaign with 10 episodes of
100 steps each. One of the episodes reached a state that satisfies
`at_least_one_committed`. Below is the summary of this episode by Claude Code
Opus 4.7:

<div markdown="1" class="ai-output-frame">

Trace summary — example of at_least_one_committed

Episode 5, step 86. Replica mapping: spec 1 ↔ dynamic 2 (the IUT), spec 2 ↔ dynamic 1, spec 3 ↔ dynamic 3. So the IUT
is spec replica 1 in the analysis below.

What happened, in order:

1. Initial election attempt fails. Spec 1 (IUT) briefly thinks it's leader (fle_become_leader replica=1 at t≈+25s) but
    then has to fle_restart_election (t≈+45s). Spec 3 simultaneously becomes leader (fle_become_leader replica=3 at
    t≈+19s); spec 2 becomes follower early on.
2. Stable leadership formed under spec 3. After the restart, IUT (spec 1) joins as follower of spec 3
    (fle_become_follower replica=1, then zab_follower_info {follower_id:1, leader_id:3}).
3. ZAB recovery completes. The leader (spec 3) walks IUT through LEADERINFO → DIFF → NEWLEADER → UPTODATE (all with
    follower_id:1, leader_id:3). A second LEADERINFO/NEWLEADER/UPTODATE round (no ids logged) syncs the other simulated
    follower spec 2. All three replicas reach zab_state = "broadcast".
4. Write submitted to the leader. Step 85: a simulated client connects to spec 3 (the leader) and issues
    zab_client_create("/p1").
5. Proposal phase (step 86):
    - Leader (spec 3) emits zab_proposal at zxid=1, epoch=1.
    - A follower acks: zab_ack_proposal zxid=1 validates cleanly (transition 52).
    - With its own self-ack the leader reaches quorum and commits locally.
    - Oracle then detects the violated invariant — i.e. the dual @example fired.

Violation state (spec replica 3 only):
- zab_history[3] = [{create, /p1, zxid=1, epoch=1}]
- zab_last_committed[3] = {index:1, zxid:1}
- zab_committed_zxid = 1
- Replicas 1 (IUT) and 2 still have zab_last_committed.index = 0 and empty histories — the commit has not yet been
  broadcast to them.

</div>

Below is the sequence diagram of this full episode. Click on it to see the full-size
version and examine it in detail. It is quite long, so feel free to scroll
through it.

<figure>
    <a href="{{ site.baseurl }}/img/zk-testing/at_least_one_committed.svg" target="_blank" title="Click to open full-size"><picture>
      <img class="responsive-img"
        src="{{ site.baseurl }}/img/zk-testing/at_least_one_committed.svg"
        alt="At least one committed">
    </picture></a>
    <figcaption>Figure 7: A trace where at least one replica has committed (view the full-size image by clicking).</figcaption>
</figure>

The table below shows the example coverage in two test campaigns (20 episodes of
100 steps and 20 episodes of 200 steps).

| Example | Times found | Min step | Max step |
|---|---:|---:|---:|
| at_least_one_committed | 1 | 48 | 48 |
| at_least_two_committed | 1 | 74 | 74 |
| some_follower_synced | 4 | 26 | 43 |
| quorum_recovery_completed | 7 | 21 | 185 |
| newleader_sent | 3 | 23 | 42 |
| forwarded_request_sent | 1 | 46 | 46 |
| forwarded_request_received | 1 | 68 | 68 |
| forwarded_write_committed | 1 | 74 | 74 |
| proposal_in_flight | 2 | 46 | 47 |
| proposal_has_quorum_acks | 1 | 74 | 74 |
| two_proposals_in_flight | 1 | 72 | 72 |
| first_write_committed_on_quorum | 1 | 48 | 48 |
| two_distinct_znodes_committed | 1 | 74 | 74 |


<a id="conclusions"></a>
## 7. Conclusions

Obviously, the AI tools change the way we should test distributed systems.
Interestingly, my conversations with these tools show that they have very little
understanding of distributed computations. Funny enough, even though they have
all the knowledge about TCP/IP at their fingertips, if you ask them right, they
cannot efficiently operate with this knowledge. However, when they have plenty
of counterexamples to learn from, they improve the quality of the testing
harness very quickly. This is where the interplay of formal verification and AI
tools becomes really powerful. The model checker produces negative and positive
examples, and the AI tools learn from them and improve the specification and the
test harness.

**The good**:

 - It is actually **possible to extract formal specifications from the source
 code** of a real distributed system and to write test harnesses with AI tools.
 We have to keep in mind that this requires a verification loop, which uses a
 tool such as [Apalache][].
 
 - In this experiment, we extracted a **modular specification that captures five
 protocols**.
 
 - If we do not try to one-shot the testing process and **follow an iterative
 process with a clear pre-defined architecture**, the AI tools actually help us.
 **"Test it and make no mistakes" obviously does not work**.
 
 - Comparing to [tftp-testing][], the **AI tools in 2026 are much better** at
 triaging specification mismatches and producing fixes. The whole process is
 **much less energy-draining now**.
 
**The bad**:

 - I have **no idea about the extracted specification**. When I write a
 specification by hand, I internalize the protocol behavior.  Even after I
 forget the details, I can still come back and recover them from the spec.
 Here, it is much harder.
 
 - If we focus on bug finding, it is fine to have a hard-to-understand
 specification. However, **from the maintainability perspective, it is a big
 problem**. This is probably why we see such a spike in security bugs, but no so
 much in real software products.
 
Even though the whole development is quite exciting, my main takeaway is that
**writing formal specifications is still a human job**. AI tools
can assist us in producing test harness and finding issues.

If you need help with writing formal specifications and producing test
harnesses, contact me. I can help you with that. It still takes time, expertise,
and effort to do it right. Also, coming up with the right architecture is not as
easy as it may seem. Of course, you can hire an intern and spend several months
learning from your own mistakes together. Or you can fast-forward it and hire
me.

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
[D-CON 2026]: https://www.tu.berlin/en/mtv/research/events/d-con-2026
[Uwe Nestmann]: https://www.tu.berlin/en/mtv/team/head/uwe-nestmann
[multi-grained]: https://dl.acm.org/doi/abs/10.1145/3689031.3696069
[Digital Twin]: https://en.wikipedia.org/wiki/Digital_twin
[zookeeper-tla-spec]: https://github.com/Disalg-ICS-NJU/zookeeper-tla-spec
[ITF Format]: https://apalache-mc.org/docs/adr/015adr-trace.html
[tla2026-recording]: https://www.youtube.com/watch?v=CQPhAfi-6Uk
[compact]: https://github.com/apalache-mc/apalache/tree/main/json-rpc#311-method-compact
[GNU parallel]: https://www.gnu.org/software/parallel/