---
layout: post
title: "The Force Awakens: Hybrid Blockchain Runtime Monitors (Solarkraft #4)"
date: 2024-06-24
categories: 
  - "solarkraft"
tags: 
  - "apalache"
  - "formal-methods"
  - "runtime-monitor"
  - "smart-contracts"
  - "solarkraft"
  - "soroban"
  - "specification"
  - "stellar"
  - "tla"
  - "tlaplus"
---

![Solarkraft](/img/solarkraft.png)

**» This guest post by [Andrey Kuprianov][] first appeared [on his blog][part4].**

_This is the forth in a series of blog posts introducing [Solarkraft][], a TLA+-based runtime monitoring solution for [Soroban smart contracts][Soroban]. The first post,_ ["A New Hope – Why Smart Contract Bugs Matter and How Runtime Monitoring Saves the Day"][part1] _gives an overview of smart contracts, explains how traditional security fails to address major challenges in securing crypto assets, and introduces runtime monitoring as a solution. The second post,_ ["Guardians of the Blockchain: Small and Modular Runtime Monitors in TLA+ for Soroban Smart Contracts"][part2] _introduces the basic language of Solarkraft monitors. The third post,_ ["How to Run Solarkraft"][part3] _gives an overview of the various features of Solarkraft, and explains how to use each one, step-by-step._ 


_Solarkraft has been developed in collaboration by [Igor Konnov][], [Jure Kukovec][], [Andrey Kuprianov][] and [Thomas Pani][]._

While the previous posts explain the current state of the project, in this one we take one step further, and explore the directions in which we plan to evolve blockchain runtime monitoring with Solarkraft. Throughout the post we are using the same [`timelock` contract][timelock] from `soroban-examples` that was used in [Part 2: "Guardians of the Blockchain"][part2]; please explore at least this post first to acquire the necessary context.


## Blockchain Runtime Monitors

Runtime monitoring, also known as [Runtime verification][], is a well-established field, where many practical approaches have been devised and applied successfully. Based on this heritage, we proposed in [Part 2: "Guardians of the Blockchain"][part2] the first version Web3 runtime monitoring system for the Stellar blockchain, which is based on the [TLA+][] specification language, a well-established formalism for specifying and verifying distributed systems. 

Taking a step back from the concrete solution, let's try to answer the more abstract question: _What do we want to achieve with runtime monitors in blockchains?_ As eventually runtime monitors are going to be deployed and executed _on the live blockchain_, and they should satisfy the three requirements:

- **Prevent safety violations** (_safety_): bad things, such as your token balance being stolen, should not happen. This is the primary goal of runtime monitors: react preventively, and abort unwanted executions.
- **Detect liveness violations** (_liveness_): good things should be able to happen! E.g. you, as an account owner, should be able to withdraw your own balance. If a legitimate transaction keeps reverting, that's also a bug, not less severe than someone stealing your tokens.
- **Detect unexpected behaviors** (_completeness_): same as code, specs are not perfect. If a spec author overlooked some behaviors, and they manifest themselves on the live blockchain, this may mean anything: from simple spec incompleteness, to an exploit being executed. Monitors should be configurable to either issue a simple warning, or to prevent such behaviors altogether.

The problem we've observed with the previously employed specification approaches is that the specs of _what_ the method should do can easily be much larger than the actual implementation; compare e.g. this [ERC-721 Certora spec][] with the [ERC-721 implementation][] (don't forget to exclude comments when comparing). So we would like to add to the above the following soft requirement:

- **Specify behaviors compactly and independently** (_compactness and modularity_): it is usually the case that a smart contract encompasses a lot of various aspects (e.g. authentication, authorization, storage management, math computations), as well is written/employed/reasoned about by various roles (e.g. smart contract developer, mathematician, architect, UI developer). All of those roles should be able to specify various aspects of the smart contract behavior as easily and as independently as possible.

So monitors should be able to specify both _safety_ and _liveness_ properties, be _complete_ wrt. the current and future system behaviors, and, preferably, also be _compact and modular_. For that we propose to apply a certain structure to the _direct monitors_ (those reasoning from cause to effect), as well as complement it with _reverse monitors_ (those going from effect to cause), thus combining them together in what we call _hybrid monitors_.


## Direct Monitors

Here we reason from the cause (method invocation) to the effect, but apply a structure which closely mimics in formal semantics what we expect to see when we program smart contracts. The essence of the structure is in the picture below:

![Direct monitor specs](/img/DirectMonitors.png)

- `MustFail_i` is a condition under which the method is expected to fail. If _any_ of those conditions hold, the monitor fires, and checks that the method does indeed fail;
- `MustPass_i` is a condition, under which the method is expected to succeed, _provided that_ none of the `MustFail_i` conditions fired. Each `MustPass_i` condition represents a separate happy path in the method invocation;
- `MustHold_i` is a condition that should hold over past and next state variables, if the method invocation is successful (e.g. the tokens should be transferred). _All_ of `MustHold_i` should hold if the method is executed successfully.


In the above, `Must<Fail|Pass|Hold>` is a prefix, which tells the monitor system how to interpret this predicate. The complete pattern for predicate names with these prefixes is as follows:

```
Must<Fail|Pass|Hold>_<Method>_<ConditionDescription>
```

All predicates which refer to the same `<Method>` will be grouped, to create together one _method monitor_. Interpreted formally, the monitor should do the following when `<Method>` is invoked:

1. If any of `MustFail_i` conditions fire, check that method invocation reverts (otherwise, issue a warning / revert if configured to do so)
2. If none of `MustFail_i` conditions fired, but method invocation reverted, issue a warning (incomplete spec)
3. If none of  `MustFail_i` fired, and one of `MustPass_i` conditions fired, check that method invocation succeeds (otherwise, issue a warning)
3. If none of  `MustFail_i` fired, and none of `MustPass_i` conditions fired, but method invocation succeeded, issue a warning of an incomplete spec (or revert if configured to do so)
4. If method invocation succeeds, check that all of `MustHold_i` conditions hold on the pre- and post-states of the method invocation (otherwise, issue a warning / revert if configured to do so)


Notice that above we apply _or_ as default connector for preconditions (`MustFail_i` / `MustPass_i`), and we apply _and_ as default connector for effects (`MustHold_i`). Thus, you may split preconditions/effects into separate predicates at your convenience, thus avoiding complicated logical structure inside predicates themselves.



### Direct monitors for the Timelock contract

Having outlined the general structure of direct monitors, let's apply it to the [Timelock contract][timelock]. Direct monitors for Timelock's `deposit` and `claim` methods can be found in [deposit.tla][deposit] and [claim.tla][claim] respectively; below we depict only the structure of these monitor specifications (we omit `Must<Fail|Pass|Hold>` as well as the method names for clarity).

![Timelock direct monitors](/img/TimelockDirectMonitors.png)

As can be seen, a direct method monitor is decomposed into a collection of independent and small monitors, i.e. we did achieve our (soft) goal of _compactness and modularity_. Safety and liveness goals also seem to be satisfied:

- _Safety_: Timelock's direct monitors guarantee the whole bunch of safety properties, a safety property is usually ensured by either <font style="background: #fd4d4d;">MustFail</font>, or <font style="background: #ffe342;">MustHold</font>, or a combination of both conditions. For example:
  - The property "only the approved claimant may claim the deposit" is ensured by the <font style="background: #fd4d4d;">NonClaimant</font> sub-monitor;
  - The property "the Timelock contract receives the deposited funds from the claimant" is ensured by the combination of <font style="background: #fd4d4d;">NotEnoughBalance</font> and  <font style="background: #ffe342;">TokenTransferred</font> sub-monitors.
 - _Liveness_: Timelock's liveness properties are guaranteed by the <font style="background: #54c45e;">MustPass</font> conditions: 
   - Implicit in case of `deposit` (whatever doesn't fail, should succeed);
   - Explicit in case of `claim`: a claim happening before the time bound, when its kind is `Before`, should succeed due to <font style="background: #54c45e;">BeforeTimeBound</font> (provided all other conditions are met); similarly, a claim happening after the time bound, when its kind is `After`, should succeed due to <font style="background: #54c45e;">AfterTimeBound</font>.


Can the described approach of direct monitors be considered satisfactory? Please stop to think about it for a sec, before opening our answer below.

<details>
<summary> <b>Are direct monitors enough?</b></summary>

<p>You may have guessed the answer: we believe NO! And here is an (incomplete) list of whys:</p>

<ol>
<li> A method may have a side effect, which was overlooked by the spec author. E.g. a boolean flag is set, which in another method allows to direct funds to another account.</li>
<li> Code evolves, but the spec stays as is; as a result a side effect above is introduced unintentionally, with the stale spec not accounting for it.</li>
<li> Internal state component is modified in multiple methods, in different ways. The specification about how the component should be updated is scattered in multiple places, and loopholes may easily creep in.</li>
<li> An invariant which is preserved by the method of this contract, is violated by a method from another contract. As no specs are written or monitored for this other contract, no violation is detected.</li>
</ol>

What is fundamentally missing from direct monitors, is the guarantee of <i>completeness</i>. Thus, we proceed to explore <i>reverse monitors</i>, which are complementary to direct monitors, specifically for ensuring specification completeness.
</details>


## Reverse Monitors

With reverse reasoning we will try to patch the loopholes that were left by direct monitor specs above. To do so, we start with an _effect_ (state was modified), and go back to its _cause_ (what should have happened taking the effect into account). Here is the corresponding picture which puts a bit of structure into the reverse reasoning.

![Reverse monitor specs](/img/ReverseMonitors.png)


- `MonitorTrigger_i` is a condition which triggers (activates) the monitor. If _any_ of those conditions hold, the monitor is activated;
- `MonitorEffect_i` is a condition over past and next state variables, which specifies the effect that the the monitor, if activated, should check. _All_ of `MonitorEffect_i` should hold if the transaction is successful.

Similar to direct reasoning, in the above, `Monitor<Trigger|Effect>` is a prefix, which tells the monitor system how to interpret this predicate. The complete pattern for predicate names with these prefixes is as follows:

```
Monitor<Trigger|Effect>_<Monitor>_<ConditionDescription>
```

All predicates which refer to the same `<Monitor>` will be grouped, to create together one _effect monitor_. Interpreted formally, the monitor should do the following when activated:

- If _any_ of `MonitorTrigger_i` conditions fire, check that _all_ `MonitorEffect_i` hold over the past and next states (otherwise, issue a warning / revert if configured to do so)

Again, imposing a simple structure which combines triggers with _or_, but effects with _and_ allows you to avoid cumbersome logic inside monitor predicates.

Let's take a look at how reverse monitor specs help us to patch the loopholes described above:

1. Overlooked side effects: a reverse monitor will detect _all_ changes to the monitored state, no matter where they originate.
2. Side effects introduced during system evolution: same as above. Additionally, if an effect monitor is configured to revert in case of unexpected effects taking place, the developers will be forced to keep the spec in sync with the implementation.
3. Inconsistent / spread-out specs: An effect monitor may describe all effects that may happen wrt. a particular state component in one place. As this monitor will be triggered when any of the methods that modify the state is executed, this also brings us considerable savings in terms of spec size/complexity, as similar effects can be grouped together.
4. Unrestricted access from other contracts/methods: as in 1. and 2., it doesn't matter again where the modification comes from: if the state component we monitor is being changed, the monitor will detect it.


### Reverse monitors for the Timelock contract

We apply the general structure of reverse monitors to the [Timelock contract][timelock]; below we depict only the structure of Timelock's reverse monitors (we omit `Monitor<Trigger|Effect>` as well as the monitor names for clarity). 

![Timelock reverse monitors](/img/TimelockReverseMonitors.png)

Timelock's reverse monitors are not specific to the smart contract methods, but rather formulate two important completeness conditions: 

- _"Timelock's balance record is allowed to be updated only by `deposit` or `claim` methods"_: see the complete specification in file [balance_record.tla][balance_record]. 
- _"Timelock's contract balance in the deposited token is allowed to be reduced only by `claim` method"_: see the complete specification in file [token_balance.tla][token_balance]. 

Having these conditions in place does indeed make the combination of Timelock's direct and reverse monitors, which we call a _hybrid monitor_, complete both wrt. deficiencies in direct monitor specifications, and wrt. future code changes. 

-----

We will soon expand this blog post series with the final one, _"The Rise of Model Checker: Verifying Blockchain Monitors In and Near Realtime"_, where we will address these important questions: _"How to verify monitor specs, and what is the verification complexity?"_, as well as _"How to practically check them on the live blockchain?"_ Stay tuned!


_Development of Solarkraft was supported by the [Stellar Development Foundation][] with a generous Activation Award from the [Stellar Community Fund][] of 50,000 USD in XLM._



[Solarkraft]: https://github.com/freespek/solarkraft
[part1]: https://thpani.net/2024/06/why-smart-contract-bugs-matter-and-how-runtime-monitoring-saves-the-day-solarkraft-1/
[part2]: https://thpani.net/2024/06/small-and-modular-runtime-monitors-in-tla-for-soroban-smart-contracts-solarkraft-2/
[part3]: https://protocols-made-fun.com/solarkraft/2024/06/19/solarkraft-part3.html
[part4]: https://systems-made-simple.dev/solarkraft/2024/06/24/solarkraft-hybrid-monitors.html

[Igor Konnov]: https://konnov.phd
[Jure Kukovec]: https://www.linkedin.com/in/jure-kukovec/
[Andrey Kuprianov]: https://www.linkedin.com/in/andrey-kuprianov/
[Thomas Pani]: https://thpani.net

[Soroban]: https://stellar.org/soroban
[Stellar Community Fund]: https://communityfund.stellar.org
[Stellar Development Foundation]: https://stellar.org/foundation

[Stellar]: https://en.wikipedia.org/wiki/Stellar_\(payment_network\)
[TLA+]: https://en.wikipedia.org/wiki/TLA%2B

[SEP-41 token contract]: https://github.com/stellar/stellar-protocol/blob/master/ecosystem/sep-0041.md
[soroban-examples]: https://github.com/stellar/soroban-examples/blob/f595fb5df06058ec0b9b829e9e4d0fe0513e0aa8/timelock/src/lib.rs
[timelock]: https://github.com/stellar/soroban-examples/blob/f595fb5df06058ec0b9b829e9e4d0fe0513e0aa8/timelock/src/lib.rs
[deposit]: https://github.com/freespek/solarkraft/blob/cf26a544ab204220eab62a3545300cb689aa899b/doc/case-studies/timelock/deposit.tla
[claim]: https://github.com/freespek/solarkraft/blob/cf26a544ab204220eab62a3545300cb689aa899b/doc/case-studies/timelock/claim.tla
[balance_record]: https://github.com/freespek/solarkraft/blob/cf26a544ab204220eab62a3545300cb689aa899b/doc/case-studies/timelock/balance_record.tla
[token_balance]: https://github.com/freespek/solarkraft/blob/cf26a544ab204220eab62a3545300cb689aa899b/doc/case-studies/timelock/token_balance.tla


[Runtime verification]: https://en.wikipedia.org/wiki/Runtime_verification
[TLA+]: https://en.wikipedia.org/wiki/TLA%2B
[Timelock contract]: https://github.com/stellar/soroban-examples/blob/v20.0.0/timelock/src/lib.rs
[SCF 24 submission example]: ./scf24/example/README.md
[ERC-721 Certora spec]: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/255e27e6d22934ddaf00c7f279039142d725382d/certora/specs/ERC721.spec
[ERC-721 implementation]: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/255e27e6d22934ddaf00c7f279039142d725382d/contracts/token/ERC721/ERC721.sol
[Timelock monitor spec]: ./case-studies/timelock/timelock_monitor.tla


