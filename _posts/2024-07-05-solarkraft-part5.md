---
layout: post
title: "The Rise of Model Checker: Verifying Blockchain Monitors In and Near Realtime (Solarkraft #5)"
date: 2024-07-19
math: true
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

**» This guest post by [Andrey Kuprianov][] first appeared [on his blog][part5].**

_Solarkraft has been developed in collaboration by [Igor Konnov][], [Jure Kukovec][], [Andrey Kuprianov][] and [Thomas Pani][]._

_This is the fifth and last in a series of blog posts introducing [Solarkraft][], a TLA+-based runtime monitoring solution for [Soroban smart contracts][Soroban]. The first post,_ ["A New Hope – Why Smart Contract Bugs Matter and How Runtime Monitoring Saves the Day"][part1] _gives an overview of smart contracts, explains how traditional security fails to address major challenges in securing crypto assets, and introduces runtime monitoring as a solution. The second post,_ ["Guardians of the Blockchain: Small and Modular Runtime Monitors in TLA+ for Soroban Smart Contracts"][part2] _introduces the language of Solarkraft monitors. The third post,_ ["How to Run Solarkraft"][part3] _gives an overview of the various features of Solarkraft, and explains how to use each one, step-by-step. The forth post,_ ["The Force Awakens: Hybrid Blockchain Runtime Monitors"][part4] _defines and explores the distinctions between direct and reverse blockchain monitors, which together form what we call hybrid monitors._

In this post we first formally define what hybrid blockchain runtime monitors are (from the formal methods point of view), as then proceed to explore the far-reaching avenues of how to go from _offline monitoring_, as done now in Solarkraft, to truly _online monitoring_ on the live blockchain.


## Verifying Runtime Monitors on a Blockchain 📒

After reading the [previous post on hybrid blockchain monitors][part4] you may say: "All that is nice and good, but here are a few questions that still need to be addressed..." For people with different backgrounds these are probably the main ones:

- 🕴CEO / CTO: "Huh? Formal methods? _Why do I need yet another monitoring solution?_ I already have the X/Y/Z system, and they send me real-time alerts!"
- 🤓 Formal methods person: "How do you _verify_ blockchain monitor? What are your _verification conditions_?"
- 👨‍🏫 Mathematician: "What about _verification complexity_?"
- 🧔 Software engineer: "How do you _practically check_ them on the live blockchain?"

This blog post outlines the answers to the above questions. **TL;DR**:

- Formal methods-based blockchain monitors offer a unique combination of _conciseness_ and _completeness_: formal monitor specifications are extremely compact, but, at the same time, they allow to completely specify and differentiate valid/invalid transactions, and to detect and prevent a wide range of potential errors or exploits, which are out of reach of traditional alert-based monitoring solutions.
- We verify blockchain monitors via a) producing verification conditions from each monitor specification; b) extracting pre- and post-states for every relevant blockchain transaction, as well as its parameters; c) validating each transaction against verification conditions using the [Apalache][] model checker.
- Complexity of verifying blockchain monitors is _linear_ wrt. the number of conditions in the specification and the number of transactions: each condition is checked _at most once_ against every transaction (but many checks may be skipped/optimized away). On the other hand, the inherent logical complexity of checking _individual verification conditions_ is highly dependent on their nature, and may be both very low and very high; _it depends_. We do propose below some ways to combat this complexity, exploiting for that the modular nature of our monitors.
- Practically, _in the current [Solarkraft system][Solarkraft]_, we verify blockchain monitors in _offline mode_ by first downloading transactions using `solarkraft fetch`, and then verifying them using `solarkraft verify`; as this doesn't allow to execute preventive measures, we want to move eventually into verifying monitor specifications on the live blockchain, i.e. we want to do _online monitoring_. There may be several intermediate-strength solutions to that problem, which we outline below.

Caught your attention? Do you want a monitoring solution for your blockchain project? <a href="mailto:andrey@kuprum.xyz">Give us a ping!</a> We are always happy to talk to you:)

Are you interested in more details? Then continue reading!

## Formal Blockchain Monitors are Super-Powerful 🦸

In this section we answer the question from an imaginary CEO/CTO:
> "Huh? Formal methods? Why do I need yet another monitoring solution? I already have the X/Y/Z system, and they send me real-time alerts!"

As a general intro into the usefulness of runtime monitoring for blockchains we recommend the first episode from our blockchain series: ["A New Hope – Why Smart Contract Bugs Matter and How Runtime Monitoring Saves the Day"][part1]. But from the question we conclude that our CEO is already convinced that monitoring is useful, and is even using some other monitoring solution. So, **why do we need formal methods-based blockchain monitors?**

To answer that question, **let's see what a typical blockchain monitoring solution offers:**

- receive real-time alerts and notifications about blockchain events
- understand usage patterns and fund flows with customized dashboards
- visualize funding patterns, track wallets, report fraudulent activity
- understand the risk of a transaction; simulate its outputs in real time.

Typically, some or all of the above activities can be parameterized, e.g. wrt. the addresses, or kinds of transactions, or amounts of funds, etc., which gives these systems a certain level of flexibility. Still, a typical monitoring system suffers from two main drawbacks:

- Prevention techniques offered by typical  monitoring systems are most often incomplete: it is impossible to describe by any fixed set of rules the correctness conditions for an arbitrary smart contract.
  - When attempts are made within standard monitoring systems to improve their completeness, these attempts usually lead to proliferation of more and more complex pattern-based rules, which are cumbersome to create and maintain, while still never achieving the necessary completeness level.
- "Real-time alerts" happen post-factum, when the transaction has already committed its changes. This is already too late: receiving a notification that funds have been withdrawn doesn't help returning them.
  - Some systems try to prevent harmful events by using throttling, i.e. limiting the amounts of fund transfers within a period of time. While helping to mitigate the harmful effects to some degree, these solutions are also unsatisfactory for two reasons: a) they can still be side-stepped (e.g. by decreasing the withdrawal speed, or using intermediaries); b) throttling restrictions lead to frustrating experience for legitimate users.

Notice that the first problem (_monitoring incompleteness_) is exactly the reason for the second problem (_post-factum response_, _lack of harm prevention_): without being sure that we have described all possible valid/invalid cases, we can't really be sure to revert a transaction, even if we suspect it being harmful.

**Here is where formal methods-based blockchain monitoring comes to save the day.** Formal methods offer a mathematical logic-based solution which allows in many cases to _completely specify and differentiate valid/invalid transactions_. Moreover, using such decades-proven specification languages as [TLA+][] helps to do it very compactly, and employing such powerful symbolic model checkers as [Apalache][] allows us to check formal specifications extremely fast, in fractions of a second. 

**We plan to seamlessly integrate complete validation of transactions against monitor specifications directly into the transaction execution lifecycle.** With our current [Solarkraft system][Solarkraft] we have made the first step towards this ultimate goal of _online blockchain monitoring_; in the subsequent sections we elaborate in more details about the technical details, as well as the next steps towards our goal.


## Blockchain Monitors in Formal Attire 👔

In this section we define, using mathematical notation, what blockchain monitors are, and how to verify whether a blockchain transaction satisfies the conditions expressed by a monitor.

Formally, a blockchain is a sequence of _ledgers_, where each ledger is a snapshot of the blockchain _environment_ and the blockchain _state_. States are partitioned: first into separate spaces per contract, and then into separate regions per contract variable. Blockchain states are mutated by _transactions_, where each transaction is an invocation of a certain contract _method_ with the corresponding method parameters supplied. The invoked method modifies the states according to its logic. A successful transaction bring the blockchain from one environment/state to the next; a rejected/reverted transaction leaves the blockchain environment/state unchanged. We assume that unsuccessful transactions can be still observed.

We employ the following notation:

- $$D$$ is the set of all possible data values: strings, numbers, structs, etc. Mathematically we don't distinguish between different data types (though practically we of course do).
- $$V$$ is the set of typed contract variables. At this stage we don't distinguish between states of different contracts: logical assertions may refer to the state of any contract (e.g. to token balances in other contracts).
- $$S = S_0, S_1, ...$$ is a sequence of states.
- $$S_i \subseteq V \mapsto D$$ is the $$i$$-th contract state, which is a partial mapping from variables to their data values. If a variable $$v$$ is present in the mapping $$S_i$$, we say that it is _defined_ in this state.
- $$T = T_0, T_1, ...$$ is a sequence of transactions. Each transaction brings the contract into its next state, which we denote by $$S_i \xrightarrow{T_i} S_{i+1}$$.
- $$P_T$$ is the set of all possible typed method parameters.
- $$T_i \subseteq P_T \mapsto D$$: each transaction is a method invocation, represented by a partial mapping from method parameter names to their values; only the parameters specific to the invoked method are present in the mapping.
- $$E = E_0, E_1, ...$$ is the blockchain environment, which is a sequence of environment states; each transaction executes in a specific environment state.
- $$P_E$$ is the set of all typed environment parameters (such as `current_contract_address`, `ledger_timestamp`, or `method_name`).
- $$E_i: P_E \mapsto D$$ is a mapping from environment parameters to their values, and defines the current blockchain environment, in which $$T_i$$ executes.
- $$X_i \in \mathbb{B} = \{ \top, \bot \}$$ is the result of executing the transaction $$T_i$$: $$\top$$ in case of success, $$\bot$$ in case of failure.

The above definitions describe the structure of the object to which we apply monitor specifications: a smart contract, executing on a blockchain. Now it's time to define the structure of monitor specifications themselves. As checking each direct method specification or reverse effect specification is independent from others, we define only the structure for individual monitors.

- $$M_D = \langle F, P, H \rangle$$ is a direct method monitor specification, where the components are the finite sets of `MustFail`, `MustPass`, and `MustHold` conditions respectively.
- $$M_R = \langle C, A \rangle$$ is a reverse effect monitor specification, where the components are the finite sets of `MonitorCheck` and `MonitorAssert` conditions respectively.

In the above:

- For any $$F_j \in F$$, $$P_k \in P$$ we have $$F_j, P_k: (E_i, S_i, T_i) \mapsto \mathbb{B}$$ are boolean conditions of the environment state, the past contract state, and the method parameters.
-  For any $$H_j \in H$$ we have $$H_j: (E_i, S_i, T_i) \times S_{i+1} \mapsto \mathbb{B}$$ are boolean conditions of the environment state, the past contract state, the method parameters, and the next contract state.
- For any $$C_j \in C$$, $$A_k \in A$$ we have $$C_j, A_k: (E_i, S_i) \times S_{i+1} \mapsto \mathbb{B}$$ are boolean conditions defined over the environment state, the past contract state, and the next contract state.

### Verification Conditions for Blockchain Monitors

_Verification conditions_ are verifiable mathematical statements, which encode a certain aspect of the system correctness; in our case they encode whether the blockchain transaction is correct wrt. the blockchain monitor. Having formally defined what are blockchain states, transactions, and monitors, we are now in a position to specify monitor verification conditions.

**For a direct blockchain monitor** $$M_D = \langle F, P, H \rangle$$, we combine individual monitor conditions into larger ones:

$$\mathbb{C}_{\mathit{Fail}} = \bigvee_{j}{F_j}$$

$$\mathbb{C}_{\mathit{Pass}} = \bigvee_{j}{P_j}$$

$$\mathbb{C}_{\mathit{Hold}} = \bigwedge_{j}{H_j}$$

Given the above combined conditions, we check these verification conditions:

| Name | Verification condition |
| -----| ---------------------- |
| Must fail | $$\mathbb{C}_{\mathit{Fail}}  \implies (X_i = \bot)$$ |
| Failure completeness | $$(X_i = \bot) \implies \mathbb{C}_{\mathit{Fail}}$$ |
| Must succeed | $$\neg \mathbb{C}_{\mathit{Fail}} \wedge \mathbb{C}_{\mathit{Pass}} \implies (X_i = \top)$$ |
| Success completeness | $$(X_i = \top) \implies \neg \mathbb{C}_{\mathit{Fail}} \wedge \mathbb{C}_{\mathit{Pass}}$$ |
| Method correctness  | $$(X_i = \top) \implies \mathbb{C}_{\mathit{Hold}}$$ |

Compare these formal verification conditions with the [informal conditions from the previous post][part4directmonitors], as well as with the [TLA+ encoding of verification conditions for Timelock's `deposit` method][depositVCs]. Notice also that the two implications from the pairs "Must fail"/"Failure completeness" and "Must succeed"/"Success completeness" encode together an equivalence between the checks and the transaction execution result. Nevertheless, we consider it a better strategy to treat these conditions separately, as this allows the developers to encode a more fine-grained monitor response. For example, a monitor may forcefully revert a transaction that violates the "Must fail" condition, but only issue a warning when "Failure completeness" is violated.

**For a reverse blockchain monitor** $$M_R = \langle C, A \rangle$$, we also combine individual monitor conditions into larger ones:

$$\mathbb{C}_{\mathit{Check}} = \bigvee_{j}{C_j}$$

$$\mathbb{C}_{\mathit{Assert}} = \bigwedge_{j}{A_j}$$

Reverse monitors encode only a single verification condition:

| Name | Verification condition |
| -----| ---------------------- |
| Effect correctness | $$(X_i = \top) \wedge \mathbb{C}_{\mathit{Check}} \implies \mathbb{C}_{\mathit{Assert}}$$ |

You may compare the above verification condition with the [informal condition from the previous post][part4reversemonitors], as well as with the [TLA+ encoding of verification conditions for the `BalanceRecord` monitor][balanceRecordVCs].


### Model Checking Blockchain Monitors

_Model checking_ is an automatic procedure of verifying mathematical specifications. Within [Solarkraft][], we employ [TLA+][] as our specification language, and [Apalache][] as our model checker. Here are a few details worth noting:

- Apalache is a _general purpose_ model checker, in that it performs _invariant checking_: given an initial system state $$\mathit{Init}$$, an encoding of the system transitions (the _next-state relation_) $$\mathit{Next}$$, and an encoding of a supposed system invariant $$\mathit{Inv}$$, it checks whether the invariant does indeed hold in all system states reachable from the initial one by executing system transitions.
- Apalache is a _bounded_ model checker: it can check invariants only in states reachable in a certain number of transition steps (the execution bound $$\mathit{Length}$$, say 1, 5, or 10) from the initial state.
- Apalache is a _symbolic_ model checker, i.e. it encodes the the verification conditions symbolically, as formulas in certain logical theories, and passes the resulting encoding to _Satisfiability Modulo Theories (SMT) solvers_, which are specialized tools for solving massive volumes of math equations.

_In the current system_ we employ Apalache by encoding monitor verification conditions as a _deadlock checking problem_: we encode the verification condition as part of the next-state relation. Thus, if the verification condition is violated, the system is unable to proceed (there is a deadlock), and this is detected by Apalache. Formally, for any given blockchain environment $$E_i$$, the transaction pre-state $$S_i$$, the transaction being executed $$T_i$$, the transaction execution result $$X_i$$, the transaction post-state $$S_{i+1}$$, as well as any of the above verification conditions $$\mathit{VC}$$, we execute Apalache using the following encoding:

- Initial state: $$\mathit{Init} = E_i \wedge S_i$$
- Next-state relation: $$\mathit{Next} = T_i \wedge X_i \wedge S_{i+1} \wedge \mathit{VC}$$
- Invariant: $$\mathit{Inv} = \top$$
- Execution bound: $$\mathit{Length} = 1$$


A few TLA+ tests for Apalache verification conditions using this encoding can be found e.g. in [deposit_test.tla](https://github.com/freespek/solarkraft/blob/cf26a544ab204220eab62a3545300cb689aa899b/doc/case-studies/timelock/deposit_test.tla) (for the direct monitor of Timelock's `deposit` method), or in [balance_record_test.tla](https://github.com/freespek/solarkraft/blob/cf26a544ab204220eab62a3545300cb689aa899b/doc/case-studies/timelock/balance_record_test.tla) (for the reverse balance record monitor). In all cases Apalache is invoked in a similar fashion, e.g. like that for `deposit`'s first test:

```sh
apalache-mc check --length=1 --init=Init_1 --next=Next_1 deposit_test.tla
```

As explained above, Apalache is a _bounded_ model checker: it can check execution traces up to a certain bound on the execution length. For most systems this restriction starts to manifest itself from the execution depth of around 7 steps: the model checker slows down substantially when exploring execution traces longer than that. But specifically for monitoring this restriction is irrelevant: with the execution length of 1 Apalache is blazing fast, and verifies the above formulas in fractions of a second, so it's a perfect choice for monitoring applications.

In the above tests a monolithic encoding is used: all monitor conditions are encoded as a single invariant, and also included into the next-state relation. This encoding is the compromise we had to make due to the very limited project timeline, and has a few drawbacks:

- All verification conditions are lumped together into a single invariant, and, moreover, the invariant is part of the next-state relation. As a result, when the invariant is violated, the feedback from the model checker is suboptimal: it reports only that the system is unable to proceed (deadlocked), but doesn't explain the reason for that (as no invariant was violated).
- In cases more complex than Timelock, verifying a single large invariant may become way more time-consuming than the sum of times for verifying each individual invariant separately, due to ultimately exponential nature of the resulting logical problem.

In general, we can be more flexible in encoding monitor verification conditions for model checking. E.g. in [another version of Timelock's monitors](https://github.com/freespek/solarkraft/blob/f16a96e22c73aa4bbcb4a2fba56f8a61321db00f/doc/case-studies/timelock/timelock_mon_tests.tla) we encoded one _combined monitor condition_ per invariant. Finally, verification conditions can also be encoded very fine-grained, down to the smallest scale, when an invariant to be checked contains a single direct monitor condition (one of $$F_j$$, $$P_j$$, $$H_j$$), or a single reverse monitor condition (one of $$C_j$$, $$A_j$$). In all those cases, we encode a verification condition $$\mathit{VC}$$ as an _invariant checking problem_ for Apalache in the following way:

- Initial state: $$\mathit{Init} = E_i \wedge S_i$$
- Next-state relation: $$\mathit{Next} = T_i \wedge X_i \wedge S_{i+1}$$
- Invariant: $$\mathit{Inv} = \mathit{VC}$$
- Execution bound: $$\mathit{Length} = 1$$

We then execute Apalache using the following command:

```sh
apalache-mc check --length=1 --init=Init --next=TxRes --inv=VC timelock_mon_tests.tla
```

This encoding solves the aforementioned problems wrt. monolithic encoding: the feedback from the model checker explains in details what is the problem when an invariant is violated; the encoding can also provide substantial improvements in terms of execution speed for monitors which are more complex than Timelock's.




## Practical Checking of Blockchain Monitors 🛠

In the present [Solarkraft system][Solarkraft] we do what's called _offline monitoring_: we verify monitors _after_ the state has already been committed to the blockchain. The delay between the action and the response can be made very small, a few seconds, but due to the final nature of the committed transactions this is not enough: the changes (such as balance transfer) can't be undone. Our eventual goal is to perform _online monitoring_, i.e. to verify the monitors _before_ the state has been committed, in order to be able to do preventive actions. This far-reaching goal is non-trivial, and has a few intermediate-strength solutions, which we are about to explore now.

**Offline monitoring** is is the simplest blockchain monitoring solution, applied both by standard blockchain monitors, as well as by our [current Solarkraft system][Solarkraft]:

- A transaction is committed on the blockchain;
- At some later time point, the transaction effects are observed: `solarkraft fetch`;
- Transaction is validated, and acted upon: `solarkraft verify --alert`.

This approach is useful in that the reaction to the event (a transaction) may happen in _near real time_: a few seconds later. The problem is that for blockchain this is not enough: what matters is the logical state on the blockchain, which, when committed, is irreversible (except for hard forks). Thus, in many cases, the reaction can't prevent the possible harm being done.

To better understand how preventive actions may be done, let's take a look at [Stellar's transaction lifecycle][transaction-lifecycle]. The important points where a monitoring system may intervene in the transaction lifecycle are the steps 3, 7, and 10:

> 1. Creation (Transaction Creator)
> 2. Signing (Transaction Signers)
> 3. **Submitting  (Transaction Submitter): After signing, the transaction can now be submitted to the Stellar network. If the transaction is invalid, it will be rejected immediately by Stellar Core.**
> 4. Propagating (Validator)
> 5. Crafting a candidate transaction set (Validator)
> 6. Nominating a transaction set (Validator)
> 7. **Stellar Consensus Protocol (SCP) determines the final transaction set (Validator Network). SCP resolves any differences between candidate transaction sets and ultimately determines a single transaction set to apply, the close time of the ledger, and any upgrades to the protocol that need to be applied network-wide at the apply time.**
> 8. Transaction apply order is determined (Validator Network)
> 9. Fees are collected (Validator)
> 10. **Application (Validator): Each transaction is applied in the previously-determined order. For each transaction, the account’s sequence number is consumed (increased by 1), the transaction’s validity is rechecked, and each operation is applied in the order they occur in the transaction. Operations may fail at this stage due to errors that can occur outside of the transaction and operation validity checks. For example, an insufficient balance for a payment is not checked at submission and would fail at this time.**
> 11. Protocol Upgrades (Validator)

Why are these steps important? Because exactly at these steps _new information appears, which influences transaction validity_:

- Step 3: the transaction $$T_i$$ is determined: its parameters, signatures, etc.
- Step 7: the blockchain environment $$E_i$$  is determined, in which $$T_i$$ will execute: 
  - the set of transactions which will be executed together with $$T_i$$;
  - $$T_i$$'s ledger number / timestamp;
  - the starting state for ledger's transaction set, which is the end state of the previous ledger.
- Step 10: the starting state $$S_i$$ for transaction $$T_i$$ is determined, which is the result of applying all other transactions preceding $$T_i$$ in the apply order determined at step 8.

_It is worth noting that the order of application determined at step 8 is also a new piece of information, which influences transaction validity (and ultimately determines $$S_i$$). Nevertheless, as steps 8-10 happen essentially at the same time (see [LedgerManagerImpl::closeLedger](https://github.com/stellar/stellar-core/blob/2ba9f8de47faca0b9e3bf3da540f38f15665606b/src/ledger/LedgerManagerImpl.cpp#L894-L906)), this difference in timing is immaterial. For conceptual reasons we prefer to focus on step 10._


When speaking about practicality, timing and throughput parameters start playing an important role:

- Typical Stellar ledger close time: 5-6 seconds
- Stellar transaction throughput (transactions per second, TPS): up to 1000

What does the above mean for validating blockchain monitors? Two things:

- With each step, additional data becomes available; thus more monitor verification conditions (VCs) can be validated:
  - At step 3: _stateless_ VCs can be validated, i.e. those depending only on $$T_i$$;
  - At step 7: _semi-stateful_ VCs, depending only on $$T_i$$ and $$E_i$$ can be validated;
  - At step 10: all _stateful_ VCs can be validated.
- With each step, the timing constraints become more strict (in order not to disrupt the core blockchain functionality):
  - At step 3: any reasonable time (e.g. up to 10 seconds) can be allocated to execute the transaction validity checks;
  - At step 7: a small portion of the ledger close time (e.g. up to 1 second) can be allocated for checking all ledger's transactions;
  - At step 10: a tiny portion of ledger close time (e.g. up to 100 milliseconds) can be allocated for checking all ledger's transactions.

What can [Apalache][] model checker checker offer us in terms of validity checks execution time? For the Timelock example, the typical VC check time is around 1 second on a powerful laptop. Using such features as _Server Mode_ (mostly implemented, see [[FEATURE] Server Mode](https://github.com/informalsystems/apalache/issues/730) and [RFC-010: Implementation of Transition Exploration Server](https://apalache.informal.systems/docs/adr/010rfc-transition-explorer.html)) we expect the startup time (runtime setup, parsing, typechecking, preprocessing) to be amortized for multiple queries, and validity checking time to be reduced to something like 100 milliseconds. This sounds good! But a few problems still exist, unfortunately:

- This is the checking time for a single transaction; but for steps 7 and 10 _all ledger's transactions_ need to be checked. Taking into account the blockchain parameters, this means checking up to 5000 transactions in 1 second (for step 7), or in 100 milliseconds (for step 10).
- The Timelock example is one of the simplest imaginable in terms of its logical complexity. Thus, for more complex examples the checking time can be substantially higher.

Taking all of the above in consideration we have two (mostly independent) strategies of how blockchain monitors can be integrated into the transaction lifecycle: one  from formal methods point of view, and another from blockchain engineering point of view.

### Model Checking Improvements for Blockchain Monitoring

As can be seen from the analysis above, **model checking has to provide hard real time execution guarantees for validity checks**, 
 such as _"up to 5000 transactions can be checked in 100 milliseconds"_. How can this be done? Below are a few ideas on how to achieve that.

**Software engineering improvements**. Features such as Server Mode can substantially reduce startup times, giving up to 10x checking time reduction. This feature is mostly implemented, but still needs some polishing. Another useful feature would be efficient parallelization (also partially implemented): given 5000 transactions, each independently checkable in 100 ms, and being able to execute the checks in parallel, would allow us to execute all ledger's transactions checks in 100 ms.

**Model checking problem decomposition.** Our [hybrid blockchain monitors][part4] are already quite modular, in the sense that each monitor is expressed as a combination of simple conditions. As we explained in the previous sections, the verification conditions can be checked independently for each monitor condition, and then combined at the boolean level. Solving each of the resulting subproblem independently will allow both for parallelization (see above), as well as to use specialized solvers for each subproblem, with different complexity constraints (see below). We could employ the [three-valued logic](https://en.wikipedia.org/wiki/Three-valued_logic) to describe the boolean structure of the overall problem, with the _Unknown_ value expressing that the model checking is not possible with the available information, or didn't terminate within the required hard time bound. Using then logical connectors from the three-valued logic would allow us to provide meaningful answers in some cases when the standard model checking procedure would not terminate.

**Theory-specific solvers for subproblems.** Apalache reduces model checking problem to the QF_NIA logic (Quantifier-free theory of nonlinear integer arithmetic). While being very general and powerful, this theory is in the worst case undecidable. When looking at moderately large model checking problems as a whole (even at Timelock) at least QF_LIA (Quantifier-free theory of linear integer arithmetic) is required, which is a subtheory of QF_NIA with exponential complexity. When looking at subproblems though, simpler theories could be employed; examples of those are QF_EUF (Quantifier-free theory of equality and uninterpreted functions) with the worst-case $$n \cdot \mathit{log}(n)$$ complexity, or QF_IDL (Quantifier-free theory of integer difference logic), with the worst-case cubic complexity. Putting aside record access (which can be abstracted away in some cases) examples of subproblems with reduced complexity in the Timelock case can be found in the [Balance Record monitor](https://github.com/freespek/solarkraft/blob/cf26a544ab204220eab62a3545300cb689aa899b/doc/case-studies/timelock/balance_record.tla#L10-L25), which falls under QF_EUF theory, or [Claim's `MustHold` monitor conditions](https://github.com/freespek/solarkraft/blob/cf26a544ab204220eab62a3545300cb689aa899b/doc/case-studies/timelock/claim.tla#L30-L38), which is expressible in QF_IDL theory.


### Blockchain Engineering for Runtime Monitoring

All of the above model checking improvements are useless if they can't be applied at the right time and place. For that, a proper **integration of monitoring into transaction lifecycle is necessary**, specifically to be able to execute preventive measures when a violating transaction is detected. Based of the transaction lifecycle outlined above, here is how we see this can be done:

**Execute stateless validity checks at transaction submission time**. At step 3, when a transaction is submitted to the blockchain, stateless checks (depending only in $$T_i$$) can be executed; this needs to be done at Stellar Core, as the single controllable point of entry for all incoming transactions. As timing requirements are not too strict at that point, Apalache can be employed as is (only the software engineering improvements would be useful for efficiency reasons).

**Execute semi-stateful validity checks when SCP decides ledger's transaction set**. Semi-stateful checks (depending on $$T_i$$ and $$E_i$$) can be executed at step 7 by the validator network; the timing requirements become moderately strict, so model checking problem decomposition becomes necessary.

**Execute stateful checks when transactions are applied**. This is done by a validator node at step 10, and the timing requirements are the most strict ones, so all model checking improvements become necessary. Inevitably there will be cases when model checking will exceed the timing requirements, returning the _Unknown_ answer, so the monitoring system should be configurable with actions to be executed when this happens. E.g. in the most critical cases a transaction can be reverted; in less critical cases a transaction may be allowed to pass, but an alert will be issued. 


All of the above requires integration of formal-methods based monitoring into the central blockchain components. If this isn't possible for some reason for the whole blockchain, what can a project do in order to implement **individual project monitoring**? Though it's less efficient than the whole-blockchain solution, but a lot can still be done:

**Perform stateless validation of user transactions via a dedicated service**. A project may require its users to submit transactions using `Permit`s via a centralized service, which will perform transaction validation by interacting with the monitoring system. The service, in case of successful checks, will sign and submit transaction to the blockchain. The on-chain components of the system need to be restricted to accept only such transactions which are signed by the service, and also validate user's `Permit` signatures.

**During transaction processing, perform stateful checks via on-chain monitoring system**. An on-chain monitoring system can be implemented which will perform (limited) transaction validation. A project-specific contract, when receiving a transaction, will call into the monitoring system to perform transaction validation. This in turn can be done in two ways:

- Implement on-chain solvers for simple theories such as as QF_EUF or QF_IDL, and validate the transaction within the same call. Some attempts in that direction have been undertaken already for EVM/Solidity, see e.g. the pilot project [EVM Symbolic Execution in Solidity](https://github.com/leonardoalt/dl_symb_exec_sol).
- Accept transaction for validation, log it on-chain, and wait for an off-chain component to validate it. The off-chain component will commit the validation results on-chain, and the on-chain component will forward the result to the project-specific contract. This happens with an inevitable delay of at least 1 ledger: e.g. a transaction is submitted at ledger $$n$$, but validated and executed at ledger $$n+1$$. While slightly less convenient for the user, this allows to side-step hard real time requirements wrt. model checker execution.

-----

This post concludes our blog post series about the first phase of [Solarkraft][] development; we hope you've enjoyed it. Please don't hesitate to <a href="mailto:andrey@kuprum.xyz">write to us</a>: we are happy to hear from you, and discuss everything concerning the fascinating topic of blockchain runtime monitoring!

-----

_Development of Solarkraft was supported by the [Stellar Development Foundation][] with a generous Activation Award from the [Stellar Community Fund][] of 50,000 USD in XLM._



[Solarkraft]: https://github.com/freespek/solarkraft
[Apalache]: https://konnov.phd/portfolio/apalache/
[part1]: https://thpani.net/2024/06/why-smart-contract-bugs-matter-and-how-runtime-monitoring-saves-the-day-solarkraft-1/
[part2]: https://thpani.net/2024/06/small-and-modular-runtime-monitors-in-tla-for-soroban-smart-contracts-solarkraft-2/
[part3]: https://protocols-made-fun.com/solarkraft/2024/06/19/solarkraft-part3.html
[part4]: https://systems-made-simple.dev/solarkraft/2024/06/24/solarkraft-hybrid-monitors.html
[part5]: https://systems-made-simple.dev/solarkraft/2024/07/04/solarkraft-monitor-verification.html
[part4directmonitors]: https://systems-made-simple.dev/solarkraft/2024/06/24/solarkraft-hybrid-monitors.html#direct-monitors
[part4reversemonitors]: https://systems-made-simple.dev/solarkraft/2024/06/24/solarkraft-hybrid-monitors.html#reverse-monitors
[depositVCs]: https://github.com/freespek/solarkraft/blob/cf26a544ab204220eab62a3545300cb689aa899b/doc/case-studies/timelock/deposit.tla#L66-L104
[balanceRecordVCs]: https://github.com/freespek/solarkraft/blob/cf26a544ab204220eab62a3545300cb689aa899b/doc/case-studies/timelock/balance_record.tla#L31-L39
[Igor Konnov]: https://konnov.phd
[Jure Kukovec]: https://www.linkedin.com/in/jure-kukovec/
[Andrey Kuprianov]: https://www.linkedin.com/in/andrey-kuprianov/
[Thomas Pani]: https://thpani.net

[Soroban]: https://stellar.org/soroban
[Stellar Community Fund]: https://communityfund.stellar.org
[Stellar Development Foundation]: https://stellar.org/foundation

[Stellar]: https://en.wikipedia.org/wiki/Stellar_\(payment_network\)
[TLA+]: https://en.wikipedia.org/wiki/TLA%2B

[transaction-lifecycle]: https://developers.stellar.org/docs/learn/fundamentals/transactions/transaction-lifecycle

