---
layout: post
title: "Specification and Model-checking of the ZKsync Governance Protocol"
date: 2024-09-09
categories: zksync matterlabs quint specification modelchecking
quint: true
math: true
---

**Authors: Denis Kolegov ([Matter Labs][]), [Igor Konnov][]**

After our success in [specification and model checking of the ChonkyBFT
consensus][chonky-quint] in Quint, we have decided to apply Quint and its tools
to a slightly different domain: governance contracts in Solidity. This blogpost
summarizes our experience and highlights the important modeling decisions we
made.

## 1. Introduction

[ZKsync Governance][zksync-gov] is a protocol that allows governance bodies
(members), such as the ZKsync Security Council and Guardians, to manage ZKsync
through regular and emergency procedures. The ZK token serves as the
governance token for voting. The ZKsync Governance Procedures are maintained by
the ZKsync Association and are updated to reflect any changes to the underlying
smart contracts and on-chain mechanisms. They are intended as a
high-level overview rather than a comprehensive guide.

The ZKsync governance smart contracts have been previously tried by well-known
researchers in the field, who reported several vulnerabilities. When writing the
formal specification, one of our goals was to see whether we could triage some
of these reports and reproduce the vulnerabilities with the model checker.
Another goal was to use the legal documents (especially devoted to the
[emergency response procedures][]) to ensure formally defined coverage of the
contracts with state invariants.

As a result of our work, we have written over 50 state invariants. All of them
were tried with the randomized simulator of Quint as well as with the symbolic
model checker Apalache. While we do not claim to have achieved a 100% accuracy
in verifying these state invariants, since we were doing bounded model checking
and randomized symbolic simulation, we believe that the specification and model
checking activity was quite valuable, for the following reasons:

1. While writing the Quint specification, we have identified a few fragments of
the Solidity code that could be improved, though they were not directly
exploitable.

1. While writing the state invariants and discussing them with the parties
involved, we raised questions about the properties that led to further
improvement of the freezability logic.

1. We have reproduced several of the reported scenarios with the model checker
and, for some of the scenarios, we showed that they were not reproducible in our
specification.

1. We have found that the legal documents of ZKsync governance were
“verification-friendly”. It was relatively easy to translate many clauses from
those documents into state invariants.

In this blogpost, we highlight the non-trivial parts of our specification
process using Quint, overcoming challenges such as the lack of built-in
primitives for Solidity and EVM. We created reference models for critical
contract mechanisms, including multi-sig operations, cryptographic signatures,
and EVM calls, and validated these models through symbolic model checking with
SMT solvers.

## 2. Overview of the ZKsync Governance Protocol

The ZKsync Governance Protocol is structured around a governance system with
four distinct voting classes:

 - Token Assembly: Comprised of ZK tokenholders, who delegate the voting power
 of ZK tokens they hold to ZKsync addresses in order to (indirectly) participate
 in the ZKsync governance system.
 
 - ZK Foundation: A privileged supporting entity.

 - Guardians: A group of 5 to 8 actors with administrative privileges.
 
 - Security Council: A group of 9 to 12 actors with administrative privileges.
 
The key characteristics of this governance system include:

 - Any proposal from the Token Assembly requires approval from either the
 Guardians or the Security Council to proceed.
 
 - In collaboration, the ZK Foundation, Guardians, and Security Council can
 initiate an emergency upgrade.
 
 - The Security Council can freeze the ZKsync protocol in case of an emergency.
 
 - Guardians have the independent power to veto proposals.

In our research, we have modeled the L1 contracts in Solidity that can be found
in the [following GitHub repository][zksync-gov-contracts]. We give a brief overview
of the contracts below.

**Multisig**. The Multisig contract is an abstract implementation of a multi-sig
wallet, allowing a group of governance bodies to authorize actions collectively
by meeting a predefined signature threshold. It uses EIP-1271 for secure
signature verification, requiring signatures from unique members in a sorted
order. The contract ensures that the number of signatures meets or exceeds the
required threshold before validating them against the list of authorized
members. If the signatures are valid, the action is authorized, enabling secure
collective decision-making within a decentralized environment.

**Security Council**. The SecurityCouncil is a contract responsible for
communication with the security experts of the ZKsync protocol. It operates as a
multi-sig wallet with 12 members and handles critical functions such as
approving protocol upgrades, initiating protocol freezes, and unfreezing the
protocol when necessary.

Key Functions:

 - *Upgrade Approval*: Requires 6 signatures to approve protocol upgrades,
 ensuring consensus among security experts.
 
 - *Soft Freeze*: Initiated by a smaller threshold of council members (default
 of 3 signatures), temporarily halting protocol changes.
 
 - *Hard Freeze*: 9 signatures are required to trigger a full protocol freeze.
 
 - *Unfreeze*: It also requires 9 signatures to unfreeze, resuming normal
 protocol operations.
 
 - *Threshold Management*: The council can adjust the soft freeze threshold,
 with changes requiring 9 signatures and expiring after a set period.

Each function call is secured using EIP-712 signatures, ensuring only authorized
members can initiate critical security functions.


[zksync-gov-contracts]: https://github.com/zksync-association/zk-governance/tree/master/l1-contracts
[zksync-gov]: https://docs.zknation.io/zksync-governance/zksync-governance-procedures-overview
[emergency-response]: https://docs.zknation.io/zksync-governance/schedule-2-emergency-response-procedures
[chonky-quint]: https://protocols-made-fun.com/consensus/matterlabs/quint/specification/modelchecking/2024/07/29/chonkybft.html
[Igor Konnov]: https://konnov.phd
[Matter Labs]: https://matter-labs.io/