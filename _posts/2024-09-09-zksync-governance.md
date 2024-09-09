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
[emergency response procedures][emergency-response]) to ensure formally defined
coverage of the contracts with state invariants.

As a result of our work, we have written over 50 state invariants. All of them
were tried with the randomized simulator of Quint as well as with the symbolic
model checker [Apalache][]. While we do not claim to have achieved a 100%
accuracy in verifying these state invariants, since we were doing bounded model
checking and randomized symbolic execution, we believe that the specification
and model checking activity were quite valuable, for the following reasons:

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

**Security Council**. The `SecurityCouncil` contract responsible for
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

**Guardians**. The Guardians contract safeguards the ZKsync protocol, providing
essential governance functions such as approving upgrades, managing L2
proposals, and extending legal veto periods. This contract also uses a
multi-signature mechanism, requiring a specific number of guardian approvals for
different actions. 

Key functions include:

 - *Upgrade Approval*: Guardians can approve protocol upgrades with 5
 signatures, ensuring a consensus-driven approach to critical changes.
 
 - *Legal Veto Extension*: Guardians can extend the legal veto period for L1
 upgrade proposals with just 2 signatures, adding a layer of security. 
 
 - *L2 Proposal Management*: Guardians can propose and cancel L2 governance
 proposals, requiring 5 signatures. The contract uses EIP-712 for secure and
 verifiable signature handling, preventing unauthorized actions. Each proposal
 or veto action is recorded with a unique nonce to protect against replay
 attacks, ensuring that every decision is unique and intentional.

**Emergency Upgrade Board**. The `EmergencyUpgradeBoard` contract
facilitates emergency protocol upgrades through a coordinated process involving
three critical entities: the Security Council, Guardians, and the ZK Foundation.
Each entity must provide multi-sig approval for any emergency upgrade to
proceed, ensuring consensus among key stakeholders. The contract leverages
EIP-712 for secure and verifiable signature handling, defining specific type
hashes for each group's approval process. Upon receiving the necessary
signatures, the contract validates them against the specified type hashes. If
all approvals are verified, the contract delegates the upgrade execution to the
`ProtocolUpgradeHandler`.  

**Protocol Upgrade Handler**. The ProtocolUpgradeHandler is a backend contract
that manages the upgrade process for the ZKsync protocol. It holds ownership of
all ZKsync contracts on both L1 and L2, ensuring that upgrades follow a secure
and structured process.  The contract also manages emergency actions, such as
protocol freezes and self-upgrades.The upgrade process involves several stages:
proposal, legal veto, approval, pending, and execution:

 - Proposal: Delegates propose a protocol upgrade by sending a special message
 initiating the upgrade process.
 
 - Legal Veto Period: Guardians can veto the upgrade within a 3-day period,
 extendable to 7 days.
 
 - Approval: Requires approval from the Security Council or Guardians. The
 Security Council can approve immediately, while Guardians’ approval requires a
 30-day waiting period.
 
 - Pending: A mandatory delay before execution allows for final preparations.
 
 - Execution: The approved changes are executed, completing the upgrade process.
 
## 3. Modeling the Protocol

We use [Quint][] to produce an [executable specification][zksync-gov-spec] of
the [ZKsync Governance contracts][zksync-gov-contracts] in Solidity, and write
several basic tests to check that the specification doesn’t have trivial coding
bugs and typos. Since Quint is a relatively general specification language,
which stems from TLA+, it does not offer built-in primitives for modeling
Solidity and EVM. Hence, to model the governance protocol, we need to create
adequate reference models for the following primitives and mechanisms of the EVM
smart contracts:

 - Contract inheritance,
 - Multisig,
 - Cryptographic signatures,
 - Hashing, e.g., Keccak256,
 - EVM Calls.

**Modeling inheritance.** In the reference implementation, two of the most
important contracts from a modeling perspective are `SecurityCouncil` and
`Guardians`.  They inherit from `Multisig` and `EIP712`. Since Quint does not
support inheritance natively, we manually emulated it by calling all necessary

For example, to create a new instance of `SecurityCouncil` we have to first
directly create a new instance of `Multisig` for it:

```quint
pure def newSecurityCouncil(_members: Set[Address]): Result[SecurityCouncilState] = {
  pure val multisig = newMultisig(_members, 9)
  pure val empty = {
    multisig: multisig.v, softFreezeThreshold: 0, softFreezeNonce: 0,
    hardFreezeNonce: 0, softFreezeThresholdSettingNonce: 0, unfreezeNonce: 0
  }
  if (isOk(multisig)) {
    pure val membersSize = _members.size()
    pure val e = require(membersSize == 12,
      "SecurityCouncil requires exactly 12 members")
    if (e != "") {
      err(empty, e)
    } else {
      ...
    }
  } else {
    err(empty, multisig.err)
  }
}
```

**Modeling multisig mechanics.** The ZKsync Governance Protocol is based on
2-layer multi-sig contracts: Guardians and Security Council are multi-sig
contracts, and each their member (body) is also a multi-sig contract. We
implemented a separate module for multi-sig that instantiates mechanics with the
necessary thresholds and implemented three methods to check signatures. The
implementation can be found in [multisig.qnt][]. Notably, we have simplified the
model related to [ERC-1271][]. So, in the specification multi-sig module
implements the method `isValidSignatureNow` which is a wrapper around the method
`isValidSignature`.

```quint
/// @dev The function to check if the provided signatures are valid and meet predefined threshold.
/// @param _digest The hash of the data being signed.
/// @param _signature An array of signers and signatures to be validated ABI encoded from `address[], bytes[]` to `abi.decode(data,(address[],bytes[]))`.
pure def isValidSignature(self: MultisigState, _digest: AbiEncoded, _signature: Set[Signature]): Bytes4 = {
    pure val err = self.checkSignatures(_digest, _signature.map(s => s.signer), _signature, self.EIP1271_THRESHOLD)
    if (err != "") err
    else EIP1271_MAGICVALUE
}

/// @dev Should return whether the signature provided is valid for the provided data
/// @param hash      Hash of the data to be signed
/// @param signature Signature byte array associated with _data
pure def isValidSignatureNow(self: MultisigState, _digest: AbiEncoded, _signature: Set[Signature]): bool = {
        isValidSignature(self, _digest, _signature) == EIP1271_MAGICVALUE
}
```

**Modeling signing and hashing.** As is typical for smart contracts in Solidity,
the ZKsync governance contracts are extensively using the hash function
`keccak256` to compute message digests. In particular, these digests are used in
the EIP-721 signature verification (see above). In addition to that, the
contracts also call `abi.encode` and `abi.decode` to pack and unpack data
structures into/from arrays of bytes, respectively. If we were to specify the
behavior of these functions directly, we would have to implement plenty of
arithmetic computations in Quint.  As we use symbolic execution and
satisfiability-modulo-theory solvers to analyze the protocol specification, we
have to avoid heavy arithmetic computations. It is well-known that SMT solvers
are slowing down on complex arithmetic constraints very quickly. Hence, we
have to avoid the actual cryptographic implementations of hashing, be it the
actual implementations or simplified ones.  Fortunately, we can draw inspiration
from classic security research such as the [Dolev-Yao model][].

In Dolev-Yao, encryption and decryption functions `encrypt` and `decrypt` are
symbolic and uninterpreted in the sense that the main property of these
functions is as follows: `decrypt(encrypt(M)) = M`, for an arbitrary message
`M`. In a similar spirit, we could treat a hash function symbolically, that is,
require that `hash(M1) = hash(M2)` if and only if `M1 = M2`. This is a cool
idea: We don’t have to explain to the solver how real-life cryptography works
but rely on a few simple axioms.

One issue that stops us from naively implementing Dolev-Yao in Quint is the
Quint’s type system. First, Quint does not support uninterpreted functions.
Second, even if it did, we would have to deal with the fact that the messages
have plenty of different types. Interestingly, this would not be an issue in an
untyped specification language such as TLA<sup>+</sup>. Fortunately, we do not
have to specify the behavior of hashing for arbitrary messages. We only have to
do it for the kinds of messages that are mentioned in the ZKsync contracts.
There are not so many, actually. As a result, we define the shape of the
hashable messages with `AbiElem` and `AbiEncoded`:

```quint
    type AbiElem =
      AbiStr(str) | AbiInt(int) |
      AbiUpgradeProposal(UpgradeProposal) | AbiL2Proposal(L2GovernorProposal)
    type AbiEncoded = List[AbiElem]
```


[Dolev-Yao model]: https://en.wikipedia.org/wiki/Dolev%E2%80%93Yao_model
[multisig.qnt]: https://github.com/zksync-association/zk-governance/blob/master/spec/multisig.qnt
[ERC-1271]: https://eips.ethereum.org/EIPS/eip-1271
[Quint]: https://quint-lang.org
[Apalache]: https://apalache-mc.org
[zksync-gov-spec]: https://github.com/zksync-association/zk-governance/tree/master/spec 
[zksync-gov-contracts]: https://github.com/zksync-association/zk-governance/tree/master/l1-contracts
[zksync-gov]: https://docs.zknation.io/zksync-governance/zksync-governance-procedures-overview
[emergency-response]: https://docs.zknation.io/zksync-governance/schedule-2-emergency-response-procedures
[chonky-quint]: https://protocols-made-fun.com/consensus/matterlabs/quint/specification/modelchecking/2024/07/29/chonkybft.html
[Igor Konnov]: https://konnov.phd
[Matter Labs]: https://matter-labs.io/