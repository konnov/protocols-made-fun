---
layout: post
title: "A New Hope – Why Smart Contract Bugs Matter and How Runtime Monitoring Saves the Day (Solarkraft #1)"
date: 2024-06-14
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

![]({{ site.baseurl }}/img/solarkraft.png)

» **This guest post by [Thomas Pani][] first appeared [on his blog][part1].**

_In this series of blog posts, we introduce [Solarkraft][], a TLA+-based runtime monitoring solution for [Soroban smart contracts][Soroban]. We will start easy, with an overview of smart contracts, their principal vulnerabilities, and the traditional model of securing smart contracts, and an overview of how Solarkraft proposes a new solution._  
_The following posts dive deeper into Soroban and Solarkraft, how to write TLA+-based runtime monitors in Solarkraft, and the more technical parts of our unique runtime monitoring solution (modular and hybrid runtime monitors)._

_Solarkraft has been developed in collaboration by [Igor Konnov][], [Jure Kukovec][], [Andrey Kuprianov][] and [Thomas Pani][]._

Since the advent of smart contract-enabled blockchains like [Ethereum][] and [Stellar][], smart contracts have become the power engines underlying decentralized applications (dApps) on blockchains. These self-executing contracts are computer programs that automate digital agreements and transactions, enabling trustless interactions without the need for intermediaries. Smart contracts hold immense potential for transforming various industries, from finance to supply chain management. However, a hidden vulnerability lurks within these powerful tools: software bugs. 🐛

## The High Cost of Tiny Errors

Unlike traditional software, smart contracts are **immutable** after deployment. So even if a vulnerability is found, it is impossible to patch a smart contract on the fly. In addition, a smart contract transaction **cannot simply be undone**. Once it has taken place, it is permanently recorded on the blockchain. Nowadays, it is very unlikely that blockchain validators would agree to halt the entire blockchain to allow the contract authors to remedy the issue (as they did years ago for the _DAO Hack_ – see below).

Smart contract immutability and blockchain finality are a double-edged sword. While they guarantee tamper-proof execution, it also means that patching a bug or reverting a malicious transaction after the fact is impossible. Thus, a single error in a smart contract often has **devastating consequences**:

- **Financial Losses:** Hackers can exploit vulnerabilities to steal cryptocurrency or other valuable assets locked within smart contracts. In 2016, the infamous _DAO Hack_ [resulted in the loss of over $60 million worth of ETH][DAO Hack] and lead to the controversial hard fork of Ethereum at block 192,000.  
More recently, in March 2023, an unknown attacker targeted [Euler Finance][Euler Finance hack], a permissionless borrowing and lending protocol on Ethereum, and stole assets worth $200 million from its flashloan protocol.

- **Service Disruption & Frozen Funds:** Bugs can render the entire dApp unusable, causing unrecoverable financial losses and severe reputational damage for the project. For example, in 2017 a bug in the Parity multisig wallet contracts [froze over $300 million worth of funds][Parity hack] – 1% of the total valuation of ETH at the time. One year after the DAO Hack, introducing another hard fork had become inconceivable.  
Denial-of-service attacks slow down or interrupt service altogether; for example, the Manta Networks launch earlier this year was [interrupted by a DDoS attack during token issuance][Manta attack].

- **Systemic risks**: As DeFi protocols are becoming more and more interconnected, a single bug can trigger a domino effect, impacting other protocols or entire ecosystems. In October 2021, the Cream Finance DeFi protocol was subject to a [series of flash loan attacks][Cream Finance hack], losing $130 million in various cryptocurrencies. Attackers exploited a vulnerability in the way Cream Finance interacted with price oracles to borrow a large amount of funds, essentially for free. This inflated the price of the borrowed assets and triggered liquidations for other users, ultimately draining millions of dollars from the protocol.

Isolated incidents? Sadly no, as [this list of recent DeFi hacks](https://rekt.news/) shows.

The combination of risks above emphasizes the critical need for thorough security practices during the entire development lifecycle of smart contracts.

## The Traditional Model of Securing Smart Contracts

Traditionally, securing smart contracts has targeted individual stages of the development life cycle:

![]({{ site.baseurl }}/img/solarkraft-traditional_security.png)

- **Development**: Like other software, smart contracts are first coded by an individual developer or a team of developers. Solid developers will write unit and perhaps integration tests (advanced developers may use [fuzz tests][]). All of this happens in a development environment that does not reflect the final production environment.

- **Staging & Testing**: The team will deploy the contracts to a production-like environment, the "testnet". The main strategy here is manual testing of the deployed code (obviously, this is prone to missing important bugs). Experienced teams will automate their testing with integration and end-to-end tests.

- **Pre-release Security Audit**: Before going live, security-conscious teams will order one or multiple [security audits][Audits] from either an audit firm, independent auditors, or a [contest platform][Audits]. These auditors perform a manual code review of a fixed commit of the source code. Extremely experienced auditors may do some fuzzing or formal modeling, though most providers skip these advanced techniques to keep their time investment low. (Not sure which kind of audit is best for you? [Reach out][Contact]!)

- **Deployed on mainnet**: After all the vulnerabilities discovered during testing and auditing have been patched, the smart contracts are ready to go live on mainnet! Your funds are secure, right? Well, as we've seen above – perhaps not. They now have to withstand the attacks of persistent, creative, and destructive attackers. Hopefully, the development team has put some monitoring and [circuit breaker functionality][circuit breaker] in place?

---

The team behind Solarkraft has experience **securing all stages of blockchain and smart contract development**. We understand the full stack from consensus-layer protocols to smart contracts, have worked in **multiple ecosystems**, and bring experience in

- developing and applying fuzz and model-based testing tools,
- developing formal methods-based modeling and verification tools,
- formal specification, simulation and model-checking of protocols and smart contracts, and
- auditing anything from L1 chains to smart contracts.

Caught your interest? [Reach out][Contact]!

---

## Runtime Monitors: Guardians of the Blockchain

It should be clear by now that the traditional security model is quite error-prone. It involves a lot of diverse actors of varying skill levels, and targets individual development phases with different methods.

Can we take a security approach that cuts across all development phases?  
Yes! With Solarkraft, we propose a [runtime monitoring][] solution to our problem. Runtime monitoring is a proactive approach that **monitors a smart contract for expected and abnormal behavior** as soon as it executes – and can happen during all phases of the development lifecycle. Not only that – it can supplement the artifacts (test, audit protocols, ...) developed by the traditional approach.

![]({{ site.baseurl }}/img/solarkraft-monitoring.png)

Here's how it works:

![]({{ site.baseurl }}/img/solarkraft-architecture.jpg)

1. **Monitor Specification:** Developers define a _runtime monitor_ that captures the expected behavior of the contract using a formal language like [TLA+][]. These specifications outline
    - **pre-conditions**: conditions that must be met before a function can execute,
    
    - **post-conditions**: the expected ledger state changes after each successful invocation, and
    
    - **failure conditions**: conditions under which the smart contract must revert.

(Solarkraft introduces two novel ideas: small _modular_ monitor specifications, and a _hybrid_ monitoring approach. We will cover both in a later posts.)

{:start="2"}
2. **Monitoring in Action:** The Solarkraft _fetcher_ component of the runtime monitor continuously observes the blockchain for contract invocations and retrieves the transaction data.

3. **Verification & Catching Deviations**: The Solarkraft _verifier_ compares the on-chain transaction data to the expected behavior defined in the monitor specification. This is an off-chain component that runs the [Apalache model-checker][Apalache] (running it on-chain would be too expensive and infeasible).

4. **Alerts:** If the verifier detects any deviation from the specified behavior (e.g., an unauthorized transaction attempt or an unexpected state change), it can take predefined actions, such as pausing the smart contract or raising an on- or off-chain alert to developers.

By continuously monitoring behavior against formal specifications, runtime monitoring offers several advantages over traditional methods:

- **Proactive Approach:** It catches bugs in nearly real-time, limiting or preventing potential financial losses and disruptions before they occur.

- **Continuous Monitoring:** Unlike testing and audits, which occur at a specific point in time against a fixed commit, runtime verification provides ongoing security throughout the contract's lifecycle.

- **Early Detection:** Runtime monitoring can identify potential issues early in the execution process, allowing for quicker mitigation and reducing the attack window for malicious actors.

In the following posts of this series, we'll delve deeper into the world of runtime monitoring in Solarkraft with TLA+. We'll explore how to specify contract behavior using this language, dive into Solarkraft's unique specification and monitoring strategies, and see how runtime verification can be seamlessly integrated into the development workflow to build more secure and reliable smart contracts.

_Development of Solarkraft was supported by the [Stellar Development Foundation][] with a generous Activation Award from the [Stellar Community Fund][] of 50,000 USD in XLM._


[Apalache]: https://konnov.phd/portfolio/apalache/
[Solarkraft]: https://thpani.net/solarkraft/
[Audits]: https://thpani.net/audits/
[Contact]: https://thpani.net/#contact

[part1]: https://thpani.net/2024/06/why-smart-contract-bugs-matter-and-how-runtime-monitoring-saves-the-day-solarkraft-1/
[part2]: https://thpani.net/2024/06/small-and-modular-runtime-monitors-in-tla-for-soroban-smart-contracts-solarkraft-2/

[Igor Konnov]: https://konnov.phd
[Jure Kukovec]: https://www.linkedin.com/in/jure-kukovec/
[Andrey Kuprianov]: https://www.linkedin.com/in/andrey-kuprianov/
[Thomas Pani]: https://thpani.net

[Soroban]: https://stellar.org/soroban
[Stellar Community Fund]: https://communityfund.stellar.org
[Stellar Development Foundation]: https://stellar.org/foundation

[Ethereum]: https://en.wikipedia.org/wiki/Ethereum
[Stellar]: https://en.wikipedia.org/wiki/Stellar_\(payment_network\)
[TLA+]: https://en.wikipedia.org/wiki/TLA%2B
[circuit breaker]: https://en.wikipedia.org/wiki/Circuit_breaker_design_pattern
[fuzz tests]: https://en.wikipedia.org/wiki/Fuzzing
[runtime monitoring]: https://en.wikipedia.org/wiki/Runtime_verification

[DAO Hack]: https://www.gemini.com/cryptopedia/the-dao-hack-makerdao
[Euler Finance hack]: https://www.chainalysis.com/blog/euler-finance-flash-loan-attack/
[Parity hack]: https://www.theguardian.com/technology/2017/nov/08/cryptocurrency-300m-dollars-stolen-bug-ether
[Manta attack]: https://www.coindesk.com/tech/2024/01/19/manta-network-hit-by-ddos-attack-day-after-token-issuance/
[Cream Finance hack]: https://medium.com/immunefi/hack-analysis-cream-finance-oct-2021-fc222d913fc5
[Rekt]: https://rekt.news/