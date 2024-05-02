---
layout: post
title: "Is it a medium, is it a high: What are the protocol expectations?"
date: 2024-04-30
categories: smart-contracts contests specification tlaplus
math: true
---

## 1. Introduction

It has been a while, since I wrote to this blog. I was not just chilling these
months though :mountain_bicyclist:. My friends and I have received funding from
the Stellar Foundation to develop [Solarkraft][]. More funding is in progress.
We also have been looking for bugs in Web3 protocols at [Code4rena][] and
[Sherlock][], individually as well as in the team called [CodeWasp][]. Although
we are still aiming at discovering a magic recipe to finding high-rewarding
bugs, we had a few successes already such as getting the first places in the
[UniStaker Infrastructure][] and [Mento][], among other findings in the recent
months. 

One immediate observation about the Web3 contests is that not every valid
finding guarantees a payout at the competition platforms. These platforms go in
detail about what is considered the most precious finding, that is a "high" or a
"medium". For example, see [Code4rena Severity Categorization][] and [Sherlock's
Criteria for Issue Validity][]. In addition to that, [Code4rena Incentive Model
and Awards][] incentivizes security researchers to find unique issues. That is
why a perfectly fine High which would be a big win in a traditional security
audit may easily result in a payout of $0.12 in a security contest :flushed:

In the end of the day, even given all the guidelines, the contest sponsors and
the judges have to figure out which fundings are worth rewarding. In this blog
post I would like to step away from the discussions about the human subjectivity
in the contests. The question I have been asking myself for some time:

*Is it even possible to formally specify highs and mediums for some protocols*?

Let's try. After all, bugs were not invented by blockchain engineers, and
researchers in [Formal Verification][] have been preoccupied with similar
questions for decades. For example, [Temporal Specification Patterns][] classify
properties of concurrent and reactive systems.

Here are the shortest introductory definitions from [Code4rena Severity
Categorization][]:

> 2 — Med: Assets not at direct risk, but the function of the protocol or its
availability could be impacted, or leak value with a hypothetical attack path
with stated assumptions, but external requirements.

> 3 — High: Assets can be stolen/lost/compromised directly (or indirectly if
there is a valid attack path that does not have hand-wavy hypotheticals).

## 2. Specifying a High

Let's start with specifying a behavior that demonstrates a finding deserving a
High.

### 2.1. Attempt 1: An Abstract Protocol




[Solarkraft]: https://konnov.phd/portfolio/solarkraft/
[Stellar Community Fund]: https://communityfund.stellar.org/
[UniStaker Infrastructure]: https://code4rena.com/reports/2024-02-uniswap-foundation
[Mento]: https://audits.sherlock.xyz/contests/187
[Code4rena]: https://code4rena.com/
[Sherlock]: https://www.sherlock.xyz/
[CodeWasp]: https://code4rena.com/@CodeWasp 
[Sherlock's Criteria for Issue Validity]: https://docs.sherlock.xyz/audits/judging/judging
[Code4rena Severity Categorization]: https://github.com/code-423n4/docs/blob/main/awarding/judging-criteria/severity-categorization.md
[Code4rena Incentive Model and Awards]: https://github.com/code-423n4/docs/tree/main/awarding/incentive-model-and-awards
[Quint]: https://github.com/informalsystems/quint
[Apalache]: https://github.com/informalsystems/apalache
[TLC]: https://lamport.azurewebsites.net/tla/tools.html
[TLA+]: https://lamport.azurewebsites.net/tla/tla.html
[Formal Verification]: https://en.wikipedia.org/wiki/Formal_verification
[Temporal Specification Patterns]: https://matthewbdwyer.github.io/psp/