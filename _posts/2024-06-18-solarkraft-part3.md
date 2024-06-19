---
layout: post
title: "How to Run Solarkraft (Solarkraft #3)"
date: 2024-06-19
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

**» This is a guest post by [Jure Kukovec][].**

_This is the third in a series of blog posts introducing [Solarkraft][], a TLA+-based runtime monitoring solution for [Soroban smart contracts][Soroban]. The first post,_ ["A New Hope – Why Smart Contract Bugs Matter and How Runtime Monitoring Saves the Day"][part1] _gives an overview of smart contracts, explains how traditional security fails to address major challenges in securing crypto assets, and introduces runtime monitoring as a solution. The second post,_ [Guardians of the Blockchain: Small and Modular Runtime Monitors in TLA+ for Soroban Smart Contracts][part2] _introduces the language of Solarkraft monitors._ 

_Solarkraft has been developed in collaboration by [Igor Konnov][], [Jure Kukovec][], [Andrey Kuprianov][] and [Thomas Pani][]._


If you’ve read the previous posts, and are keen to start using Solarkraft, you’ve come to the right place. In this post, we’ll give you a detailed overview of the various features of Solarkraft, and explain how to use each one, step-by-step.
We’ve recorded a short video demonstrating every command, which you can follow along as give more details:

![]({{ site.baseurl }}/video/SolarkraftDemo.mp4)

## Before we start
In order to use `solarkraft`, you need the following:
  - The contract ID of a Soroban contract, deployed on the Stellar blockchain. Can be `mainnet` or `testnet`
  - A TLA+ monitor tailored to the chosen contract

The [Soroban admin guide](https://developers.stellar.org/network/soroban-rpc/admin-guide) explains how you can use the `soroban cli` to deploy your own contract. For details on how to write a monitor, and some examples, see [Part 2 of our blogpost series](part2).

## Building solarkraft
Solarkraft is free and open-source, and you can find the GitHub repository [here](https://github.com/freespek/solarkraft/). To start, you’ll want to clone the repository, navigate to the `solarkraft` sub-directory, and follow [these installation instructions](https://github.com/freespek/solarkraft/blob/038540fa87d32bd78da5d23d805b5867b47a1f17/solarkraft/INSTALL.md).

After you’ve successfully installed solarkraft, you can use `solarkraft –help` to see a list of options:

![]({{ site.baseurl }}/img/solarkraft_help.png)

## Solarkraft commands
Solarkraft has two main commands, `fetch` and `verify`, and an auxiliary command `list`. We will go over the details of each command separately.

Conceptually, the process of using Solarkraft can be broken down into two parts
  1. Data retrieval: Solarkraft collects information on all transactions related to a given contract ID, from a given point in time onward. It uses [Stellar Horizon](https://developers.stellar.org/network/horizon), which ingests and re-serves data produced by the Stellar network, to access historical and near-real time transaction data. This is done via the `solarkraft fetch` command.
  2. Transaction verification: Given transaction data, concretely the state of the data storage before and after the transaction was executed, as well as information about which smart contract function was invoked in that transaction, and with which parameters, we use a monitor specification to see whether the executed transaction satisfies the constraints specified in the monitor. This is done via the `solarkraft verify` command.

Our approach allows us to do things asynchronously and modularly: we can `fetch` one transaction (or a collection of transactions) and reuse the obtained data as often as we like; verifying against multiple combinations of monitors, in sequence or in parallel.

## Data retrieval: `solarkraft fetch`
The first step towards verification is obtaining the transaction data that we wish to verify, and `fetch` is the way to do that. If we look at the `--help` available, we can see a number of parameters to pass to `solarkraft fetch`:


![]({{ site.baseurl }}/img/solarkraft_fetch_help.png)

The first few are self-explanatory, so let's focus on the critical ones:
  - `id`: This is a mandatory parameter, since `fetch` will only retrieve transactions related to the provided contract ID.
  - `typemap`:  For the present MVP, we focus on the core functionality and require user annotations. Because Apalache, the backend solver used in `solarkraft verify`, deals with typed TLA+, we need to provide type hints, whenever the types of values present in the transaction data are ambiguous. `typemap` accepts a JSON file containing such type hints for method parameters and storage-values. A detailed description of the shape of this file can be found [here](https://github.com/freespek/solarkraft/blob/038540fa87d32bd78da5d23d805b5867b47a1f17/solarkraft/src/fetch.ts#L12-L43), and an example can be found [here](https://github.com/freespek/solarkraft/blob/038540fa87d32bd78da5d23d805b5867b47a1f17/doc/timelock/typeHints.json). This parameter is always optional, but if omitted, `verify` might be unable to continue, in which case you will be prompted to `fetch` again, with `typemap` specified.
  - `rpc`: The Horizon RPC URL. If your contract is deployed to the testnet, you don’t need to provide this, but you have to specify it otherwise.
  - `height`: This parameter is mandatory, and specifies the minimum ledger height, from which `solarkraft fetch` will attempt to retrieve all transactions related to the provided contract id.
  - `timeout`: Unless provided, `fetch` will indefinitely attempt to retrieve new transaction data as the ledger grows. The parameter should be used if you need to limit `fetch` execution time (e.g. in automation). By default, you can keep it running in the background, if you’re interested in always keeping up-to-date transaction data for a specific contract.

Here’s an example of a `solarkraft fetch` command specifying some of the parameters:

![]({{ site.baseurl }}/img/solarkraft_fetch.png)

Observe that every time a transaction related to the contract id is found, `fetch` notifies us with a `save: XYZ` message. In the above case, we started at height 8152, and found two transactions in ledgers 8153 and 8154, before stopping the fetcher.

## Data display: `solarkraft list`
In order to keep track of transactions we’ve fetched, and those we’ve verified, we can use `list`, to display the list of all transactions:

![]({{ site.baseurl }}/img/solarkraft_list.png)

Note that if you’ve been strictly following this tutorial, both transactions should be marked as `unverified`. The above image is intended to give you a more general sense of the kind of output to expect from `solarkraft list`.

For each contract, and each transaction related to the contract, `solarkraft list` displays
  - The verification status: `unverified`, if no verification has been done yet, `ok`, if no property violations were found, w.r.t. the last monitor that was used to `solarkraft verify` this transaction, or `fail`, if the transaction violated one or more properties in the monitor. 
  - The height at which this transaction was read.
  - The transaction hash. This value is used as a parameter to `solarkraft verify`.

If you’re working with multiple contracts at the same time, you can refine the listing by specifying a single contract id with `--id`; by default, it lists all transactions for all contracts.


## Transaction verification: `solarkraft verify`
Assuming we’ve successfully used `solarkraft fetch` to grab a number of transactions, the next step is to verify them against the monitor(s). Much like `fetch`, `solarkraft verify` takes a number of parameters:

![]({{ site.baseurl }}/img/solarkraft_verify_help.png)

The critical ones are:
  - `txHash`: The hash of the transaction to be verified. We get this value by reading from `solarkraft list`.
  - `monitor`: The TLA+ monitor file, which specifies our constraints. See [2] for more detail.
  - `alert`: An optional parameter, which allows us to automatically submit a transaction to an alert contract deployed on the testnet after verification terminates, uploading whatever the result of verification was, and emitting an event if a property violation was found. More on this parameter later.

If you’re looking to verify a transaction locally and/or manually, and have no automation in place to respond to property violations, you only need to provide a hash and a monitor:

![]({{ site.baseurl }}/img/solarkraft_verify.png)

In this mode, you get notified of the verification result (which also gets stored, if you call `solarkraft list` later), and can respond to it accordingly.

### Verification automation: `--alert`
Solarkraft provides you with some tools to facilitate automation. One of those is automatic verification-status submissions to an on-chain alert contract. The solarkraft repository offers an [alert contract](https://github.com/freespek/solarkraft/tree/038540fa87d32bd78da5d23d805b5867b47a1f17/ContractExamples/contracts/alert), which you can deploy on testnet (there is no mainnet alert support in the MVP).
If you call `solarkraft verify --alert`, and provide the contract ID of such an alert contract, the results of verification will automatically be submitted to it, and an event will be emitted, which you can listen for, and respond to, if you so choose.


## Summary

  1. `fetch` to grab the transaction data from the provided Horizon RPC, then
  2. `list`, to see which transactions you have already fetched, and what their verification statuses are, then
  3. `verify` to check the transaction data against the monitor specification, and  `--alert`, if you want the verification results to get submitted on-chain automatically



[Solarkraft]: https://thpani.net/solarkraft/
[part1]: https://thpani.net/2024/06/why-smart-contract-bugs-matter-and-how-runtime-monitoring-saves-the-day-solarkraft-1/
[part2]: https://thpani.net/2024/06/small-and-modular-runtime-monitors-in-tla-for-soroban-smart-contracts-solarkraft-2/

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
[deposit]: https://github.com/stellar/soroban-examples/blob/f595fb5df06058ec0b9b829e9e4d0fe0513e0aa8/timelock/src/lib.rs#L57-L91
[claim]: https://github.com/stellar/soroban-examples/blob/f595fb5df06058ec0b9b829e9e4d0fe0513e0aa8/timelock/src/lib.rs#L93-L120

[tlauc]: https://ahelwer.ca/post/2024-05-28-tla-unicode/