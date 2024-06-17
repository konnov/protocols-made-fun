---
layout: post
title: "Guardians of the Blockchain: Small and Modular Runtime Monitors in TLA+ for Soroban Smart Contracts (Solarkraft #2)"
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

**» This guest post by [Thomas Pani][] first appeared [on his blog][part2].**

_This is the second in a series of blog posts introducing [Solarkraft][], a TLA+-based runtime monitoring solution for [Soroban smart contracts][Soroban]. The first post,_ ["A New Hope – Why Smart Contract Bugs Matter and How Runtime Monitoring Saves the Day"][part1] _gives an overview of smart contracts, explains how traditional security fails to address major challenges in securing crypto assets, and introduces runtime monitoring as a solution._

_Solarkraft has been developed in collaboration by [Igor Konnov][], [Jure Kukovec][], [Andrey Kuprianov][] and [Thomas Pani][]._

## Running Example: The Soroban Timelock Contract

In this post, we'll explore how to write small and modular runtime monitors in Solarkraft for Soroban contracts. [Soroban][] is the Rust-based smart contract language of the [Stellar blockchain][Stellar]. In fact, we will take a 127 LOC Soroban smart contract and specify (part of) its behavior in just 11 lines of Solarkraft and TLA+. 🚀

But first, we need a smart contract to secure! For this, we choose the [`timelock` contract][timelock] from [`soroban-examples` on Github][soroban-examples].

The contract's function is rather simple: It has two functions: `deposit()` and `claim()`. With `deposit()`, a user transfers a number of tokens into the contract and specifies (a) a list of allowed claimants, and (b) a time bound before or after which the amount may be claimed. One of the permitted claimants may later claim the deposit with `claim()` – as long as the time bound is upheld.

### Depositing tokens

We first look at [`deposit()`][deposit]:

```rust
pub fn deposit(env: Env, from: Address, token: Address, amount: i128, claimants: Vec<Address>, time_bound: TimeBound) {
    // ...

    // Transfer token from `from` to this contract address.
    token::Client::new(&env, &token).transfer(
        &from,
        &env.current_contract_address(),
        &amount);
        
    // Store necessary info to allow one of the claimants to claim it.
    env.storage().instance().set(&DataKey::Balance,
        &ClaimableBalance {token, amount, time_bound, claimants}
    );

    // ...
}
```

As we see above, `deposit()` takes a source account `from`, an [SEP-41 token contract][] `token` (similar to an ERC-20 token contract on Ethereum) and an `amount`. It also takes a list of addresses `claimants` that can claim the transferred amount, and a `TimeBound` that specifies before or after what `timestamp` the amount becomes available:

```rust
pub enum TimeBoundKind { Before, After }

pub struct TimeBound { pub kind: TimeBoundKind, pub timestamp: u64 }
```

Assume that we have two users _Alice_ and _Bob_ with addresses `addrAlice` and `addrBob`, and an SEP-41 token contract deployed at `addrTestToken`. Let's follow an example interaction with the contract: Alice invokes `deposit()` to place a number of test tokens into the contract:

```rust
deposit(addrAlice, addrTestToken, 100,
        [ addrBob ], {"kind": "After", "timestamp": 1718000000})
```

The call to `token::Client::new(...).transfer()` in `deposit()` simply transfers the specified `amount` of test tokens from Alice into the contract. The second line `env.storage().instance().set()` stores the claim information in the contract's ledger state: only Bob is allowed to claim the money, and only after Unix epoch `1718000000` (June 10, 2024 at 06:13:20 UTC).

### Claiming the deposit

Let's convince ourselves that this is the case by looking at [`claim()`][claim]:

```rust
// check that the timestamp is before/after the current ledger timestamp
fn check_time_bound(env: &Env, time_bound: &TimeBound) -> bool {
  let ledger_timestamp = env.ledger().timestamp();

  match time_bound.kind {
    TimeBoundKind::Before => ledger_timestamp <= time_bound.timestamp,
    TimeBoundKind::After => ledger_timestamp >= time_bound.timestamp,
  }
}

pub fn claim(env: Env, claimant: Address) {
  // Make sure claimant has authorized this call
  claimant.require_auth();
   
  // Just get the balance - if it's been claimed, this will simply panic
  let claimable_balance: ClaimableBalance =
       env.storage().instance().get(&DataKey::Balance).unwrap();

  if !check_time_bound(&env, &claimable_balance.time_bound) {
    panic!("time predicate is not fulfilled");
  }

  let claimants = &claimable_balance.claimants;
  if !claimants.contains(&claimant) {
    panic!("claimant is not allowed to claim this balance");
  }

  // Transfer the stored amount of token to claimant
  token::Client::new(&env, &claimable_balance.token).transfer(
    &env.current_contract_address(),
    &claimant,
    &claimable_balance.amount,
  );
  // Remove the balance entry to prevent any further claims.
  env.storage().instance().remove(&DataKey::Balance);
}
```

As we can see, `claim()` starts by checking that:

- `claimant` has actually originated the call,

- some claimable balance has been set through `deposit()`,

- the invocation happens before/after the timestamp specified by the depositor, and

- `claimant` is one of the claimants specified by the depositor

If one of these checks fails, the contract will panic and the transaction reverts. On the other hand, if all the checks pass, the deposited amount is transferred out of the contract to the `claimant`. Finally, the contract deletes the balance information so that no further claim can occur.

If Bob invokes `claim()` after June 10, 2024 at 06:13:20 UTC (the specified time bound), he will receive the 100 test tokens previously deposited by Alice.

## Modular Runtime Monitors in TLA+

Now that we know the timelock contract, let's specify a runtime monitor! In essence, a runtime monitor is a list of properties that should hold about each invocation of the smart contract.

But wait, how shall we do it? We need a programming language in which to write our properties... 🤔 In [Solarkraft][], we use [TLA+][], a formal specification language that has been developed by Turing Award-winner Leslie Lamport for reasoning about distributed systems.

### A first property: when to revert

Remember that `claim()` started with a long list of safety checks. If any of those checks fail, the contract should revert. One of them was "some claimable balance has been set":

```rust
// Just get the balance - if it's been claimed, this will simply panic
let claimable_balance: ClaimableBalance =
     env.storage().instance().get(&DataKey::Balance).unwrap();
```

Here's how we specify this behavior in Solarkraft / TLA+:

```tlaplus
MustRevert_claim_NoBalanceRecord(env) ≜ ¬instance_has("Balance", env)
```

`MustRevert_` means that we expect the contract to revert if this condition ever holds true. `_claim_` identifies the smart contract function this property applies to. Finally, `NoBalanceRecord` is an arbitrary name we can give to our property.

The property itself is easy enough to parse: `instance_has` checks whether the given key (`"Balance"`) exists in the contract instance storage. If you've taken a course on boolean logic, you know that `¬` stands for negation.

(The TLA+ in this post is typeset in Unicode, as produced by [`tlauc` by Andrew Helwer][tlauc].)

That's cool! We specified a complicated property about contract behavior in a single line! 🥳 Let's try another one?

### Another property: verifying the time bound

We expect `claim()` to revert if the time bound given by the depositor is violated. Here's how to do it:

```tlaplus
MustRevert_claim_BeforeTimeBound(env) ≜
    ∧ Balance.time_bound.kind = Variant("Before", UNIT)
    ∧ env.timestamp > Balance.time_bound.timestamp
```

Here, we check two conditions – they are connected through TLA+'s conjunction `∧`, indicating that _both_ conditions must hold for the contract to revert.

`Variant("Before", UNIT)` is simply the equivalent way of writing the Rust variant `Before()`. So if we see a "before" time bound, but the block timestamp is _after_ the timestamp specified during `deposit()`, the call to `claim()` should revert.

### Monitors in TLA+ are _Smadular_

Do you remember the Soroban source code necessary to check the time bound? Let's look at it again:

```rust
// check that the timestamp is before/after the current ledger timestamp
fn check_time_bound(env: &Env, time_bound: &TimeBound) -> bool {
  let ledger_timestamp = env.ledger().timestamp();

  match time_bound.kind {
    TimeBoundKind::Before => ledger_timestamp <= time_bound.timestamp,
    TimeBoundKind::After => ledger_timestamp >= time_bound.timestamp,
  }
}

pub fn claim(env: Env, claimant: Address) {
  // ...
  if !check_time_bound(&env, &claimable_balance.time_bound) {
    panic!("time predicate is not fulfilled");
  }
  // ...
```

That's a lot of code 😮‍💨 Not quite easy to see what it should be doing, right?  
Yet, we managed to give a **small behavioral Solarkraft spec** in just 3 lines of code:

```tlaplus
MustRevert_claim_BeforeTimeBound(env) ≜
    ∧ Balance.time_bound.kind = Variant("Before", "U_OF_UNIT")
    ∧ env.timestamp > Balance.time_bound.timestamp
```

Did you notice anything else? We did not have to specify the entirety of the time bound functionality (we did not cover the `"After"` case)! Our **specifications are modular** in this sense – you can specify as little or as much behavior as you like, extend your specification later on, and combine properties in any way you like.

So our runtime monitors in TLA+ are **small and modular**! Smadular! 🤩

### Specifying expected behavior

So far, we specified _when a contract invocation should revert_.  
What about expected behavior on successful transactions? Of course, we can specify those as well:

Remember that `deposit()` saves the supplied list of claimants and the time bound to the ledger state? Here's how we specify this in Solarkraft and TLA+:

```tlaplus
MustHold_deposit_BalanceRecordCorrect(args) ≜
    ∧ Balance'.token = args.token
    ∧ Balance'.amount = args.amount
    ∧ Balance'.time_bound = args.time_bound
    ∧ Balance'.claimants = args.claimants
```

For convenience, the Soroban instance storage key `"Balance"` is mapped to a TLA+ variable `Balance`. We use `Balance` and `Balance'` to refer to the ledger state before and after the transaction, respectively. Our property checks that the function arguments are saved to the ledger state after successful execution of `deposit()` as indicated by the property name `MustHold_deposit_`.

## What's next?

So far, so good! After learning about smart contract security in the first post of this series, this post explored how to specify runtime monitors in Solarkraft / TLA+. We looked at the Soroban [`timelock` contract][timelock] – 127 LOC in Rust, and created a small and modular Solarkraft specification of just 11 LOC. 🚀

In the next post, we explain how to run Solarkraft to verify a smart contract and delve a bit into its architecture. Our final post goes into even more detail about runtime monitors, forward and backward reasoning, and what we call "hybrid" monitors.

_Development of Solarkraft was supported by the [Stellar Development Foundation][] with a generous Activation Award from the [Stellar Community Fund][] of 50,000 USD in XLM._



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