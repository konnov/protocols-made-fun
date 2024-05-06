---
layout: post
title: "Is it a medium or a high: What are the protocol expectations?"
date: 2024-04-30
categories: smart-contracts contests specification tlaplus
math: true
tlaplus: true
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
why a perfectly fine High, which would be a big win in a traditional security
audit, may easily result in a payout of $0.12 in a security contest :flushed:

At the end of the day, even given all the guidelines, the contest sponsors and
the judges have to figure out which findings are worth rewarding. In this blog
post I would like to step away from the discussions about the human subjectivity
in the contests. The question I have been asking myself for some time:

*Is it even possible to formally specify highs and mediums for some protocols*?

Let's try. After all, bugs were not invented by blockchain engineers.
Researchers in [Formal Verification][] have been preoccupied with similar
questions for decades. For example, [Temporal Specification Patterns][] classify
properties of concurrent and reactive systems.

Here are the shortest introductory definitions from [Code4rena Severity
Categorization][]:

> 2 — Med: Assets not at direct risk, but the function of the protocol or its
availability could be impacted, or leak value with a hypothetical attack path
with stated assumptions, but external requirements.

> 3 — High: Assets can be stolen/lost/compromised directly (or indirectly if
there is a valid attack path that does not have hand-wavy hypotheticals).

## 2. Abstract DeFi Protocol

Since Mediums and Highs involve a protocol, we need a protocol to talk about.
At this point, a security researcher would typically choose one of the two
approaches:

 1. Point to a concrete protocol, e.g., a smart contract in Solidity.

 1. Present an idea of a protocol in English, perhaps, adding a bit of
 math notation on top of it.

Instead of following one of the above approaches, I am following the third
approach, which is much more powerful, even though less common. I am using
Temporal Logic of Actions, or TLA<sup>+</sup>, which was designed exactly for
[Specifying Systems][]. I am not going to explain TLA<sup>+</sup> in this blog
post. There are plenty of resources out there, including [Learn TLA][] by Hillel
Wayne.  If you want to quickly recall the syntax of TLA<sup>+</sup>, check my
[TLA+ cheatsheet][].

What do most of the DeFi protocols have in common? Well, they move tokens from
and to various addresses. For instance, many Ethereum contracts creatively
manipulate with ETH. This is what we distill into a very abstract specification
of a DeFi protocol in TLA<sup>+</sup>[^1]: 

**Source: [AbstractDeFi.tla][]**

```tla
------ MODULE AbstractDeFi ------
EXTENDS Integers

CONSTANT
    \* A set of account addresses.
    \* @type: Set(Str);
    ADDR,
    \* A set of token amounts.
    \* @type: Set(Int);
    AMOUNTS,
    \* Initial supply of tokens for all addresses.
    \* @type: Str -> Int;
    INITIAL_SUPPLY

VARIABLES
    \* Balances for one kind of a token, e.g., ETH.
    \* @type: Str -> Int;
    balances

\* Negative and positive updates to the token amounts
Deltas ≜ AMOUNTS ∪ { -i: i ∈ AMOUNTS}

\* Protocol initialization, e.g., contract instantiation
Init ≜
    balances = INITIAL_SUPPLY

\* An abstract transfer between multiple accounts.
\* @type: (Str -> Int) => Bool;
Update(deltas) ≜
    \* update the balances
    LET newBalances ≜ [ a ∈ ADDR ↦ balances[a] + deltas[a] ] IN 
    ∧ ∀ a ∈ ADDR: newBalances[a] ∈ AMOUNTS
    ∧ balances' = newBalances
    \* A concrete protocol would have plenty of other constraints.
    \* However, we are not interested in these details.

\* A single protocol step, e.g., a public function of a smart contract
Next ≜
    ∃ deltas ∈ [ ADDR → Deltas ]:
        Update(deltas)
=====================================
```

What does `AbstractDeFi` actually specify? Well, we have a state machine, that
keeps track of token `balances` for every address from the set `ADDR`.
Initially, the balances are set to `INITIAL_SUPPLY`, e.g., we could give all the
tokens to the contract owner. At every step, the balance of each account `a \in
ADDR` is updated by some delta from `deltas[a]`. If you think about it, many
DeFi protocols fit into this description. For example, the famous [ERC20][]
token standard is concerned with transferring tokens, and, optionally, minting
and burning them.

If you wonder about `ADDR`, `AMOUNTS`, and `INITIAL_SUPPLY`, check how we set them
up in a specification instance:

**Source: [MC_AbstractDeFi.tla][]**

```tla
...
\* a few addresses for illustration purposes
ADDR == { "alice", "bob", "eve", "contract", "investor", "owner", "0x0" }
\* a small range of amounts
AMOUNTS ≜ 0‥100
\* only the owner gets tokens initially
INITIAL_SUPPLY ≜ [ a ∈ ADDR ↦ IF a = "owner" THEN 100 ELSE 0 ]
...
```

Our protocol specification is quite general, perhaps, even too general. Like in
real protocols, multiple accounts may be updated in a single step (e.g., in a
single blockchain transaction), e.g., by updating contract balances, burning
gas, transferring protocol fees, etc. We could make our abstract protocol even
more general by maintaing balances for multiple token types. To keep things
simple, we will restrict the protocol to one token type.

By writing this abstract protocol, we have introduced a crucial assumption:

*All changes to `balances` are made via `AbstractDeFi`.*

If we compare `AbstractDeFi` with an arbitrary smart contract in DeFi, we will
immediately notice that `AbstractDeFi` is quite permissive in comparison to the
actual contract. Indeed, this is why we call our specification "abstract". It
does allow for many behaviors that are ruled out in actual protocols. Yet, our
specification is useful, as it lets us capture interesting behaviors without
going into unnecessary details.

## 3. Formalizing Highs

Now that we have given a bit of shape to our DeFi protocol, how do we specify
a High? When I started to think about that, I realized that there is probably
no one "good" way of specifying all kinds of highs. Hence, we will go over a
series of various highs, starting with the most dangerous ones.

### 3.1. Draining All Tokens

Let's start with specifying the most obvious, the most evil, behavior
:smiling_imp:. Every now and then, we see protocols where an attacker is able to
drain all tokens from the protocol. Following the tradition, we would say that
the attacker is called Eve. To express this property, we simply write the
following [State Invariant][]:

**Source: [MC_AbstractDeFi.tla][]**

```tla
\* A state invariant that specifies that there is no way to drain all tokens:
\* It's never the case that Eve (the attacker) gets all the tokens.
DrainAllInv ≜                                                               
    ∃ a ∈ ADDR \ { "eve" }:
        balances[a] > 0
```

The invariant `DrainAllInv` says that there is at least one address with a
non-negative balance, and this address is different from `"eve"`, the attacker.

This all sounds too abstract. Can we have an example? Yep. I simply run the
model checker [Apalache][] to produce a behavior that violates `DrainAllInv`.
Here is one example that Apalache gave to me:

| **owner** | **contract** | **eve** | **alice** | **bob** | **investor** |
|-----------|--------------|---------|-----------|---------|--------------|
| **100**   | 0            | 0       | 0         | 0       | 0            |
| 0         | 0            | **22**  | 0         | 0       | 0            |

(*To tell you the truth, Apalache gave me an example in TLA<sup>+</sup>, but
ChatGPT was quite helpful in transforming it to the above markdown table.*)

If you are a security researcher and you find a behavior like the one above in a
security contest, that's definitely a big win for you. Collect the reward and
enjoy your life :palm_tree: Or, maybe not, if 200 other participants have found
the same issue :scream:. Of course, such findings are rare. They would
demonstrate a catastrophic flaw in the protocol. Sometimes, this is caused by
incorrectly set permissions, e.g., see [Decent721][] (my first :dollar:). Also,
the model checker was lazy and produced us an example, where the funds were
drained in a single step, while a large part of it was burnt. In real life, an
attacker would typically drain funds via multiple transactions.

Let's go back to the Code4rena classification of a high:

> 3 — High: Assets can be stolen/lost/compromised directly (or indirectly if
there is a valid attack path that does not have hand-wavy hypotheticals).

Our invariant `DrainAllInv` specifies the case of assets being stolen.  Even
more, it specifies the case of all assets being stolen. We revisit this property
later.

### 3.2. Burning Tokens

We have seen an example of tokens being stolen. How about tokens being lost?
Let's write a state invariant that tells us that it should not be possible to
burn all the tokens:

**Source: [MC_AbstractDeFi.tla][]**

```tla
\* A state invariant that specifies that all tokens cannot be burnt.
BurnAllInv ≜
    ∃ a ∈ ADDR:
        balances[a] > 0
```

We run the model checker and it gives us an example of a behavior that violates
`BurnAllInv`:

| **owner** | **contract** | **eve** | **alice** | **bob** | **investor** |
|-----------|--------------|---------|-----------|---------|--------------|
| **100**   | 0            | 0       | 0         | 0       | 0            |
| 0         | 0            | 0       | 0         | 0       | 0            |

**Accounting for dust.** To be fair, it seems to be almost impossible that a
protocol burns all of the tokens down to zero. Typically, some dust amounts
would be left on the accounts. It is easy to modify `BurnAllInv` to account for
dust amounts.  Say, the amounts below 5 are considered to be dust:

**Source: [MC_AbstractDeFi.tla][]**

```tla
\* A state invariant that specifies that all tokens cannot be burnt.
\* This invariant considers the amounts below 5 to be dust.
BurnAllButDustInv ≜
    ∃ a ∈ ADDR:
        balances[a] >= 5
```

We run the model checker again. This time, to check `BurnAllButDustInv`:

| **owner** | **contract** | **eve** | **alice** | **bob** | **investor** |
|-----------|--------------|---------|-----------|---------|--------------|
| **100**   | 0            | 0       | 0         | 0       | 0            |
| **3**     | 0            | **4**   | **4**     | **1**   | **2**        |

The model checker produces a somewhat bizarre example: Dust amounts were spread
over five accounts, though it is still well below the initial supply.  This
behavior still follows the `AbstractDeFi` specification.  Perhaps, there are
protocols like that in the wild?

**Burning some tokens.** Okay, we can specify what it means to burn all or
almost all of the tokens. How often does that happen? Similar to the case of
`DrainAllInv`, it should be a rare finding. How about not burning all the
tokens, but burning some of the initial supply? This is what we specify with
`BurnSomeInv` below:

**Source: [MC_AbstractDeFi.tla][]**

```tla
\* A state invariant that specifies that the balances should not go
\* below the initial supply.
BurnSomeInv ≜
    LET AddInitial(sum, addr) ≜ sum + INITIAL_SUPPLY[addr]
        AddCurrent(sum, addr) ≜ sum + balances[addr]
        initialTotal ≜ ApaFoldSet(AddInitial, 0, ADDR)
        currentTotal ≜ ApaFoldSet(AddCurrent, 0, ADDR)
    IN
    currentTotal ≥ initialTotal
```

Even though `BurnSomeInv` looks a bit more complex than `BurnAllInv`, there is
not much happening. We simply sum over the initial balances and the current
balances, then compare the sums. The model checker gives us an example that
violates `BurnSomeInv`:

| **owner** | **contract** | **eve** | **alice** | **bob** | **investor** |
|-----------|--------------|---------|-----------|---------|--------------|
| **100**   | 0            | 0       | 0         | 0       | 0            |
| **99**    | 0            | 0       | 0         | 0       | 0            |

**Economic feasibility.** Whereas the above example looks valid, it would be
hard to get a valid high finding out of that. Why? Logically speaking, it
demonstrates a bug. However, we should not forget that DeFi deals with finances
instead of perfect logic. Most likely, the above behavior would be rejected as a
non-finding with a verdict of being "economically infeasible". The reason is
that the attacker would have to burn gas to run this attack. If it costs the
attacker more in gas to run the attack than they would benefit from it, e.g.,
from the token prices going down, then this attack would not be considered
economically feasible.

The bad news is that the model checker has no idea about finances and what is
feasible or not. The good news is that it is up to us to tell it what it means.
For example, we could say that burning over 50% of the initial funds is
not good, for sure:

**Source: [MC_AbstractDeFi.tla][]**

```tla
\* A state invariant that specifies that the balances should not go
\* significantly below the initial supply.
BurnHalfInv ≜
    LET AddInitial(sum, addr) ≜ sum + INITIAL_SUPPLY[addr]
        AddCurrent(sum, addr) ≜ sum + balances[addr]
        initialTotal ≜ ApaFoldSet(AddInitial, 0, ADDR)
        currentTotal ≜ ApaFoldSet(AddCurrent, 0, ADDR)
    IN
    currentTotal ≥ initialTotal ÷ 2
```

This time, the model checker produces the following example:

| **owner** | **contract** | **eve** | **alice** | **bob** | **investor** |
|-----------|--------------|---------|-----------|---------|--------------|
| **100**   | 0            | 0       | 0         | 0       | 0            |
| **10**    | 0            | **4**   | **1**     | 0       | **34**       |

Again, the model checker has scattered the balances over various accounts, since
this is allowed. What is important, the example shows that over a half of the
tokens have disappeared, as we requested.

OK. We have considered many ways to burn tokens. Are we done with losing tokens?
Not yet. There is one more curious way to lose tokens.

### 3.3. Transferring Tokens to an Uncontrolled Address

Another way to lose tokens is by transferring them to an address that no one can
control. Perhaps, the most famous example of this is transferring tokens to the
address `0x0...0` in Ethereum, see [Transfer to zero address][]. In 2024, it's
virtually impossible to get a reward for finding a transfer to `0x0....0`,
though locking funds in a smart contract can still be a valid finding.

It is easy to specify that a designated address should not receive tokens:

**Source: [MC_AbstractDeFi.tla][]**

```tla
\* A state invariant: no transfer to zero should ever happen.
LockingInZeroInv ≜
    balances["0x0"] = 0
```

Again, the model checker is ready to give us a counterexample to `LockingInZeroInv`:

| **owner** | **contract** | **eve** | **alice** | **bob** | **investor** | **0x0**      |
|-----------|--------------|---------|-----------|---------|--------------|--------------|
| **100**   | 0            | 0       | 0         | 0       | 0            | 0            |
| **8**     | **2**        | 0       | 0         | 0       | **61**       | **29**       |

Here we are. The address `0x0` has the balance of 29, and there is no way to
recover these tokens.

If you look at the example carefully, no tokens were burnt or minted. The token
supply happens to be the same. I have asked the model checker to do it on
purpose by using the definition `NextPreserving` instead of `Next`:

**Source: [MC_AbstractDeFi.tla][]**

```tla
\* The next step that preserves the total supply.
\* Use NextPreserving instead of Next, when you do not want to see the          
\* examples of burning and minting.
NextPreserving ≜
    ∧ Next
    ∧ LET AddBefore(sum, addr) ≜ sum + balances[addr]
          AddAfter(sum, addr) ≜ sum + balances'[addr]
          totalBefore ≜ ApaFoldSet(AddBefore, 0, ADDR)
          totalAfter ≜ ApaFoldSet(AddAfter, 0, ADDR)
      IN
      totalBefore = totalAfter
```

### 3.4. Minting Tokens

Surprisingly, we are still not done exploring the ways for Eve getting rich
according to the "law of the code". Assume that we forbid our protocol to
decrease the balances on all accounts. We can easily write a restricted form of `Next`,
similar to `NextPreserving`:

**Source: [MC_AbstractDeFi.tla][]**

```tla
\* The next step that does not allow the total supply decrease.
\* Use NonDecreasing instead of Next, when you do not want to see the
\* examples of burning.
NextNonDecreasing ≜
    ∧ Next
    ∧ ∀ addr ∈ ADDR:
        balances'[addr] ≥ balances[addr]
```

Further, we write an [Action Invariant][] for Eve:

**Source: [MC_AbstractDeFi.tla][]**

```tla
\* An action invariant: Eve cannot increase her balance.
EveNoBalanceIncreaseInv ≜
    balances'["eve"] ≤ balances["eve"]
```

Obviously, the model checker produces an example of minting tokens:

| **owner** | **contract** | **eve** | **alice** | **bob** | **investor** | **0x0**      |
|-----------|--------------|---------|-----------|---------|--------------|--------------|
| **100**   | 0            | 0       | 0         | 0       | 0            | 0            |
| **100**   | **61**       | **67**  | **1**     | **80**  | **98**       | **29**       |

Our abstract DeFi protocol has generously minted tokens to everyone, including Eve.

## 4. Bullet-Proof Protocol?

Having restricted our protocol with `NextPreserving` and `NextNonDecreasing` in
the previous sections, we may be tempted to combine both of these two
constraints like this:

**Source: [MC_AbstractDeFi.tla][]**

```tla
\* a combination of the above two transition relations
NextPreservingAndNonDecreasing ≜
    NextPreserving ∧ NextNonDecreasing
```

Interestingly, the model checker does not find a counterexample to **all
invariants** that we have written so far. Is it a perfect bullet-proof protocol?
Kind of. If we look carefully at the constraints in
`NextPreservingAndNonDecreasing`, we will see that this protocol is doing
absolutely nothing useful. It starts with the initial supply and never changes
the balances.

## 5. Refining the Abstract DeFi Protocol

So far we have seen more or less obvious effects of a DeFi attack, even though
the underlying protocol could be quite complex. It does not always happen that
an attacker steals or burns almost all tokens. Even if they steal, say, 5% of
the total value locked, then they may be well off.

How can we specify such an attack? Intuitively, Eve has to extract more value
from the protocol than she invested. To this end, we have to keep track of how
much Eve has sent to the protocol and received from it. Unfortunately, our
`AbstractDeFi` protocol is too abstract for this purpose. We cannot even
distinguish between depositing, withdrawing, and other protocol actions.
Hence, we refine `AbstractDeFi` into `AbstractDeFi2`:

**Source: [AbstractDeFi2.tla][]**

```tla
------ MODULE AbstractDeFi2 ------
EXTENDS Integers

CONSTANT
    \* A set of account addresses.
    \* @type: Set(Str);
    ADDR,
    \* Externally owned addresses.
    \* @type: Set(Str);
    EOA,
    \* A set of token amounts.
    \* @type: Set(Int);
    AMOUNTS,
    \* Initial supply of tokens for all addresses.
    \* @type: Str -> Int;
    INITIAL_SUPPLY

ASSUME EOA ⊆ ADDR

VARIABLES
    \* Balances for one kind of a token, e.g., ETH.
    \* @type: Str -> Int;
    balances,
    \* Amounts that were deposited.
    \* @type: Str -> Int;
    amountsIn,
    \* Amounts that were withdrawn.
    \* @type: Str -> Int;
    amountsOut

\* Negative and positive updates to the token amounts
Deltas ≜ AMOUNTS ∪ { -i: i ∈ AMOUNTS}

\* Protocol initialization, e.g., contract instantiation
Init ≜
    ∧ balances = INITIAL_SUPPLY
    ∧ amountsIn = INITIAL_SUPPLY
    ∧ amountsOut = [ a ∈ ADDR ↦ 0 ]

\* An abstract transfer between multiple accounts.
\* @type: (Str -> Int) => Bool;
Update(deltas) ≜
    \* update the balances
    LET newBalances ≜ [ a ∈ ADDR ↦ balances[a] + deltas[a] ] IN 
    ∧ ∀ a ∈ ADDR: newBalances[a] ∈ AMOUNTS
    ∧ balances' = newBalances
    ∧ UNCHANGED ⟨amountsIn, amountsOut⟩
    \* A concrete protocol would have plenty of other constraints.
    \* However, we are not interested in these details.

\* An abstract deposit.
\* @type: (Str, Int) => Bool;
Deposit(sender, amount) ≜
    ∧ balances[sender] + amount ∈ AMOUNTS
    ∧ balances' = [ balances EXCEPT ![sender] = @ + amount ]
    ∧ amountsIn' = [ amountsIn EXCEPT ![sender] = @ + amount ]
    ∧ UNCHANGED amountsOut

\* An abstract withdrawal.
\* @type: (Str, Int) => Bool;
Withdraw(sender, amount) ≜
    ∧ balances[sender] - amount ∈ AMOUNTS
    ∧ balances' = [ balances EXCEPT ![sender] = @ - amount ]
    ∧ amountsOut' = [ amountsOut EXCEPT ![sender] = @ + amount ]
    ∧ UNCHANGED amountsIn

\* A single protocol step, e.g., a public function of a smart contract
Next ≜
    ∨ ∃ deltas ∈ [ ADDR → Deltas ]:
        Update(deltas)
    ∨ ∃ sender ∈ EOA, amount ∈ AMOUNTS:
        ∨ Deposit(sender, amount)
        ∨ Withdraw(sender, amount)
=====================================
```

The specification `AbstractDeFi2` extends `AbstractDeFi` as follows:

 - In addition to the constant `ADDR`, it has `EOA` for externally-owned
 addresses.
 
 - In addition to the state variable `balances`, it has state variables
 `amountsIn` and `amountsOut`

 - In addition to the action `Update`, it has two more actions:
 `Deposit` and `Withdraw`.

We also introduce a model-checking instance [MC_AbstractDeFi2.tla][].
 
## 6. Refining Draining Attacks

Let's see how we could formalize more refined attacks, not just "drain it all".

### 6.1. Naive Invariant

Now that we have `amountsIn` and `amountsOut`, we can think about detecting a
state, where Eve exhibits malicious activity. Our first attempt is somewhat
naive.  We state that it should be impossible for Eve to generate more than 50%
on top of what she has deposited.

```tla
\* A naive invariant: Eve cannot extract more than 150.00% of her deposit from the protocol
WithdrawCappedInv ≜
    amountsIn["eve"] > 0 ⇒ (amountsOut["eve"] ≤ (15000 * amountsIn["eve"]) ÷ 10000)
```

Since our abstract protocol is virtually unrestricted in what kind of updates it
permits, the model checker quickly finds a counterexample to
`WithdrawCappedInv`:

| **State**     | **`amountsIn["eve"]`** | **`balances["eve"]`**  | **`amountsOut["eve"]`** |
| -------------:| ----------------------:| ----------------------:| -----------------------:|
| 0.            | 0                      | 0                      | 0                       | 
| 1.            | 0                      | **64**                 | 0                       |
| 2.            | 0                      | **62**                 | **2**                   |
| 3.            | **1**                  | **63**                 | **2**                   |

The invariant `WithdrawCappedInv` is violated in the third state, as Eve
deposited 1 token in the third state, whereas she withdrew 2 tokens (in the
second state). If we look carefully at the above example, we will see that
something is not exactly as we might have expected.  Indeed, Eve has the
following values in the second state:

```tla
  amountsIn["eve"] = 0 ∧ amountsOut["eve"] = 2
```

The above example demonstrates a strange behavior, where Eve could withdraw 2
tokens without depositing anything. On one hand, it could probably demonstrate a
bug in a real protocol. On the other hand, Eve could receive rewards such as
protocol fees, which could explain this behavior.

*Can we write a property that actually connects deposited tokens and withdrawn
tokens?*

### 6.2. Less Naive Safety Property

Intuitively, we would like to say something like that:

  *Whenever Eve deposits a positive amount, she cannot withdraw over 150% of
   this amount.*

This sounds like a temporal relation between deposits and withdrawals. Good that
we are using Temporal Logic of Actions! In TLA<sup>+</sup>, we can easily write
this property as `LimitedDeposit`:

```tla
\* A safety property: Eve's withdrawals are limited with her deposits.
CappedWithdrawal ≜
    □((amountsIn["eve"] > amountsOut["eve"])
         ⇒ □(amountsOut["eve"] ≤ (15000 * amountsIn["eve"]) ÷ 10000))
```

The symbol `□` stands for "always", and `⇒` is classical implication, that is,
`A ⇒ B` is equivalent to `¬A ∨ B`. When we check this property against
[MC_AbstractDeFi2.tla][], the model checker produces a counterexample, e.g.:

| **State**     | **`amountsIn["eve"]`** | **`balances["eve"]`**  | **`amountsOut["eve"]`** |
| -------------:| ----------------------:| ----------------------:| -----------------------:|
| 0.            | 0                      | 0                      | 0                       |
| 1.            | **5**                  | **5**                  | 0                       |
| 2.            | **5**                  | **42**                 | 0                       |
| 3.            | **5**                  | **26**                 | **16**                  |

If we find a behavior like the one above in a real protocol, this may clearly
demonstrate an issue.

### 6.3. Increasing Rewards with Time

Whereas the protocol behavior in the previous section could demonstrate a
draining attack in one protocol, it could be seen as a false positive in another
protocol.  Indeed, our safety property `CappedWithdrawal` restricts all
withdrawals at 150% of the deposits. For example, it does not seem to be
realistic in a staking protocol, where depositors may collect higher rewards in
several years.

When we have to express more fine-grained protocol properties like staking
rewards, we have to introduce the notion of time in the protocol. This usually
needs consensus block numbers or timestamps. Further, we have to account for the
periods of time when certain amounts are staked, and we have to constrain the
withdrawals with the potential rewards.

It's possible to further refine our abstract DeFi protocol. However, this blog
post is too long already. If you are interested in seeing such properties, let
me know.

## 7. Centralization Risks

So far, we have been seeing behaviors, in which Eve was obtaining or destroying
tokens. Since we have not specified details of the actual protocol, we
implicitly assumed that all the behaviors involved the actions by Eve. However,
it often happens that an attacker can perform their actions only after the
protocol adminstrator -- usually, the protocol owner -- has performed specific
actions.

This is where subtle issues may appear. In principle, the protocol owner could
simply steal all the tokens or destroy the protocol contracts. If the protocol
owner is a single externally-owned account (EOA), then the protocol has a single
point of failure, namely, the protocol owner. This is why people say that such
protocols have the risk of centralization, even though the rest of their
operations is decentralized. Technically, the protocol owner does not have to be
a single EOA. Instead, it could be a proxy contract that requires multiple
signatures (multisig) for every transaction. Still, if this multisig contract
requires only a few signatures, it can be considered centralized.

Since the protocol owner has so much power, [centralization risks][] usually
lead to no reward. However, sometimes the protocol owner may unlock absolutely
valid protocol features that are exploited by an attacker later. Formalizing and
verifying such findings is not trivial. To start with, we would have to
partition the protocol actions according to the roles that are required to
execute them. For instance, in Solidity, owner-only external functions usually
come with the modifier `onlyOwner`. We could definitely specify role-related
properties. However, it is out of scope for this blog post.

## 8. Conclusions

We have looked into the most common behaviors that could indicate an attack
leading to a potentially "High" finding. I am pretty sure that there are still
plenty of findings on [Solodit][] that would need more fine-grained
specifications of the properties and the protocols. Nevertheless, I believe
that thinking about protocols and their properties in terms of state machines
is extremely useful, for the following reasons:

 1. We *move away from extremely ambiguous descriptions in natural language* to
 precise descriptions in a formal language that is designed for this purpose.  I
 have been using TLA<sup>+</sup> in this blog post, since I am most comfortable
 with the language and its tooling. Obviously, having been developing
 [Apalache][] for over than seven years, I know how to express properties in
 such a way that it works the best for the human reader and the model checker. I
 could have used [Quint][] instead of TLA<sup>+</sup> and it would not make much
 of a difference for this blog post. I just felt that the more mathematical
 syntax of TLA<sup>+</sup> would suit this level of abstraction more naturally.
 
 1. We can *use tools* to produce positive examples that would help you in
 understanding the properties better. As we have seen in the blog post, the
 tools are extremely helpful in findind *counterexamples*, that is,
 demonstrating the cases when the properties are violated. I have been using
 [Apalache][]. Actually, we could find the same problems with [TLC][], though it
 could take longer. Alternatively, we could express our abstract protocols in
 Solidity and use a fuzzer such as [Medusa][] to produce examples. However, when
 using a fuzzer, we would not be able to conclude that certain invariants could
 not be violated.

 1. When we start thinking about protocols and their properties in terms of
 state machines, we can rely upon the *decades of research* in computer-aided
 verification and model checking. We do not have to reinvent from scratch the
 techniques that are written in thousands of pages in [Handbook of Model
 Checking][] and [Principles of Model Checking][].
 
 1. Classifying protocol properties is essential for *tool development*. When we
 see that certain properties are required by multiple protocols, we can
 fine-tune the tools to check these properties.

This blog post is quite long. I have not considered another layer of attacks,
namely, availability attacks. If you are curious to see a blog post on this
topic, let me know. These are the attacks that disable certain actions in a
protocol. Interestingly, such attacks require reasoning about liveness of the
protocol, not just its safety. This would require temporal properties instead of
invariants. Sometimes, it is possible to express such properties with state
invariants. This is what [Apalache][] does internally, implementing the
technique that is described in the paper called [Liveness Checking as Safety
Checking][]. These invariants are large and hard to understand for a
non-expert. They would be even harder to write by hand.

If you need my help in specifying the expected properties of your protocols, be
it smart contracts, consensus, or distributed systems in general, feel free to
[contact me](mailto:igor@konnov.phd).


**Footnotes:**
 
[^1]: I found TLA<sup>+</sup> specs to be more accessible in this blog post when they are written in Unicode, as produced by the tool [tlauc][] by [Andrew Helwer][].

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
[Specifying Systems]: https://lamport.azurewebsites.net/tla/book.html
[Learn TLA]: https://learntla.com/
[TLA+ cheatsheet]: https://protocols-made-fun.com/tlaplus/2024/01/22/tla-cheatsheet.html
[ERC20]: https://docs.openzeppelin.com/contracts/4.x/erc20
[AbstractDeFi.tla]: {{ site.baseurl }}/specs/severity/AbstractDeFi.tla
[MC_AbstractDeFi.tla]: {{ site.baseurl }}/specs/severity/MC_AbstractDeFi.tla
[AbstractDeFi2.tla]: {{ site.baseurl }}/specs/severity/AbstractDeFi2.tla
[MC_AbstractDeFi2.tla]: {{ site.baseurl }}/specs/severity/MC_AbstractDeFi2.tla
[tlauc]: https://github.com/tlaplus-community/tlauc
[Andrew Helwer]: https://ahelwer.ca/
[Hillel Wayne]: https://www.hillelwayne.com/
[Transfer to zero address]: https://solodit.xyz/issues/transfer-to-zero-address-mixbytes-none-gearbox-protocol-markdown_
[Decent721]: https://github.com/code-423n4/2024-01-decent-findings/issues/721
[State Invariant]: https://apalache.informal.systems/docs/apalache/principles/invariants.html#state-invariants
[Action Invariant]: https://apalache.informal.systems/docs/apalache/principles/invariants.html#action-invariants
[Centralization risks]: https://github.com/code-423n4/docs/blob/main/awarding/judging-criteria/severity-categorization.md#centralization-risks
[Solodit]: https://solodit.xyz
[Medusa]: https://github.com/crytic/medusa
[Liveness Checking as Safety Checking]: https://www.sciencedirect.com/science/article/pii/S1571066104804109?via%3Dihub
[Handbook of Model Checking]: https://link.springer.com/book/10.1007/978-3-319-10575-8
[Principles of Model Checking]: https://mitpress.mit.edu/9780262026499/principles-of-model-checking/