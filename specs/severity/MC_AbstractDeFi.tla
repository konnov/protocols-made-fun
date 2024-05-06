------ MODULE MC_AbstractDeFi ------
EXTENDS Integers, Apalache

\* a few addresses for illustration purposes
ADDR == { "alice", "bob", "eve", "contract", "investor", "owner", "0x0" }
\* a small range of amounts
AMOUNTS == 0..100
\* only the owner gets tokens initially
INITIAL_SUPPLY == [ a \in ADDR |-> IF a = "owner" THEN 100 ELSE 0 ]

VARIABLES
    \* @type: Str -> Int;
    balances

INSTANCE AbstractDeFi

\* The next step that preserves the total supply.
\* Use NextPreserving instead of Next, when you do not want to see the
\* examples of burning and minting.
NextPreserving ==    
    /\ Next
    /\ LET AddBefore(sum, addr) == sum + balances[addr]
           AddAfter(sum, addr) == sum + balances'[addr]
           totalBefore == ApaFoldSet(AddBefore, 0, ADDR)
           totalAfter == ApaFoldSet(AddAfter, 0, ADDR)
       IN
       totalBefore = totalAfter

\* The next step that does not allow the total supply decrease.
\* Use NonDecreasing instead of Next, when you do not want to see the
\* examples of burning.
NextNonDecreasing ==    
    /\ Next
    /\ \A addr \in ADDR:
          balances'[addr] >= balances[addr]

\* a combination of the above two transition relations
NextPreservingAndNonDecreasing ==
    NextPreserving /\ NextNonDecreasing          

\* State invariants that may be of interest.

\* A state invariant that specifies that there is no drain-all high:
\* It's never the case that Eve (the attacker) gets all the tokens.
DrainAllInv ==
    \E a \in ADDR \ { "eve" }:
        balances[a] > 0

\* A state invariant that specifies that all tokens cannot be burnt.
BurnAllInv ==
    \E a \in ADDR:
        balances[a] > 0

\* A state invariant that specifies that all tokens cannot be burnt.
\* This invariant considers the amounts below 5 to be dust.
BurnAllButDustInv ==
    \E a \in ADDR:
        balances[a] >= 5

\* A state invariant that specifies that the balances should not go
\* below the initial supply.
BurnSomeInv ==
    LET AddInitial(sum, addr) == sum + INITIAL_SUPPLY[addr]
        AddCurrent(sum, addr) == sum + balances[addr]
        initialTotal == ApaFoldSet(AddInitial, 0, ADDR)
        currentTotal == ApaFoldSet(AddCurrent, 0, ADDR)
    IN
    currentTotal >= initialTotal

\* A state invariant that specifies that the balances should not go
\* significantly below the initial supply.
BurnHalfInv ==
    LET AddInitial(sum, addr) == sum + INITIAL_SUPPLY[addr]
        AddCurrent(sum, addr) == sum + balances[addr]
        initialTotal == ApaFoldSet(AddInitial, 0, ADDR)
        currentTotal == ApaFoldSet(AddCurrent, 0, ADDR)
    IN
    currentTotal >= initialTotal \div 2

\* A state invariant: no transfer to zero should ever happen.
LockingInZeroInv ==
    balances["0x0"] = 0

\* An action invariant: Eve cannot increase her balance.
EveNoBalanceIncreaseInv ==
    balances'["eve"] <= balances["eve"]

\* Trivial false invariants to get examples:

\* A false invariant: The contract never has tokens on its balance:
\* $ apalache-mc check --inv=ContractBalanceIsZero specs/severity/MC_AbstractProtocol.tla
ContractBalanceIsZero ==
    balances["contract"] = 0

EveBalanceIsZero ==
    balances["eve"] = 0

AliceDoesNotLoseFunds ==
    balances'["alice"] >= balances["alice"]

========================================