------ MODULE MC_AbstractDeFi ------
EXTENDS Integers, Apalache

\* a few addresses for illustration purposes
ADDR == { "alice", "bob", "eve", "contract", "investor", "owner" }
\* a small range of amounts
AMOUNTS == 0..100
\* only the owner gets tokens initially
INITIAL_SUPPLY == [ a \in ADDR |-> IF a = "owner" THEN 100 ELSE 0 ]

VARIABLES
    \* @type: Str -> Int;
    balances

INSTANCE AbstractDeFi

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