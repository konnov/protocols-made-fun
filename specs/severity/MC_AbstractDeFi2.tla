------ MODULE MC_AbstractDeFi2 ------
EXTENDS Integers, Apalache

\* a few externally-owned addresses
EOA == { "alice", "bob", "eve", "investor", "owner" }
\* ...and contract/system addresses
ADDR == EOA \union { "contract", "0x0" }
\* a small range of amounts
AMOUNTS == 0..100
\* only the owner gets tokens initially
INITIAL_SUPPLY == [ a \in ADDR |-> IF a = "owner" THEN 100 ELSE 0 ]

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

INSTANCE AbstractDeFi2

\* State invariants that may be of interest.

\* A state invariant that specifies that there is no drain-all high:
\* It's never the case that Eve (the attacker) gets all the tokens.
DrainAllInv ==
    \E a \in ADDR \ { "eve" }:
        balances[a] > 0

EveBalanceIsZero ==
    balances["eve"] = 0

========================================