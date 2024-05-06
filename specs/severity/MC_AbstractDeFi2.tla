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

\* A naive invariant: Eve cannot extract more than 150.00% of the deposit from the protocol
WithdrawCappedInv ==
    amountsIn["eve"] > 0 => (amountsOut["eve"] <= (15000 * amountsIn["eve"]) \div 10000)

\* A safety property: Eve's withdrawals are limited with her deposits.
CappedWithdrawal ==
    []((amountsIn["eve"] > amountsOut["eve"]) => [](amountsOut["eve"] <= (15000 * amountsIn["eve"]) \div 10000))

EveBalanceIsZero ==
    balances["eve"] = 0

========================================