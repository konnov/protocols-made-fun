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
Deltas == AMOUNTS \union { -i: i \in AMOUNTS}

\* Protocol initialization, e.g., contract instantiation
Init ==
    balances = INITIAL_SUPPLY

\* An abstract transfer between multiple accounts.
\* @type: (Str -> Int) => Bool;
Update(deltas) ==
    \* update the balances
    LET newBalances == [ a \in ADDR |-> balances[a] + deltas[a] ] IN 
    /\ \A a \in ADDR: newBalances[a] \in AMOUNTS
    /\ balances' = newBalances
    \* A concrete protocol would have plenty of other constraints.
    \* However, we are not interested in these details.

\* A single protocol step, e.g., a public function of a smart contract
Next ==
    \E deltas \in [ ADDR -> Deltas ]:
        Update(deltas)
=====================================