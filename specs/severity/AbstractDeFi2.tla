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

ASSUME EOA \subseteq ADDR

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
Deltas == AMOUNTS \union { -i: i \in AMOUNTS}

\* Protocol initialization, e.g., contract instantiation
Init ==
    /\ balances = INITIAL_SUPPLY
    /\ amountsIn = INITIAL_SUPPLY
    /\ amountsOut = [ a \in ADDR |-> 0 ]

\* An abstract transfer between multiple accounts.
\* @type: (Str -> Int) => Bool;
Update(deltas) ==
    \* update the balances
    LET newBalances == [ a \in ADDR |-> balances[a] + deltas[a] ] IN 
    /\ \A a \in ADDR: newBalances[a] \in AMOUNTS
    /\ balances' = newBalances
    /\ UNCHANGED <<amountsIn, amountsOut>>
    \* A concrete protocol would have plenty of other constraints.
    \* However, we are not interested in these details.

\* An abstract deposit.
\* @type: (Str, Int) => Bool;
Deposit(sender, amount) ==
    /\ balances[sender] + amount \in AMOUNTS
    /\ balances' = [ balances EXCEPT ![sender] = @ + amount ]
    /\ amountsIn' = [ amountsIn EXCEPT ![sender] = @ + amount ]
    /\ UNCHANGED amountsOut

\* An abstract withdrawal.
\* @type: (Str, Int) => Bool;
Withdraw(sender, amount) ==
    /\ balances[sender] - amount \in AMOUNTS
    /\ balances' = [ balances EXCEPT ![sender] = @ - amount ]
    /\ amountsOut' = [ amountsOut EXCEPT ![sender] = @ + amount ]
    /\ UNCHANGED amountsIn

\* A single protocol step, e.g., a public function of a smart contract
Next ==
    \/ \E deltas \in [ ADDR -> Deltas ]:
        Update(deltas)
    \/ \E sender \in EOA, amount \in AMOUNTS:
        \/ Deposit(sender, amount)
        \/ Withdraw(sender, amount)
=====================================