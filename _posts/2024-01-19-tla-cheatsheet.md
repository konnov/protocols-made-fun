---
layout: post
title: "TLA+ cheatsheet in Markdown"
date: 2024-01-19
categories: tlaplus
tlaplus: true
math: true
---

I have realized that I need $\tla{}$ syntax highlighting for my next blog post.
Since [highlightjs][] did not support $\tla{}$, I have introduced a
highlighting theme in [tlaplus-highlightjs][]. The best way to test
highlighting is by typing the [TLA+ Summary][] by [Leslie Lamport][]
(originally, in pdf) on this page.

All the contents below is simply retyping of the [TLA+ Summary][] in Markdown.
Hence, all the credit for the original content goes to Leslie Lamport, not to
me. I only added a few comments regarding typing $\tla{}$ in ASCII and adjusted
some typesetting to make it work in Markdown. These comments are shown in
*italic*, or in $\tla{}$ comments such as:

```tlaplus
original text   \* I: my single-line comment
  (* or
     in a multiline comment *)  
```

In addition to that, since it is not easy to combine math and code
highlighting, I am using the ASCII typesetting as well as the Unicode
typesetting, as produced by [tlauc][]. Finally, Markdown is not nearly as
good as LaTeX. I could not reproduce the last section of [TLA+ Summary][],
which maps ASCII operators to their LaTeX presentation.

## Module-Level Constructs

```tlaplus
---- MODULE M ----
```

Begins the module or submodule named $M$. *(At least four leading dashes '-'
are required.)*

```tlaplus
EXTENDS M_1, ..., M_n
```

Incorporates the declarations, definitions, assumptions, and theorems from the
modules named $M_1, \dots, M_n$ into the current module. 

```tlaplus
CONSTANTS C_1, ..., C_n
CONSTANT C_1, ..., C_n
```

Declares the $C_j$ to be constant parameters (rigid variables). Each $C_j$ is
either an identifier or has the form 
$C($_ $,\dots,$ _ $)$, the latter form
indicating that the $C$ is an operator with the indicated number of arguments.

```tlaplus
VARIABLES x_1, ..., x_n
VARIABLE x_1, ..., x_n
```

Declares the $x_j$ to be variables (parameters that are flexible variables).

```tlaplus
ASSUME P
```

Asserts $P$ as an assumption.

```tlaplus
F(x_1, ..., x_n) == exp
F(x_1, ..., x_n) ≜ exp
```

Defines $F$ to be the operator such that $F(e_1, \dots, e_n)$ equals $exp$ with
each identifier $x_k$ replaced by $e_k$. (For $n = 0$, it is written $F ≜
exp$.)

```tlaplus
f[x \in S] == exp
f[x ∈ S] ≜ exp
```

Defines $f$ to be the function with domain $S$ such that $f[x] = exp$ for all
$x$ in $S$. (The symbol $f$ may occur in $exp$, allowing a recursive
definition.)

*Note*: $x \in S$ may be replaced by a comma-separated list of items $v \in S$,
where $v$ is either a comma-separated list or a tuple of identifiers.

```tlaplus
INSTANCE M WITH p_1 <- e_1, ..., p_m <- e_m
INSTANCE M WITH p_1 ← e_1, …, p_m ← e_m
```

For each defined operator $F$ of module $M$, this defines $F$ to be the
operator whose definition is obtained from the definition of $F$ in $M$ by
replacing each declared constant or variable $p_j$ of $M$ with $e_j$. (If $m =
0$ the `WITH` is omitted.)

```tlaplus
N(x_1, ..., x_n) == INSTANCE M WITH p_1 <- e_1, ..., p_m <- e_m
N(x_1, ..., x_n) ≜ INSTANCE M WITH p_1 ← e_1, …, p_m ← e_m
```

For each defined operator $F$ of module $M$, this defines $N(d_1, \dots,
d_n)!F$ to be the operator whose definition is obtained from the definition of
$F$ by replacing each declared constant or variable $p_j$ of $M$ with $e_j$,
and then replacing each identifier $x_k$ with $d_k$. (If $m = 0$, the `WITH` is
omitted.)

```tlaplus
THEOREM P
```

Asserts that $P$ can be proved from the definitions and assumptions of the
current module.

```tlaplus
LOCAL def
```

Makes the definition(s) of `def` (which may be a definition or an `INSTANCE`
statement) local to the current module, thereby not obtained when extending or
instantiating the module.

```tlaplus
====
```

Ends the current module or submodule. *(At least four equal signs `=` are
required.)*

## The Constant Operators

### Logic

```tlaplus
p /\ q    \* I: p and q
p ∧ q
p \/ q    \* I: p or q
p ∨ q
~p        \* I: not p
¬p
p => q    \* I: p implies q
p ⇒ q
p <=> q   \* I: p if and only if q
p ⇔  q
TRUE
FALSE
BOOLEAN             \* the set { TRUE, FALSE }
\A x \in S: P       \* I: forall x in S: P, see Note (1) below
∀ x ∈ S: P
\E x \in S: P       \* I: exists x in S: P, see Note (1) below
∃ x ∈ S: P
CHOOSE x \in S: P   \* An x in S satisfying P
```

<a id="note1"/>

**Note (1):** `x \in S` may be replaced by a comma-separated list of items `v
\in S`, where `v` is either a comma-separated list or a tuple of identifiers.

### Sets

```tlaplus
S = T
S /= T
S ≠ T
x \in S
x ∈ S
x \notin S
x ∉ S
S \union T
S ∪ T
S \intersect T
S ∩ T
S \subseteq T
S ⊆ T
S \ T                   \* set difference
{ e_1, ..., e_n }       \* Set consisting of elements e_i
{ x \in S: p }          \* Set of elements x in S satisfying p, see Note (2) below
{ x ∈ S: p }
{ e: x \in S }          \* Set of elements e such that x in S, see Note (1) above
{ e: x ∈ S }
SUBSET S                \* Set of subsets of S
UNION S                 \* Union of all elements of S
```

<a id="note2"/>

**Note (2):** `x` may be an identifier or a tuple of identifiers.

 
### Functions

```tlaplus
f[e]                    \* Function application
DOMAIN f                \* Domain of function f
[x \in S |-> e]         \* Function f such that f[x] = e for x ∈ S, see Note (1) above
[x ∈ S ↦ e]
[S -> T]                \* Set of functions f with f[x] ∈ T for x ∈ S
[S → T]
[f EXCEPT ![e_1] = e_2] \* Function g equal to f except g[e_1] = e_2, see Note (3) below
```

<a id="note3"/>

**Note (3):** `![e_1]` or `!.h` may be replaced by a comma-separated list of
items `!a_1...a_n`, where each `a_i` is `[e_i]` or `.h_i`.

### Records

```tlaplus
e.h                             \* The h-field of record e
[h_1 |-> e_1, ..., h_n |-> e_n] \* The record whose h_i field is e_i
[h_1 ↦ e_1, ..., h_n ↦ e_n]
[h_1: S_1, ..., h_n: S_n]       \* Set of all records with h_i field in S_i
[r EXCEPT !.h = e]              \* Record s equal to r except s.h = e, see Note (3) above
```

### Tuples

```tlaplus
e[i]                \* The i-th component of tuple e
<<e_1, ..., e_n>>   \* The n-tuple whose i-th component is e_i
⟨e_1, …, e_n⟩
S_1 \X ... \X S_n   \* The set of all n-tuples with i-th component in S_i
S_1 × … × S_n
```

## Miscellaneous Constructs

```tlaplus
IF p THEN e_1 ELSE e_2
            \* e_1 if p is true else e_2

CASE p_1 -> e_1 [] ... [] p_n -> e_n
CASE p_1 → e_1 □ … □ p_n → e_n
            \* Some e_i such that p_i is true

CASE p_1 -> e_1 [] … [] p_n -> e_n [] OTHER -> e
CASE p_1 → e_1 □ … □ p_n → e_n □ OTHER → e
            \* Some e_i such that p_i is true, or e if all p_i are false

LET d_1 == e_1 ... d_n == e_n IN e
LET d_1 ≜ e_1 ... d_n ≜ e_n IN e
            \* e in the context of the definitions d_1, ..., d_n

/\ p_1   \* the conjunction p_1 ∧ ... ∧ p_n
   ...
/\ p_n

\/ p_1   \* the disjunction p_1 ∨ ... ∨ p_n
   ...
\/ p_n

\* the same in Unicode
∧ p_1
  ...
∧ p_n

∨ p_1
  ...
∨ p_1

```

## Action Operators

```tlaplus
e'            \* The value of e in the final state of a step
[A]_e         \* A ∨ (e' = e)
<A>_e         \* A ∧ (e' ≠ e)
ENABLED A     \* An A step is possible
UNCHANGED e   \* e' = e
A \cdot B     \* Composition of actions
```

## Temporal operators

```tlaplus
[]F       \* F is always true
□F
<>F       \* F is eventually true
◇F
WF_e(A)   \* Weak fairness for action A
SF_e(A)   \* Strong fairness for action A
F ~> G    \* F leads to G
F ↝ G
```

## User-Definable Operator Symbols

*We are using the ASCII notation. To see a nice typesetting of these operators,
check the PDF version in [TLA+ Summary][]*.

### Infix Operators

```tlaplus
+         -     *        /        \o      ++
\div      %     ^        ..       ...     --
(+)       (-)   (\X)     (/)      (.)     **
<         >     <=       >=       \sqcap  //
\prec     \succ \preceq  \succeq  \sqcup  ^^
\ll       \gg   <:       :>       &       &&
                                  |       %%
\sqsubset \sqsupset \sqsubseteq \sqsupseteq
\subset   \supset               \supseteq
                                \star     @@
|-        -|    |=       =|     \bullet   ##
~       \simeq  \approx  \cong    $       $$
\bigcirc  ::=   \asymp  \doteq    ??      !!
\propto   \wr   \uplus
```

Some of these operators are defined in the standard modules:

 - `Naturals`, `Integers`, `Reals` define:
    `+`, `-`, `*`, `\div`, `%`, `^`, `..`, `<`, `>`, `<=`, `>=`
 - `Reals` defines: `/`
 - `Sequences` defines: `\o`
 - `Bags` defines: `(+)`, `(-)`, `\sqsubseteq`
 - `TLC` defines: `:>`, `@@`

### Postfix Operators

```tlaplus
^+    ^*    ^#
```

## Operators Defined in Standard Modules

**Module** $Naturals$

```tlaplus
+     -   *       ^   ..    Nat
\div  %   <= =>   <   >
```

Note that $Naturals$ defines only infix `-`.

**Module** $Integers$

```tlaplus
+     -   *       ^   ..    Nat
\div  %   <= =>   <   >     Int
```

**Module** $Reals$

```tlaplus
+     -   *   /   ^   ..    Nat   Real
\div  %   <= =>   <   >     Int   Infinity
```

**Module** $Sequences$

```tlaplus
\o      Head    SelectSeq   SubSeq
Append  Len     Seq         Tail
```

**Module** $FiniteSets$

```tlaplus
IsFiniteSet   Cardinality
```

**Module** $Bags$

```tlaplus
(+)             BagIn     CopiesIn    SubBag
(-)             BagOfAll  EmptyBag
\sqsubseteq     BagToSet  IsABag
BagCardinality  BagUnion  SetToBag
```

**Module** $RealTime$

```tlaplus
RTBound   RTNow   \* declared to be a variable
```

**Module TLC**

```tlaplus
:>        @@    Print   Assert    JavaTime  Permutations
SortSeq
```

## Precedence Ranges of Operators

The relative precedence of two operators is unspecified if their ranges
overlap. Left-associative operators are indicated by (L).

**Prefix Operators**

```tlaplus
~         4-4     []    4-15    UNION   8-8
ENABLED   4-15    <>    4-15    DOMAIN  9-9
UNCHANGED 4-15  SUBSET  8-8       -     12-12
```

**Infix Operators**

```tlaplus
=>      1-1      <=         5-5       <:         7-7        (-)       11-11 (L)
-+->    2-2      \ll        5-5       \          8-8        -         11-11 (L)
<=>     2-2      \prec      5-5       \union     8-8 (L)    --        11-11 (L)
~>      2-2      \preceq    5-5       \intersect 8-8 (L)    &         13-13 (L)
/\      3-3 (L)  \propto    5-5       ..         9-9        &&        13-13 (L)
\/      3-3 (L)  \sim       5-5       ...        9-9        (.)       13-13 (L)
/=      5-5      \simeq     5-5       !!         9-13       (/)       13-13
-|      5-5      \sqsubset  5-5       ##         9-13 (L)   (\X)      13-13 (L)
::=     5-5      \sqsubseteq 5-5      $          9-13 (L)   *         13-13 (L)
:=      5-5      \sqsupset  5-5       $$         9-13 (L)   **        13-13 (L)
<       5-5      \sqsupseteq 5-5      ??         9-13 (L)   /         13-13
=       5-5      \subset    5-5       \sqcap     9-13 (L)   //        13-13
=|      5-5      \subseteq  5-5       \sqcup     9-13 (L)   \bigcirc  13-13 (L)
>       5-5      \succ      5-5       \uplus     9-13 (L)   \bullet   13-13 (L)
\approx 5-5      \succeq    5-5       \wr        9-14       \div      13-13
\asymp  5-5      \supset    5-5       (+)       10-10 (L)   \o        13-13 (L)
\cong   5-5      \supseteq  5-5       +         10-10 (L)   \star     13-13 (L)
\doteq  5-5      |-         5-5       ++        10-10 (L)   ^         14-14
>=      5-5      |=         5-5       %         10-11       ^^        14-14
\gg     5-5      \cdot      5-14 (L)  %%        10-11 (L)   .         17-17 (L)
\in     5-5      @@         6-6  (L)  |         10-11 (L)
\notin  5-5      :>         7-7       ||        10-11 (L)
```

**Postfix Operators**

```tlaplus
^+    15-15   ^*     15-15     ^#    15-15      ' 15-15
```


## ASCII Representation of Typeset Symbols

*Please check [TLA+ Summary][]. This is too much for Markdown.*


[highlightjs]: https://highlightjs.org/
[tlaplus-highlightjs]: https://github.com/konnov/tlaplus-highlightjs
[TLA+ Summary]: https://lamport.azurewebsites.net/tla/summary-standalone.pdf
[Leslie Lamport]: https://lamport.org/
[tlauc]: https://github.com/tlaplus-community/tlauc
