---
layout: post
title: "Proving consistency of two-phase commit in Lean 4"
date: 2025-05-08
categories: lean
tlaplus: true
quint: true
math: true
lean: true
shell: true
---

**Author:** [Igor Konnov][]

**Tags:** specification lean distributed proofs tlaplus

In the previous [blog post][lean-two-phase], we discussed specification,
randomized simulation, and property-based testing of Two-phase commit in [Lean
4][Lean]. The obvious question is whether we can use Lean for what it was
designed for, namely, proving correctness of the protocol. Yes, we can!
Here is our proof plan:

{% include webp.html
    src="two-phase-proof-schema.png"
    alt="Our proof schema" %}

In short, I have managed to write full proofs of consistency in Lean 4, starting
with a functional specification. Except for a few moments, it was clear how to
proceed, though interactive proofs are tedious. In total, it took me 29 hours to
write the proofs, excluding the time that was needed to read the Lean manuals.
Together with specification and simulation from the previous [blog
post][lean-two-phase], the whole effort required 45 hours.

I believe the proofs went quickly because the inductive invariant was already
correct, since we have found it with the model checker [Apalache][]. In fact, I
could probably reduce the proof times even further if I focused on minimizing
the inductive invariant. If the invariant had not been correct, though, the
process likely would not have gone as smoothly.

Let us have a look at the statistics in the table below.

| Files                         | LOC (excluding comments & whitespace) |
|-------------------------------|--------------------------------------:|
| Functional.lean + System.lean | 139                                   |
| Propositional.lean            | 90                                    |
| PropositionalProofs.lean      | 275                                   |
| InductiveProofs.lean          | 1077                                  |

The ratio of proofs (propositional and inductive) to the system code
(propositional) is about 15. This fits into the empirical ratio of software
verification, where the proofs are 10-20 longer than the source code.

In this blog post, we have explored a "traditional" path of interactive theorem
proving, though we have [cut corners](#3-finding-an-inductive-invariant) by
finding the inductive invariant with the model checker.

Another route to explore is to prove equivalence between our specification in
[Propositional.lean] and the [Veil][] specification. The Veil examples already
contain a [version of two-phase commit][2pc-ivy], though it is slightly
different from the [two-phase commit in TLA<sup>+</sup>](two-phase-tla) and our
specification in Lean. Perhaps, this is a good topic for another exercise.

Certainly, this is not the first exercise in using interactive theorem provers
to verify safety of a distributed algorithms. To name a few examples, there were
larger-scale efforts such as [IronFleet][], [Verdi][], [Disel][], and
[Bythos][].

## 1. What to prove?

The task does not seem simple, though. How do we approach it? Our goal is to
prove the consistency of the protocol. Fortunately, we started with the
[specification in TLA+][two-phase-tla], so we can stand on the shoulders of
giants and reuse the TLA<sup>+</sup> methodology. Here is how consistency is
specified in TLA<sup>+</sup>:

{% github_embed
  https://raw.githubusercontent.com/tlaplus/Examples/37236893f14527b4fc9f3963891eb2316c3de62e/specifications/transaction_commit/TCommit.tla
  tlaplus 54-60
 %}

This invariant looks quite similar in Lean:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
  lean 65-67
 %}

By following the TLA<sup>+</sup> methodology, to show that $TCConsistent$ is an
invariant of Two-phase commit, it suffices to find a state predicate $IndInv$
and prove three properties:

 1. The initial states satisfy the invariant $IndInv$, that is, $Init \Rightarrow
    IndInv$.
 
 1. The transition relation preserves the invariant $IndInv$, that is,
    $Next \land IndInv \Rightarrow IndInv'$.

 1. The invariant $IndInv$ implies the state invariant $TCConsistent$, that is,
    $IndInv \Rightarrow TCConsistent$.

The invariant $\mathit{IndInv}$ is called an *inductive invariant*, since it
allows us to reason about all states that are reachable from $\mathit{Init}$ via
$\mathit{Next}$ *by induction*. The interesting thing is that it is sufficient
to prove this principle only once and reuse it for all specifications. This is
why we simply use this approach without re-proving it every time. The cool thing
about Lean is that we still can re-prove this inductive principle, if we want to.

## 2. Connecting functional and propositional specs

Now we have to understand what to use as the initial predicate $Init$ and the
transition relation $Next$. If you have read the [previous blog
post][lean-two-phase], you remember that we had two kinds of specifications:

 - A functional specification in [Functional.lean][] and [System.lean][], and

 - A propositional specification in [Propositional.lean][].

Luckily, [Ilya Sergey][] warned me that writing proofs at the functional level
is hard, so I did it at the propositional level. To connect the functional spec
and the propositional spec, we prove two theorems:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/PropositionalProofs.lean
  lean 172-173
 %}

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/PropositionalProofs.lean
  lean 191-192
 %}

You can find complete proofs in [PropositionalProofs.lean][]. What's
interesting, it took me just 2.5 hours to write the equivalence proofs for all
seven actions.  That was fast, because once I wrote three proofs, the remaining
four were completely generated by Copilot! As I expected, these proofs were
relatively easy to write.

For instance, here is the function `tm_commit` in the functional specification:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/Functional.lean
  lean 68-77
 %}

And here is the propositional version `tm_commit`, which looks very much like an
action in TLA<sup>+</sup>:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/Propositional.lean
  lean 38-46
 %}

The theorem `tm_commit_correct` is connecting both of them.

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/PropositionalProofs.lean
  lean 39-58
 %}

If you are like me, it is hard to make sense of this proof by just starring at
it, in contrast to pen & paper proofs. If you want to understand the proof,
download the spec and go over the proof line by line with the [Lean plugin][].
Of course, you would have to understand how the proofs are organized in Lean.
The book on [Theorem Proving in Lean 4][lean-tp] explains this.

It took me one more hour to prove the theorem `tp_next_correct`. However, when I
turned to `tp_init_correct`, I got carried away trying to prove a statement that
was too difficult. The proof involved several inductive arguments about hash
maps, and I ended up spending four hours wrestling with a challenging fact. Once
I clarified that, it only took 30 minutes to write a simpler and more effective
proof.

Basically, the entire set of refinement proofs could be completed in a single
day! The fact that Copilot was able to fill in four out of seven cases suggests
that these proofs could be generalized into a broader lemma. This is evident
from the structure of the proofs. I decided to leave them as they are for now,
but we should consider making them more compact for easier maintenance.

For the remainder of this post, we will use only the propositional specification.

## 3. Finding an inductive invariant

To follow the proof methodology, we have to find $IndInv$. We could try to use
our goal invariant `consistency` as a candidate for the invariant. However,
safety properties rarely work as inductive invariants. Intuitively, an inductive
invariant should generalize all reachable states, and `consistency` is too weak
for that role.

How do we find $IndInv$? One approach would be to start with `True`, then try to
prove the three properties. Once we understood why `True` is not good enough,
add constraints. Repeat. In theory, this approach could work. In practice, it is
too hard, as we have to write proofs by hand. It may happen that we finish 90%
of a proof just to find that our candidate for $IndInv$ was not good enough.

We do not have to go the hard way. Instead, we can just use a model checker for
TLA<sup>+</sup> to quickly iterate on a candidate for an inductive invariant for
a small set of resource managers. This is exactly what we did for our [paper at
OOPSLA19][oopsla19] at some point in 2018. I guess, it should be available in
the [artifact][oopsla19-artifact]. In the modern version of [Apalache][], the
inductive invariant looks like this:

{% github_embed
  https://raw.githubusercontent.com/apalache-mc/apalache/984f380c3f24b754f0809064ec8e203a873543dc/test/tla/TwoPhaseTypedInv.tla
  lean 4-31
 %}

By running Apalache, we can make sure that our invariant is inductive for three
resource managers:

```sh
$ apalache-mc check --length=0  --init=Init --inv=IndInv MC3_TwoPhaseTypedInv.tla
...
Total time: 1.282 sec
$ apalache-mc check --length=1 --init=IndInv --inv=IndInv MC3_TwoPhaseTypedInv.tla
...
The outcome is: NoError
Total time: 1.621 sec
$ apalache-mc check --length=0  --init=IndInv --inv=TCConsistent MC3_TwoPhaseTypedInv.tla
...
The outcome is: NoError
Total time: 1.342 sec
```

We can do the same for 7, 20, and even 50 resource managers. However, as we
increase the number of resource managers, the model checker takes longer to
verify the properties. For example, checking inductiveness for 20 resource
managers takes about 8 seconds, compared to just 2 seconds for 3 resource
managers.

To make sure that the model checker is not just printing `"NoError"` but also
doing something useful, we replace `"committed"` with `"aborted"` in the last
line of `IndInv`.  In this case, the model checker immediately gives us a
counterexample to induction.

```sh
$ apalache-mc check --length=1 --inv=IndInv --init=IndInv MC3_TwoPhaseTypedInv.tla
...
Check the trace in: [...]/violation1.tla
State 1: state invariant 5 violated.
Total time: 1.760 sec
```

Basically, this is how we speed up the guess-work of finding an inductive
invariant with the model checker.

Interestingly, we can remove the line `/\ TCConsistent`, and Apalache does not
complain. This constraint is redundant. It is actually great that we have
removed this redundant constraint, as it would take us much longer to write
interactive proofs with this constraint in place.

We `IndInv` as a conjunction of six lemmas in Lean, as it is easier to reason
about the invariant this way:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
  lean 69-71
 %}

You can find all six lemmas in [InductiveProofs.lean][]. For example, here
is how we write `lemma1`:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
  lean 23-24
 %}

If you look carefully at `lemma5` and `lemma6` in [InductiveProofs.lean][], you
will notice that they also have redundancies. I missed that and this resulted in
a lot of extra work when writing proofs. It would only take several seconds to
check with Apalache, whether we could remove these subformulas. More on that
later.

## 4. Proving the inductive step in Lean 4

Now that we know our invariant is inductive for small sets of resource managers,
we have good chances of proving the inductive step of `invariant`. The
transition relation `tp_next` is a disjunction of seven smaller subformulas such
as `tm_commit` and `tm_abort`. Further, `invariant` is a conjunction of six
lemmas.

Thus, our plan is very simple: Prove inductiveness for each of the seven actions
and each of the six lemmas. This gives us 42 facts to prove. While this sounds
like a lot of work, the good news is that proving 42 smaller lemmas is easier
than proving one huge theorem.

Actually, the above decomposition is not hand-waiving. Our theorem
`invariant_is_inductive` is proven exactly by this decomposition. Below you can
see the first six cases: 

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
  lean 1120-1144
 %}

(If you know how to write the above decomposition nicer in Lean, please [leave a
comment][leave-comment] below.)

Now we have to prove 42 lemmas by **writing the proofs**. For example, here is
the proof for the action `tm_commit` and `lemma1`:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
  lean 198-206
 %}

As you can see, this was an easy one. It took me just 10 minutes to write it.
Actually, closer to the end of the proof, I was writing similar proofs in 1-2
minutes. You can find the remaining 41 proofs in [InductiveProofs.lean][]. The
plot below shows the total proof efforts:

{% include webp.html
    src="two-phase-inductive-proof.png"
    alt="Proof efforts for inductiveness" %}

There are several things to notice:

 1. Over a half of the lemmas took me less than 15 minutes each.
 1. Ten lemmas took me from 20 to 30 minutes.
 1. Six lemmas took me about 1 hour.
 1. There is one outlier that required over three hours.

I am not exactly sure what happened with the lemma that took me so long. It was
the second one I had to prove, so I might have spent a lot of time just figuring
out the right tactics to use. If you look at the proof of
[`invariant_is_inductive_tm_commit_lemma2`][invariant_is_inductive_tm_commit_lemma2],
it involves reasoning with universal quantifiers and some small proofs by
contradiction. If I were to write it again now, it probably would not take
nearly as much time.

Something interesting happened when I proved about 80% of the lemmas. I got
stuck. This is not really surprising, as I was at the core argument that
required reasoning about one resource manager being in the `Aborted` state and
another resource manager receiving a `Commit` message. Basically, I was
struggling with an argument for the constraints in the commented out section
below:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
  lean 44-53
 %}

The commented out disjunction is not exactly wrong. The second disjunct of it
implies the first disjunct. However, the second disjunct is much harder to
reason about. The solution? Just remove it.

Once I have removed the redundant part, the proof was quick and easy:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
  lean 968-977
 %}

A similar redundancy was present in `lemma6`. So I removed it, too. By removing
these two redundancies, I have cut the proofs in half! Small differences in
proof goals may have big implications on the proof complexity.

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
  lean 55-62
 %}

## 5. Proving consistency with the inductive invariant

Once we are sure that `invariant` is inductive, it is easy to prove that it
implies `consistency`. It took me just 15 minutes to write the proof:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
  lean 73-93
 %}

## 6. Proving the inductive base

Finally, we have to show that the initial states also satisfy `invariant`. Here
is just the header of the theorem:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
  lean 153-154
 %}

Initially, I thought that the proof would not be harder than the proof of the
inductive step, since there are fewer conditions to prove. Essentially, we have
to prove six lemmas for the initial states. In total, I think it took me about
three hours to finish the proofs.

This proof had an unexpected complication. I had to show that the initialization
of the hash map `rmState` sets all resource managers to the state `Working`.
Here is the header of this lemma:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
  lean 138-141
 %}

I observed similar issues when going through Isabelle tutorials many years ago,
so I remember that sometimes one had to generalize the proof goal. This is
exactly what happened here. In the end, the proof required this additional
lemma:

{% github_embed
  https://raw.githubusercontent.com/konnov/leanda/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
  lean 97-103
 %}

Interestingly, this is the only proof that explicitly uses the `induction`
tactic. Even though we have been reasoning about an inductive invariant, we did
not need to go into induction. Coming from TLA<sup>+</sup>, this is interesting.
I had to use `foldl` to initialize the hash map, since Lean does not seem to
have convenient primitives such as the function constructor.  In
TLA<sup>+</sup>, we would just use:

```tlaplus
  [ rm ∈ RM |-> "working"]
```

The function constructor does not introduce explicit iteration and actually has
the semantics of what I had to prove with the lemma `init_rm_state_post`.  (To
be precise, it also specifies the function domain.) Perhaps, we could introduce
higher-level primitives in Lean 4 to deal with this.  If you know of a better
alternative to using `HashMap`, please let me know in the
[comments][leave-comment].

<a name="end"></a>

[Igor Konnov]: https://konnov.phd
[Ilya Sergey]: https://ilyasergey.net/
[Thomas Pani]: https://thpani.net/[Lean]: https://github.com/leanprover/lean4
[Veil]: https://github.com/verse-lab/veil/
[Lean]: https://github.com/leanprover/lean4
[two-phase-typed]: https://github.com/apalache-mc/apalache/blob/main/test/tla/TwoPhaseTyped.tla
[two-phase-tla]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla
[fun-spec]: #32-functional-specification-in-lean
[sys-spec]: #33-system-level-specification-in-lean
[prop-spec]: #7-propositional-specification-in-lean
[spec-sim]: #5-randomised-simulator-in-lean
[spec-pbt]: #6-property-based-testing-in-lean
[Functional.lean]: https://github.com/konnov/leanda/blob/main/twophase/Twophase/Functional.lean
[System.lean]: https://github.com/konnov/leanda/blob/main/twophase/Twophase/System.lean
[Propositional.lean]: https://github.com/konnov/leanda/blob/main/twophase/Twophase/Propositional.lean
[Apalache]: https://github.com/apalache-mc/apalache
[happy to help]: {{ 'contact/' | relative_url }}
[ben-or-mc]: {% link _posts/2024-11-03-ben-or.md %}
[lean-two-phase]: {% link _posts/2025-04-25-lean-two-phase.md %}
[tla-consistency]: https://github.com/tlaplus/Examples/blob/37236893f14527b4fc9f3963891eb2316c3de62e/specifications/transaction_commit/TCommit.tla#L54-L60
[PropositionalProofs.lean]: https://github.com/konnov/leanda/blob/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/PropositionalProofs.lean
[InductiveProofs.lean]: https://github.com/konnov/leanda/blob/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean
[oopsla19-artifact]: https://zenodo.org/records/3370071
[oopsla19]: https://2019.splashcon.org/details/splash-2019-oopsla/7/TLA-Model-Checking-Made-Symbolic
[TwoPhaseTypedInv.tla]: https://github.com/apalache-mc/apalache/blob/main/test/tla/TwoPhaseTypedInv.tla
[Lean plugin]: https://marketplace.visualstudio.com/items?itemName=leanprover.lean4
[lean-tp]: https://lean-lang.org/theorem_proving_in_lean4/title_page.html
[inductive-proof-effort]: {{ site.baseurl }}/img/two-phase-inductive-proof.png
[proof-schema]: {{ site.baseurl }}/img/two-phase-proof-schema.png
[invariant_is_inductive_tm_commit_lemma2]: https://github.com/konnov/leanda/blob/199b26cb022dfa05c3e7c1576384dcea8a0bd648/twophase/Twophase/InductiveProofs.lean#L394-L429
[2pc-ivy]: https://github.com/verse-lab/veil/blob/main/Examples/IvyBench/TwoPhaseCommit.lean
[IronFleet]: https://dl.acm.org/doi/10.1145/2815400.2815428
[Verdi]: https://github.com/uwplse/verdi
[Disel]: https://ilyasergey.net/papers/disel-popl18.pdf
[leave-comment]: #end
[Bythos]: https://github.com/verse-lab/bythos