---
layout: post
title: "Running TLC with non-standard modules"
date: 2025-10-09
categories: tlaplus
tlaplus: true
math: true
shell: true
---

**Author:** [Igor Konnov][]

**Tags:** specification tlaplus apalache tlc

This must be my shortest blog post ever. I just wanted to run [TLC][] to check
a specification that uses [Apalache][] modules. For example, the typed version
of two-phase commit [MC3_TwoPhaseTyped.tla][] uses the module [Variants][].
Sure, TLC can do that, but it requires a small trick.

Let's do it step by step for [MC3_TwoPhaseTyped.tla][]. Say, we want to see
an example of all participants committing:

```tlaplus
RMAllCommittedEx ==
    ~(\A rm \in RM: rmState[rm] = "committed")
```

**Step 1.** Checkout the Apalache repository, if you don't have it already:

```shell
$ git clone git@github.com:apalache-mc/apalache.git
$ export APALACHE_HOME=$(pwd)/apalache
```

**Step 2.** Download TLA<sup>+</sup> Tools:

```shell
$ wget https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar
$ export TLC_HOME=$(pwd)
```

**Step 3.** Introduce a configuration file `MC3_TwoPhaseTyped.cfg` with the
following content:

```
$ cd $APALACHE_HOME/test/tla
$ cat >MC3_TwoPhaseTyped.cfg <<EOF
INIT Init
NEXT Next
INVARIANT RMAllCommittedEx
EOF
```

**Step 4.** Run TLC with the option `-cp`, which extends the Java
classpath. TLC will look for non-standard modules in the specified directory,
that is, in the directory `${APALACHE_HOME}/src/tla`. *This is the trick!*

```shell
$ java -cp ${TLC_HOME}/tla2tools.jar:${APALACHE_HOME}/src/tla \
  "-XX:+UseParallelGC" tlc2.TLC \
  -config MC3_TwoPhaseTyped.cfg MC3_TwoPhaseTyped.tla
``` 

As expected, TLC finds an example of `RMAllCommittedEx`:

```
Running breadth-first search Model-Checking...
...
State 11: <Next line 16, col 1 to line 16, col 22 of module MC3_TwoPhaseTyped>
/\ msgs = { [tag |-> "Commit", value |-> "0_OF_NIL"],
  [tag |-> "Prepared", value |-> "0_OF_RM"],
  [tag |-> "Prepared", value |-> "1_OF_RM"],
  [tag |-> "Prepared", value |-> "2_OF_RM"] }
/\ rmState = [0_OF_RM |-> "committed", 1_OF_RM |-> "committed", 2_OF_RM |-> "committed"]
/\ tmState = "committed"
/\ tmPrepared = {"0_OF_RM", "1_OF_RM", "2_OF_RM"}
...
1119 states generated, 287 distinct states found, 7 states left on queue.
```

<a name="end"></a>
## Bottom line

This is it! If you have any questions, please feel free to reach out. I'm
[happy to help][].

[Igor Konnov]: https://konnov.phd
[Hans Kamp]: https://en.wikipedia.org/wiki/Hans_Kamp
[Apalache]: https://apalache-mc.org/
[TLC]: https://github.com/tlaplus/tlaplus
[happy to help]: {{ 'contact/' | relative_url }}
[MC3_TwoPhaseTyped.tla]: https://github.com/apalache-mc/apalache/blob/main/test/tla/MC3_TwoPhaseTyped.tla
[Variants]: https://apalache-mc.org/docs/lang/variants.html
[leave-comment]: #end