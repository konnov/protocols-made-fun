module prng2 {
    pure val WORD_BOUND: int = 2^8
    pure val MAX_NWORDS: int = 3

    type PC = | InLoop | Done

    var pc: PC
    var bound: int
    var input: int
    var output: int
    var base: int

    action init: bool = all {
        nondet generated = 1.to(WORD_BOUND^MAX_NWORDS).oneOf()
        all {
            bound' = generated,
            input' = generated,
        },
        output' = 0,
        base' = 1,
        pc' = InLoop,
    }

    action step = any {
        loop,
        postLoop,
    }

    action loop: bool = all {
        pc == InLoop,
        input >= WORD_BOUND,
        // The original code uses a pseudo-random number generator.
        // For the purposes of testing the algorithm, the actual distribution
        // is irrelevant. Hence, we simply use non-determinism.
        nondet generated = 0.to(WORD_BOUND - 1).oneOf()
        output' = output * WORD_BOUND + generated,
        input' = input / WORD_BOUND,
        base' = base * WORD_BOUND,
        bound' = bound,
        pc' = InLoop,
    }

    action postLoop: bool = all {
        pc == InLoop,
        input < WORD_BOUND,
        nondet generated = 0.to(WORD_BOUND - 1).oneOf()
        output' = (generated % input) * base + output,
        input' = input,
        base' = base,
        bound' = bound,
        pc' = Done,
    }

    /// The only reasonable invariant we can come up with:
    /// The generated value should not go out of bounds.
    val safety = and {
        output >= 0,
        output < bound
    }

    /// If we manage to prove that `missingOutput` is an invariant,
    /// then we know that it is impossible to generate bound - 1
    /// when bound == 0xff0001.
    val missingOutput = {
        (pc == Done and bound == 0xff0001) implies (output != 0xff0000)
    }
}
