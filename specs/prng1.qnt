/**
 * This specification captures the control loop of the PRNG.
 * It totally abstracts all data away.
 *
 * Igor Konnov, 2024.
 */
module prng1 {
    type PC = | Loop | Done

    var pc: PC

    action init: bool = {
        pc' = Loop
    }

    action step = any {
        loop,
        postLoop,
    }

    action loop: bool = all {
        pc == Loop,
        pc' = Loop,
    }

    action postLoop: bool = all {
        pc == Loop,
        pc' = Done,
    }
}
