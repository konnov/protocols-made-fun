/**
 * This specification captures the control loop of the PRNG.
 * It totally abstracts all data away.
 *
 * Igor Konnov, 2024.
 */
module prng1 {
    type PC = | InLoop | Done

    var pc: PC

    action init: bool = {
        pc' = InLoop
    }

    action step = any {
        loop,
        postLoop,
    }

    action loop: bool = all {
        pc == InLoop,
        pc' = InLoop,
    }

    action postLoop: bool = all {
        pc == InLoop,
        pc' = Done,
    }
}
