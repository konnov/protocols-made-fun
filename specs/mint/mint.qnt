module mint {
    // amounts should fit into 6 bits
    pure val MAX_INT = 63
    pure val MAX_INT_PLUS_1 = 64

    var minter: int
    var burner: int
    var totalSupply: int

    pure def wrapInt(i: int): int = {
        if (i < 0) MAX_INT + i else i % MAX_INT_PLUS_1
    }

    action init = all {
        minter' = 5,
        burner' = 0,
        totalSupply' = 5,
    }

    action step = any {
        mint,
        transfer,
        burn,
    }

    action mint = {
        nondet amount = 1.to(MAX_INT).oneOf()
        all {
            2 * amount <= totalSupply,
            totalSupply + amount <= MAX_INT,
            minter' = wrapInt(minter + amount),
            burner' = burner,
            totalSupply' = totalSupply + amount,
        }
    }

    action transfer = {
        nondet amount = 1.to(MAX_INT).oneOf()
        all {
            amount <= minter,
            minter' = wrapInt(minter - amount),
            burner' = wrapInt(burner + amount),
            totalSupply' = totalSupply,
        }
    }

    action burn = {
        val amount = (burner / 2) + 1
        all {
            amount > 0,
            burner' = wrapInt(burner - amount),
            minter' = minter,
            totalSupply' = totalSupply - amount,
        }
    }

    val nonNegativeInv = all {
        burner >= 0,
        minter >= 0,
    }

    val totalSupplyInv = {
        totalSupply == minter + burner
    }
}