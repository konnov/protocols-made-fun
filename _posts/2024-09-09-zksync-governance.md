---
layout: post
title: "Specification and Model-checking of the ZKsync Governance Protocol"
date: 2024-09-09
categories: zksync matterlabs quint specification modelchecking
quint: true
math: true
---

**Authors: Denis Kolegov ([Matter Labs][]), [Igor Konnov][].**

After our success in [specification and model checking of the ChonkyBFT
consensus][chonky-quint] in Quint, we have decided to apply Quint and its tools
to a slightly different domain: governance contracts in Solidity. This blogpost
summarizes our experience and highlights the important modeling decisions we
made.



[chonky-quint]: https://protocols-made-fun.com/consensus/matterlabs/quint/specification/modelchecking/2024/07/29/chonkybft.html
[Igor Konnov]: https://konnov.phd
[Matter Labs]: https://matter-labs.io/