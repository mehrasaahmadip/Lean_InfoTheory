# Lean_InfoTheory

A formalization of Shannon's channel capacity in Lean 4 with Mathlib, for discrete
memoryless channels over finite alphabets.

## What is proved

The files under `LeanP1/InfoTheory/`, in reading order:

- `Dist.lean`: probability distributions on a finite type, point mass, uniform law.
- `Entropy.lean`: Shannon entropy in nats, with `0 ≤ H(p) ≤ log (card α)` by Jensen's inequality.
- `Channel.lean`: channels as functions `X → Dist Y`, the output law, product laws, and the
  `n`-fold memoryless extension `W.pow n`.
- `MutualInfo.lean`: conditional entropy and mutual information, `I ≥ 0`, the chain rule,
  `I ≤ H(X)` and `I ≤ H(Y)`, relabeling of the input alphabet.
- `Capacity.lean`: the capacity `C(W) = sup_p I(p, W)` and its bounds.
- `Examples/BSC.lean`: the capacity of the binary symmetric channel is `log 2 − h(ε)`.
- `CodingTheorem.lean`: block codes, error probability, rate, achievable rates, operational capacity.
- `Fano.lean`: Fano's inequality for block codes, proved without conditional distributions.
- `ProductChannel.lean`: subadditivity of entropy and of capacity under products, and
  `C(W.pow n) ≤ n · C(W)`.
- `Converse.lean`: the converse of the coding theorem, every achievable rate is at most `C(W)`.

The only remaining `sorry` is the achievability half of the coding theorem,
`Channel.isAchievable_of_lt_capacity` in `CodingTheorem.lean`. Everything else is checked by Lean
and depends only on the standard axioms.

## Design choices

- Alphabets are finite types, so every probability is a finite sum.
- A distribution is a structure with a real-valued mass function, nonnegativity, and total mass one.
- Entropy uses the natural logarithm via Mathlib's `Real.negMulLog`; capacities are in nats.
- Conditional distributions are avoided: inequalities such as Fano's are proved by summing the
  pointwise Gibbs inequality `negMulLog a ≤ -a log b + b - a`.

## Building

Requires [elan](https://github.com/leanprover/elan). Then run `lake exe cache get` to download the
precompiled Mathlib, followed by `lake build`. To check a theorem's axioms, add a line such as
`#print axioms LeanP1.Channel.capacity_bsc` to a file and read the Infoview in VS Code.

## Website

Every push to `main` builds the library and renders it with
[Referee](https://github.com/LeanMachineLearning/exposition) into a site with one page per
declaration and overview pages for theorems, claims, sorries and upstream trust, at
[mehrasaahmadip.github.io/Lean_InfoTheory](https://mehrasaahmadip.github.io/Lean_InfoTheory/).
The headline results shown on its Claims page are listed in `formalization.yaml`.
