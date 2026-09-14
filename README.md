# Lean_InfoTheory

A formalization of Shannon's channel capacity in Lean 4 with Mathlib, for discrete
memoryless channels over finite alphabets.

## What is proved

| File | Content |
| --- | --- |
| `LeanP1/InfoTheory/Dist.lean` | Probability distributions on a finite type: point mass, uniform law, basic lemmas. |
| `LeanP1/InfoTheory/Entropy.lean` | Shannon entropy in nats; `0 ≤ H(p) ≤ log (card α)` (Jensen), entropy of point mass and uniform law. |
| `LeanP1/InfoTheory/Channel.lean` | Channels `X → Dist Y`, output law, product laws, the `n`-fold memoryless extension `W.pow n`. |
| `LeanP1/InfoTheory/MutualInfo.lean` | Conditional entropy, mutual information, `I ≥ 0`, chain rule, `I ≤ H(X)`, `I ≤ H(Y)`, relabeling of inputs. |
| `LeanP1/InfoTheory/Capacity.lean` | Capacity `C(W) = sup_p I(p, W)` and its bounds. |
| `LeanP1/InfoTheory/Examples/BSC.lean` | Capacity of the binary symmetric channel: `log 2 − h(ε)`. |
| `LeanP1/InfoTheory/CodingTheorem.lean` | Block codes, error probability, rate, achievable rates, operational capacity. |
| `LeanP1/InfoTheory/Fano.lean` | Fano's inequality for block codes, with no conditional distributions. |
| `LeanP1/InfoTheory/ProductChannel.lean` | Subadditivity of entropy and capacity under products; `C(W.pow n) ≤ n · C(W)`. |
| `LeanP1/InfoTheory/Converse.lean` | The converse of the coding theorem: every achievable rate is at most `C(W)`. |

The only remaining `sorry` is the achievability half of the coding theorem,
`Channel.isAchievable_of_lt_capacity` in `CodingTheorem.lean`. Everything else is checked by
Lean and depends only on the standard axioms (`#print axioms` reports no `sorryAx`).

## Design choices

* Alphabets are finite types (`Fintype`), so every probability is a finite sum.
* A distribution is a structure with a real-valued mass function, nonnegativity, and total mass one.
* Entropy uses the natural logarithm via Mathlib's `Real.negMulLog`; capacities are in nats.
* Conditional distributions are avoided: inequalities such as Fano's are proved by summing a
  pointwise Gibbs inequality `negMulLog a ≤ -a log b + b - a`.

## Building

Requires [elan](https://github.com/leanprover/elan). Then:

```sh
lake exe cache get   # download the precompiled Mathlib
lake build
```

To check a theorem's axioms, add for example `#print axioms LeanP1.Channel.capacity_bsc` to a
file and read the Infoview in VS Code.

## Website

Every push to `main` builds the library and renders it with
[Referee](https://github.com/LeanMachineLearning/exposition) into a site with one page per
declaration (statement, proof, dependency graph) and overview pages for theorems, claims,
sorries and upstream trust:

[mehrasaahmadip.github.io/Lean_InfoTheory](https://mehrasaahmadip.github.io/Lean_InfoTheory/)

The list of headline results shown on the site's Claims page is `formalization.yaml`.

Publishing needs GitHub Pages enabled with "GitHub Actions" as the source, under
**Settings → Pages**. GitHub Pages is only available for public repositories on the free plan.
