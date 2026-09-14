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

## GitHub configuration

The workflows in `.github/workflows` build the project on every push and publish documentation
to GitHub Pages. To enable the documentation site: under **Settings → Actions → General**,
allow GitHub Actions to create and approve pull requests; under **Settings → Pages**, select
"GitHub Actions" as the source.
