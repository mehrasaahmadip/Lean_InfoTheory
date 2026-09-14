import LeanP1.InfoTheory.Dist

/-!
# Discrete memoryless channels

Stage 3 of the channel-capacity project.

A channel from an input alphabet `X` to an output alphabet `Y` assigns to each input
symbol a distribution on output symbols.  We write `W x y` for the probability of
receiving `y` when `x` was sent.

## Main definitions

* `Channel X Y`: channels, i.e. functions `X → Dist Y`.
* `Channel.output W p`: the distribution of the output when the input has law `p`.
* `Dist.pi`: product of independent distributions.
* `Channel.pow W n`: `n` independent uses of `W` (the memoryless extension).
-/

namespace LeanP1

open Finset

/-- A discrete memoryless channel: each input symbol gives a distribution on outputs. -/
abbrev Channel (X Y : Type*) [Fintype Y] := X → Dist Y

namespace Dist

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]

/-- The product of independent distributions on the coordinates of a product type. -/
noncomputable def pi (p : ∀ i, Dist (β i)) : Dist (∀ i, β i) where
  pmf := fun b => ∏ i, p i (b i)
  nonneg := fun b => prod_nonneg fun i _ => (p i).nonneg (b i)
  sum_eq_one := by
    rw [show (∑ b : ∀ i, β i, ∏ i, p i (b i)) = ∏ i, ∑ j, p i j from
      (Fintype.prod_sum fun i j => p i j).symm]
    simp [sum_coe]

@[simp] theorem pi_apply (p : ∀ i, Dist (β i)) (b : ∀ i, β i) : pi p b = ∏ i, p i (b i) := rfl

end Dist

namespace Channel

variable {X Y : Type*} [Fintype Y]

section Output

variable [Fintype X]

/-- The output distribution `pW` when the input is distributed according to `p`:
`(pW) y = ∑ x, p x * W x y`. -/
noncomputable def output (W : Channel X Y) (p : Dist X) : Dist Y where
  pmf := fun y => ∑ x, p x * W x y
  nonneg := fun y => sum_nonneg fun x _ => mul_nonneg (p.nonneg x) ((W x).nonneg y)
  sum_eq_one := by
    rw [sum_comm]
    simp_rw [← mul_sum, Dist.sum_coe, mul_one]
    exact p.sum_coe

@[simp] theorem output_apply (W : Channel X Y) (p : Dist X) (y : Y) :
    W.output p y = ∑ x, p x * W x y := rfl

end Output

/-- `n` independent uses of the channel `W`, acting on words of length `n`. -/
noncomputable def pow (W : Channel X Y) (n : ℕ) : Channel (Fin n → X) (Fin n → Y) :=
  fun x => Dist.pi fun i => W (x i)

@[simp] theorem pow_apply (W : Channel X Y) (n : ℕ) (x : Fin n → X) (y : Fin n → Y) :
    W.pow n x y = ∏ i, W (x i) (y i) := rfl

end Channel

end LeanP1
