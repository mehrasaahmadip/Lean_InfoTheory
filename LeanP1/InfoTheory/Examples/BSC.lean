import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import LeanP1.InfoTheory.Capacity

/-!
# Example: the binary symmetric channel

The binary symmetric channel `bsc ε` flips its input bit with probability `ε`.
We compute its capacity exactly: `C(bsc ε) = log 2 - binEntropy ε` (in nats).

The proof has the two halves typical of any capacity computation:
* upper bound: for every input `p`, `I(p, W) = H(pW) - binEntropy ε ≤ log 2 - binEntropy ε`,
  because the output lives on the two-element type `Bool`;
* lower bound: the uniform input produces a uniform output, so it attains the bound.
-/

namespace LeanP1

open Real Finset

namespace Dist

/-- The Bernoulli distribution on `Bool` with `P(true) = q`. -/
noncomputable def bernoulli (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Dist Bool where
  pmf := fun b => if b then q else 1 - q
  nonneg := by
    intro b
    cases b <;> simp <;> linarith
  sum_eq_one := by
    rw [Fintype.sum_bool]; norm_num

@[simp] theorem bernoulli_true {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    bernoulli q h0 h1 true = q := rfl

@[simp] theorem bernoulli_false {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    bernoulli q h0 h1 false = 1 - q := rfl

/-- The entropy of a Bernoulli distribution is Mathlib's binary entropy function. -/
theorem entropy_bernoulli {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (bernoulli q h0 h1).entropy = binEntropy q := by
  rw [entropy, Fintype.sum_bool, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rfl

end Dist

namespace Channel

/-- The binary symmetric channel with crossover probability `ε`:
the output equals the input with probability `1 - ε` and is flipped with probability `ε`. -/
noncomputable def bsc (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : Channel Bool Bool :=
  fun x => Dist.bernoulli (if x then 1 - ε else ε)
    (by cases x <;> simp <;> linarith) (by cases x <;> simp <;> linarith)

variable {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)

theorem bsc_entropy (x : Bool) : (bsc ε h0 h1 x).entropy = binEntropy ε := by
  cases x <;> simp [bsc, Dist.entropy_bernoulli]

/-- Every input symbol sees the same noise, so `H(Y | X) = binEntropy ε` for every input law. -/
theorem bsc_condEntropy (p : Dist Bool) : (bsc ε h0 h1).condEntropy p = binEntropy ε := by
  simp only [condEntropy, bsc_entropy, ← sum_mul, p.sum_coe, one_mul]

/-- A uniform input produces a uniform output. -/
theorem bsc_output_uniform : (bsc ε h0 h1).output Dist.uniform = Dist.uniform := by
  ext y
  simp only [output_apply, Dist.uniform_apply, Fintype.card_bool, Fintype.sum_bool]
  cases y <;> simp [bsc] <;> ring

theorem bsc_mutualInfo_le (p : Dist Bool) :
    (bsc ε h0 h1).mutualInfo p ≤ log 2 - binEntropy ε := by
  rw [mutualInfo, bsc_condEntropy]
  have h := ((bsc ε h0 h1).output p).entropy_le_log_card
  simp only [Fintype.card_bool, Nat.cast_ofNat] at h
  linarith

theorem bsc_mutualInfo_uniform :
    (bsc ε h0 h1).mutualInfo Dist.uniform = log 2 - binEntropy ε := by
  rw [mutualInfo, bsc_condEntropy, bsc_output_uniform, Dist.entropy_uniform, Fintype.card_bool]
  norm_num

/-- **Capacity of the binary symmetric channel**: `C(bsc ε) = log 2 - binEntropy ε`. -/
theorem capacity_bsc : (bsc ε h0 h1).capacity = log 2 - binEntropy ε :=
  le_antisymm (capacity_le fun p => bsc_mutualInfo_le h0 h1 p)
    (le_capacity Dist.uniform (bsc_mutualInfo_uniform h0 h1).ge)

end Channel

end LeanP1
