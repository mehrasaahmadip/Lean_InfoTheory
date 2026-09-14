import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import LeanP1.InfoTheory.Dist

/-!
# Shannon entropy

Stage 2 of the channel-capacity project.

The entropy of a finite distribution `p` is `H(p) = ∑ a, -(p a) * log (p a)`, in nats.
Mathlib provides the real function `Real.negMulLog x = -x * log x` together with its
concavity, which is all we need.

## Main results

* `Dist.entropy_nonneg`: `0 ≤ H(p)`.
* `Dist.entropy_le_log_card`: `H(p) ≤ log |α|` (Jensen's inequality).
* `Dist.entropy_pure`: a point mass has entropy `0`.
* `Dist.entropy_uniform`: the uniform distribution has entropy `log |α|`.
-/

namespace LeanP1

namespace Dist

open Real Finset

variable {α : Type*} [Fintype α]

/-- A distribution can only live on a nonempty type (otherwise the total mass would be `0`). -/
theorem nonempty (p : Dist α) : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := p.sum_coe
  simp at this

/-- Shannon entropy in nats: `H(p) = ∑ a, negMulLog (p a)`. -/
noncomputable def entropy (p : Dist α) : ℝ := ∑ a, negMulLog (p a)

theorem entropy_nonneg (p : Dist α) : 0 ≤ p.entropy :=
  sum_nonneg fun a _ => negMulLog_nonneg (p.nonneg a) (p.le_one a)

/-- Entropy is maximised by the uniform distribution: `H(p) ≤ log |α|`.
This is Jensen's inequality for the concave function `negMulLog`. -/
theorem entropy_le_log_card (p : Dist α) : p.entropy ≤ log (Fintype.card α) := by
  have := p.nonempty
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hJ := concaveOn_negMulLog.le_map_sum (t := univ)
    (w := fun _ : α => (Fintype.card α : ℝ)⁻¹) (p := fun a => p a)
    (fun _ _ => by positivity)
    (by simp [sum_const, card_univ])
    (fun a _ => p.nonneg a)
  simp only [smul_eq_mul, ← mul_sum, p.sum_coe, mul_one] at hJ
  have key : negMulLog (Fintype.card α : ℝ)⁻¹
      = (Fintype.card α : ℝ)⁻¹ * log (Fintype.card α) := by
    rw [negMulLog, log_inv]; ring
  rw [key] at hJ
  exact le_of_mul_le_mul_left hJ (inv_pos.mpr hn)

@[simp] theorem entropy_pure [DecidableEq α] (a : α) : (pure a).entropy = 0 := by
  unfold entropy
  refine sum_eq_zero fun b _ => ?_
  by_cases h : b = a <;> simp [h]

theorem entropy_uniform [Nonempty α] : (uniform : Dist α).entropy = log (Fintype.card α) := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [entropy, uniform_apply, negMulLog, log_inv, sum_const, card_univ]

end Dist

end LeanP1
