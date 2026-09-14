import Mathlib.Tactic

/-!
# Finite probability distributions

Stage 1 of the channel-capacity project.

A `Dist α` is a probability mass function on a finite type `α`: a function to `ℝ`
that is nonnegative and sums to `1`.  We work with finite alphabets only, so every
probability is a finite sum and no measure theory is needed.

## Main definitions

* `Dist α`: probability distributions on a finite type.
* `Dist.pure a`: the point mass at `a`.
* `Dist.uniform`: the uniform distribution.

## Basic lemmas

* `Dist.le_one`: every probability is at most one.
* `Dist.exists_pos`: some element has positive probability.
* `Dist.pure_apply_ne`: the point mass is zero away from its point.
-/

namespace LeanP1

/-- A probability distribution on a finite type `α`. -/
structure Dist (α : Type*) [Fintype α] where
  /-- The probability mass function. -/
  pmf : α → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ a, 0 ≤ pmf a
  /-- Probabilities sum to one. -/
  sum_eq_one : ∑ a, pmf a = 1

namespace Dist

variable {α : Type*} [Fintype α]

/-- Write `p a` for the probability of `a` under `p`. -/
instance : CoeFun (Dist α) (fun _ => α → ℝ) := ⟨Dist.pmf⟩

@[simp] theorem pmf_eq_coe (p : Dist α) (a : α) : p.pmf a = p a := rfl

/-- Two distributions are equal if they agree pointwise. -/
@[ext] theorem ext {p q : Dist α} (h : ∀ a, p a = q a) : p = q := by
  cases p; cases q
  simp only [mk.injEq]
  exact funext h

theorem sum_coe (p : Dist α) : ∑ a, p a = 1 := p.sum_eq_one

/-- Every probability is at most one. -/
theorem le_one (p : Dist α) (a : α) : p a ≤ 1 := by
  calc p a ≤ ∑ b, p b := Finset.single_le_sum (fun b _ => p.nonneg b) (Finset.mem_univ a)
    _ = 1 := p.sum_coe

/-- Some element has positive probability.
Proof by contradiction: if every probability were `≤ 0`, then (being also `≥ 0`) they would
all be `0`, so the total mass would be `0`, contradicting `sum_eq_one`. -/
theorem exists_pos (p : Dist α) : ∃ a, 0 < p a := by
  by_contra h
  push Not at h
  -- `h : ∀ a, p a ≤ 0`
  have hzero : ∑ a, p a = 0 :=
    Finset.sum_eq_zero fun a _ => le_antisymm (h a) (p.nonneg a)
  linarith [p.sum_coe]

/-! ### Point mass -/

section Pure

variable [DecidableEq α]

/-- The point mass at `a`: probability one at `a`, zero elsewhere. -/
def pure (a : α) : Dist α where
  pmf := fun b => if b = a then 1 else 0
  nonneg := by
    intro b
    split_ifs <;> norm_num
  sum_eq_one := by simp

@[simp] theorem pure_apply (a b : α) : pure a b = if b = a then 1 else 0 := rfl

@[simp] theorem pure_apply_self (a : α) : pure a a = 1 := by simp

/-- The point mass vanishes away from its point. -/
theorem pure_apply_ne {a b : α} (h : b ≠ a) : pure a b = 0 := by
  simp [h]

end Pure

/-! ### Uniform distribution -/

section Uniform

variable [Nonempty α]

/-- The uniform distribution: every element has probability `1 / |α|`. -/
noncomputable def uniform : Dist α where
  pmf := fun _ => (Fintype.card α : ℝ)⁻¹
  nonneg := by
    intro _
    positivity
  sum_eq_one := by
    have h : (Fintype.card α : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [Finset.sum_const, Finset.card_univ, h]

@[simp] theorem uniform_apply (a : α) : (uniform : Dist α) a = (Fintype.card α : ℝ)⁻¹ := rfl

end Uniform

end Dist

end LeanP1
