import Mathlib.Algebra.Order.Archimedean.Real.Basic
import LeanP1.InfoTheory.Capacity

/-!
# Shannon's channel coding theorem

Stage 6 of the channel-capacity project: the *statement* of the noisy-channel coding
theorem, with the operational notions it needs.

A block code of length `n` for `M` messages is an encoder `Fin M → (Fin n → X)` together
with a decoder `(Fin n → Y) → Fin M`.  Sending message `m` through `n` independent uses of
`W` and decoding gives an error probability; the code's maximal error is the sup over `m`.
A rate `R` (in nats per channel use) is *achievable* if there are codes of every block
length with rate at least `R` whose maximal error tends to `0`.

## Main statements

* `Channel.isAchievable_of_lt_capacity` (achievability, **not yet proved**): every `R < C(W)`
  is achievable.  The classical proof is Shannon's random-coding argument.
* The converse `Channel.IsAchievable.le_capacity` and the full statement
  `Channel.operationalCapacity_eq_capacity` live in `LeanP1.InfoTheory.Converse`.

Everything else in this file (basic properties of error probabilities, achievability of
nonpositive rates, monotonicity) is proved.
-/

namespace LeanP1

namespace Channel

open Real Finset Filter Topology

variable {X Y : Type*} [Fintype Y]

/-- A block code of length `n` for the message set `Fin M`. -/
structure Code (X Y : Type*) (n M : ℕ) where
  /-- The encoder: each message is sent as a word of length `n`. -/
  enc : Fin M → (Fin n → X)
  /-- The decoder: each received word is interpreted as a message. -/
  dec : (Fin n → Y) → Fin M

/-- The rate of a code with `M` messages and block length `n`, in nats per channel use. -/
noncomputable def rate (n M : ℕ) : ℝ := log M / n

namespace Code

variable {n M : ℕ}

/-- The probability that message `m` is decoded incorrectly after `n` uses of `W`. -/
noncomputable def errorProb (W : Channel X Y) (c : Code X Y n M) (m : Fin M) : ℝ :=
  ∑ y ∈ univ.filter (fun y => c.dec y ≠ m), W.pow n (c.enc m) y

/-- The maximal error probability of the code over all messages. -/
noncomputable def maxError (W : Channel X Y) (c : Code X Y n M) : ℝ :=
  ⨆ m, c.errorProb W m

theorem errorProb_nonneg (W : Channel X Y) (c : Code X Y n M) (m : Fin M) :
    0 ≤ c.errorProb W m :=
  sum_nonneg fun y _ => (W.pow n (c.enc m)).nonneg y

theorem errorProb_le_one (W : Channel X Y) (c : Code X Y n M) (m : Fin M) :
    c.errorProb W m ≤ 1 := by
  calc c.errorProb W m ≤ ∑ y, W.pow n (c.enc m) y :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun y _ _ => (W.pow n (c.enc m)).nonneg y
    _ = 1 := (W.pow n (c.enc m)).sum_coe

theorem maxError_nonneg (W : Channel X Y) (c : Code X Y n M) : 0 ≤ c.maxError W :=
  Real.iSup_nonneg fun m => c.errorProb_nonneg W m

theorem maxError_le_one (W : Channel X Y) (c : Code X Y n M) : c.maxError W ≤ 1 :=
  Real.iSup_le (fun m => c.errorProb_le_one W m) zero_le_one

theorem errorProb_le_maxError (W : Channel X Y) (c : Code X Y n M) (m : Fin M) :
    c.errorProb W m ≤ c.maxError W :=
  le_ciSup (Set.finite_range _).bddAbove m

end Code

/-- A rate `R` is achievable if there are codes of every block length `n` with rate at least
`R` whose maximal error probability tends to `0` as `n → ∞`. -/
def IsAchievable (W : Channel X Y) (R : ℝ) : Prop :=
  ∃ (M : ℕ → ℕ) (c : ∀ n, Code X Y n (M n)),
    (∀ n, 0 < n → R ≤ rate n (M n)) ∧
    Tendsto (fun n => (c n).maxError W) atTop (𝓝 0)

/-- The operational capacity: the supremum of all achievable rates. -/
noncomputable def operationalCapacity (W : Channel X Y) : ℝ := sSup {R | W.IsAchievable R}

/-- Any rate below an achievable rate is achievable. -/
theorem IsAchievable.mono {W : Channel X Y} {R R' : ℝ} (h : W.IsAchievable R) (hR : R' ≤ R) :
    W.IsAchievable R' := by
  obtain ⟨M, c, hrate, hlim⟩ := h
  exact ⟨M, c, fun n hn => hR.trans (hrate n hn), hlim⟩

/-- Nonpositive rates are achievable, using the trivial one-message code. -/
theorem isAchievable_of_nonpos [Nonempty X] (W : Channel X Y) {R : ℝ} (hR : R ≤ 0) :
    W.IsAchievable R := by
  classical
  let c : ∀ n, Code X Y n 1 := fun _ => ⟨fun _ _ => Classical.arbitrary X, fun _ => 0⟩
  refine ⟨fun _ => 1, c, ?_, ?_⟩
  · intro n _
    simp [rate, hR]
  · have h0 : ∀ n (m : Fin 1), (c n).errorProb W m = 0 := by
      intro n m
      rw [Fin.eq_zero m]
      simp [c, Code.errorProb]
    have hmax : ∀ n, (c n).maxError W = 0 := by
      intro n
      simp [Code.maxError, h0]
    simp only [hmax]
    exact tendsto_const_nhds

/-- **Achievability** (Shannon): every rate below the capacity is achievable.
The classical proof is the random-coding argument: pick a codebook at random from the
capacity-achieving input distribution and decode by joint typicality.  Not yet formalised. -/
theorem isAchievable_of_lt_capacity [Fintype X] (W : Channel X Y) {R : ℝ} (hR : R < W.capacity) :
    W.IsAchievable R := by
  sorry

end Channel

end LeanP1
