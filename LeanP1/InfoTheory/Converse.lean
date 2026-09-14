import LeanP1.InfoTheory.ProductChannel

/-!
# The converse of the channel coding theorem

Stage 9 of the channel-capacity project: no rate above the capacity is achievable.

## Proof

Take codes `c n` with `M n` messages, rate at least `R`, and maximal error `λ n → 0`.
Fano's inequality (`Code.log_card_mul_one_sub_avgError_le`) and `capacity_pow_le` give, for
every `n ≥ 1`,

  `log (M n) * (1 - P_e n) ≤ n * C(W) + log 2`,

so `R * (1 - P_e n) ≤ C(W) + log 2 / n`.  Since `P_e n ≤ λ n → 0`, letting `n → ∞` gives
`R ≤ C(W)`.

## Main results

* `Channel.IsAchievable.le_capacity`: the converse.
* `Channel.operationalCapacity_eq_capacity`: Shannon's theorem, modulo the achievability half.
-/

namespace LeanP1

namespace Channel

open Real Finset Filter Topology

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- **Converse** (Shannon): every achievable rate is at most the capacity. -/
theorem IsAchievable.le_capacity [Nonempty X] {W : Channel X Y} {R : ℝ} (h : W.IsAchievable R) :
    R ≤ W.capacity := by
  classical
  obtain ⟨M, c, hrate, hlim⟩ := h
  have hY : Nonempty Y := (W (Classical.arbitrary X)).nonempty
  have hMpos : ∀ n, 0 < M n := fun n => Fin.pos ((c n).dec fun _ => Classical.arbitrary Y)
  -- the average error is squeezed between `0` and the maximal error
  have ha0 : ∀ n, 0 ≤ (c n).avgError W := fun n => (c n).avgError_nonneg W
  have ha1 : ∀ n, (c n).avgError W ≤ (c n).maxError W := fun n =>
    have : NeZero (M n) := ⟨(hMpos n).ne'⟩
    (c n).avgError_le_maxError W
  have ha : Tendsto (fun n => (c n).avgError W) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim ha0 ha1
  -- the two sides of the key inequality converge to `R` and to `C(W)`
  have hL : Tendsto (fun n => R * (1 - (c n).avgError W)) atTop (𝓝 R) := by
    have := (tendsto_const_nhds (x := R)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub ha)
    simpa using this
  have hU : Tendsto (fun n : ℕ => W.capacity + log 2 / n) atTop (𝓝 W.capacity) := by
    have := (tendsto_const_nhds (x := W.capacity)).add
      ((tendsto_const_nhds (x := log 2)).div_atTop tendsto_natCast_atTop_atTop)
    simpa using this
  refine le_of_tendsto_of_tendsto hL hU (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  dsimp only
  have : NeZero (M n) := ⟨(hMpos n).ne'⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1a : 0 ≤ 1 - (c n).avgError W := by linarith [ha1 n, (c n).maxError_le_one W]
  have hRn : R * n ≤ log (M n) := by
    have := hrate n hn
    simp only [rate] at this
    exact (le_div_iff₀ hn').1 this
  have hF := (c n).log_card_mul_one_sub_avgError_le W
  have hpow := W.capacity_pow_le n
  have key : R * (1 - (c n).avgError W) * n ≤ n * W.capacity + log 2 := by
    calc R * (1 - (c n).avgError W) * n = R * n * (1 - (c n).avgError W) := by ring
      _ ≤ log (M n) * (1 - (c n).avgError W) := mul_le_mul_of_nonneg_right hRn h1a
      _ ≤ (W.pow n).capacity + log 2 := hF
      _ ≤ n * W.capacity + log 2 := by linarith
  rw [show W.capacity + log 2 / n = (n * W.capacity + log 2) / n by
        rw [add_div, mul_div_cancel_left₀ _ hn'.ne'],
    le_div_iff₀ hn']
  exact key

/-- **Shannon's channel coding theorem**: the operational capacity, i.e. the supremum of the
achievable rates, equals the information capacity `sup_p I(p, W)`.
The achievability half `isAchievable_of_lt_capacity` is not yet formalised. -/
theorem operationalCapacity_eq_capacity [Nonempty X] (W : Channel X Y) :
    W.operationalCapacity = W.capacity := by
  have hbdd : BddAbove {R | W.IsAchievable R} :=
    ⟨W.capacity, fun _ hR => IsAchievable.le_capacity hR⟩
  apply le_antisymm
  · exact csSup_le ⟨0, W.isAchievable_of_nonpos le_rfl⟩ fun _ hR => IsAchievable.le_capacity hR
  · calc W.capacity = sSup (Set.Iio W.capacity) := csSup_Iio.symm
      _ ≤ sSup {R | W.IsAchievable R} :=
          csSup_le_csSup hbdd ⟨W.capacity - 1, by simp⟩
            fun _ hR => W.isAchievable_of_lt_capacity hR

end Channel

end LeanP1
