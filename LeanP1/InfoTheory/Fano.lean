import LeanP1.InfoTheory.CodingTheorem

/-!
# Fano's inequality for block codes

Stage 7 of the channel-capacity project: the information-theoretic heart of the converse.

Fix a code `c` with `M ≥ 1` messages and block length `n`, and send a uniformly random
message through `n` uses of `W`.  Let `P_e` be the average error probability.  Then

  `log M - I(message ; received word) ≤ log 2 + P_e * log M`.

Combined with `I ≤ C(W.pow n)` this gives `log M * (1 - P_e) ≤ C(W.pow n) + log 2`.

## Proof idea

We avoid conditional distributions entirely.  The pointwise Gibbs inequality
`negMulLog a ≤ -a * log b + b - a` (for `a ≥ 0 < b`) is summed over the joint law `J` of
(message, word) against the "guess" weights `b = q(word) * t(message, word)`, where `q` is the
law of the word and `t` puts mass `1/2 + 1/(2M)` on the decoded message and `1/(2M)` elsewhere.
Since `∑_message t = 1`, the sum of `b` is `1`, and `-log t ≤ log 2 + [error] * log M`.

## Main results

* `Channel.Code.fano`: Fano's inequality as stated above.
* `Channel.Code.log_card_mul_one_sub_avgError_le`: `log M * (1 - P_e) ≤ C(W.pow n) + log 2`.
-/

namespace LeanP1

open Real Finset

/-! ### A pointwise Gibbs inequality -/

/-- Pointwise Gibbs inequality: for `0 ≤ a` and `0 < b`, `negMulLog a ≤ -a * log b + b - a`.
Summed over a distribution `a` against weights `b`, this reads `H(a) ≤ -∑ a log b + ∑ b - 1`. -/
theorem _root_.Real.negMulLog_le_of_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    negMulLog a ≤ -a * log b + b - a := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp [hb.le]
  · have h := self_sub_one_le_mul_log (div_nonneg ha hb.le)
    rw [log_div ha'.ne' hb.ne'] at h
    have key : a - b ≤ a * log a - a * log b := by
      calc a - b = (a / b - 1) * b := by rw [sub_mul, div_mul_cancel₀ a hb.ne', one_mul]
        _ ≤ a / b * (log a - log b) * b := mul_le_mul_of_nonneg_right h hb.le
        _ = a * log a - a * log b := by
            rw [mul_comm, ← mul_assoc, mul_div_cancel₀ a hb.ne']; ring
    rw [negMulLog]
    linarith

namespace Channel

variable {X Y : Type*} [Fintype Y] {n M : ℕ}

instance {M : ℕ} [NeZero M] : Nonempty (Fin M) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩⟩

namespace Code

/-- The channel seen by the messages: message `m` is encoded and sent through `n` uses of `W`. -/
noncomputable def msgChannel (W : Channel X Y) (c : Code X Y n M) :
    Channel (Fin M) (Fin n → Y) :=
  fun m => W.pow n (c.enc m)

@[simp] theorem msgChannel_apply (W : Channel X Y) (c : Code X Y n M) (m : Fin M) :
    c.msgChannel W m = W.pow n (c.enc m) := rfl

/-- Average error probability over uniformly distributed messages. -/
noncomputable def avgError (W : Channel X Y) (c : Code X Y n M) : ℝ :=
  ∑ m, (M : ℝ)⁻¹ * c.errorProb W m

theorem avgError_nonneg (W : Channel X Y) (c : Code X Y n M) : 0 ≤ c.avgError W :=
  sum_nonneg fun m _ => mul_nonneg (by positivity) (c.errorProb_nonneg W m)

theorem avgError_le_maxError [NeZero M] (W : Channel X Y) (c : Code X Y n M) :
    c.avgError W ≤ c.maxError W := by
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  calc c.avgError W = ∑ m, (M : ℝ)⁻¹ * c.errorProb W m := rfl
    _ ≤ ∑ _m : Fin M, (M : ℝ)⁻¹ * c.maxError W :=
        sum_le_sum fun m _ =>
          mul_le_mul_of_nonneg_left (c.errorProb_le_maxError W m) (by positivity)
    _ = c.maxError W := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ hM, one_mul]

/-! ### The guess weights -/

private theorem guess_pos (hM : (0 : ℝ) < M) (b : Prop) [Decidable b] :
    0 < (if b then (2 : ℝ)⁻¹ else 0) + (2 * (M : ℝ))⁻¹ := by
  have h : 0 ≤ (if b then (2 : ℝ)⁻¹ else 0) := by split_ifs <;> norm_num
  have h' : 0 < (2 * (M : ℝ))⁻¹ := by positivity
  linarith

private theorem neg_log_guess_le (hM : (0 : ℝ) < M) (b : Prop) [Decidable b] :
    -log ((if b then (2 : ℝ)⁻¹ else 0) + (2 * (M : ℝ))⁻¹) ≤ log 2 + if b then 0 else log M := by
  split_ifs with hb
  · have h1 : (2 : ℝ)⁻¹ ≤ 2⁻¹ + (2 * (M : ℝ))⁻¹ := by
      have : 0 < (2 * (M : ℝ))⁻¹ := by positivity
      linarith
    have h2 := log_le_log (by norm_num) h1
    rw [log_inv] at h2
    linarith
  · rw [zero_add, log_inv, log_mul two_ne_zero hM.ne']
    linarith

private theorem sum_guess (hM : (0 : ℝ) < M) (m₀ : Fin M) :
    ∑ m : Fin M, ((if m₀ = m then (2 : ℝ)⁻¹ else 0) + (2 * (M : ℝ))⁻¹) = 1 := by
  simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [mul_inv, mul_comm (2 : ℝ)⁻¹, ← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]
  norm_num

/-! ### Fano's inequality -/

/-- **Fano's inequality** (crude form) for a block code.  With uniformly distributed messages,
`log M - I(message ; received word) ≤ log 2 + P_e * log M`, where `P_e` is the average error. -/
theorem fano [NeZero M] (W : Channel X Y) (c : Code X Y n M) :
    log M - (c.msgChannel W).mutualInfo Dist.uniform ≤ log 2 + c.avgError W * log M := by
  classical
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  set V := c.msgChannel W with hV
  set p : Dist (Fin M) := Dist.uniform with hp
  rw [mutualInfo_eq_add_sub, Dist.entropy_uniform, Fintype.card_fin]
  suffices h : (V.joint p).entropy ≤ (V.output p).entropy + (log 2 + c.avgError W * log M) by
    linarith
  -- Pointwise bound, from the Gibbs inequality with weights `q(y) * t(m, y)`.
  have key : ∀ my : Fin M × (Fin n → Y),
      negMulLog (V.joint p my) ≤
        -(V.joint p my) * log (V.output p my.2)
        + V.joint p my * (log 2 + if c.dec my.2 = my.1 then 0 else log M)
        + V.output p my.2 * ((if c.dec my.2 = my.1 then (2 : ℝ)⁻¹ else 0) + (2 * (M : ℝ))⁻¹)
        - V.joint p my := by
    intro my
    obtain ⟨m, y⟩ := my
    dsimp only
    have hJ : 0 ≤ V.joint p (m, y) := (V.joint p).nonneg _
    have hJq : V.joint p (m, y) ≤ V.output p y := by
      simp only [joint_apply, output_apply]
      exact single_le_sum (fun m' _ => mul_nonneg (p.nonneg m') ((V m').nonneg y)) (mem_univ m)
    rcases ((V.output p).nonneg y).eq_or_lt with hq | hq
    · have hJ0 : V.joint p (m, y) = 0 := le_antisymm (hJq.trans hq.ge) hJ
      rw [hJ0, ← hq]
      simp
    · have ht := guess_pos hM (c.dec y = m)
      have hb : 0 < V.output p y * ((if c.dec y = m then (2 : ℝ)⁻¹ else 0) + (2 * (M : ℝ))⁻¹) :=
        mul_pos hq ht
      have h1 := Real.negMulLog_le_of_pos hJ hb
      rw [log_mul hq.ne' ht.ne'] at h1
      have h3 := mul_le_mul_of_nonneg_left (neg_log_guess_le hM (c.dec y = m)) hJ
      linarith
  have hsum := sum_le_sum fun my (_ : my ∈ univ) => key my
  rw [sum_sub_distrib, sum_add_distrib, sum_add_distrib] at hsum
  -- The four sums on the right.
  have hS1 : ∑ my : Fin M × (Fin n → Y), -(V.joint p my) * log (V.output p my.2)
      = (V.output p).entropy := by
    simp only [Dist.entropy, negMulLog, Fintype.sum_prod_type_right, joint_apply, output_apply,
      neg_mul, sum_neg_distrib, ← sum_mul]
  have hS2 : ∑ my : Fin M × (Fin n → Y),
      V.joint p my * (log 2 + if c.dec my.2 = my.1 then 0 else log M)
      = log 2 + c.avgError W * log M := by
    simp only [mul_add, sum_add_distrib, ← sum_mul, (V.joint p).sum_coe, one_mul]
    congr 1
    rw [Fintype.sum_prod_type]
    simp only [joint_apply, avgError, errorProb, sum_filter, sum_mul, mul_sum, hp,
      Dist.uniform_apply, Fintype.card_fin, hV, msgChannel_apply]
    refine sum_congr rfl fun m _ => sum_congr rfl fun y _ => ?_
    by_cases h : c.dec y = m <;> simp [h]
  have hS3 : ∑ my : Fin M × (Fin n → Y),
      V.output p my.2 * ((if c.dec my.2 = my.1 then (2 : ℝ)⁻¹ else 0) + (2 * (M : ℝ))⁻¹) = 1 := by
    rw [Fintype.sum_prod_type_right]
    simp only [← mul_sum, sum_guess hM, mul_one]
    exact (V.output p).sum_coe
  have hS4 := (V.joint p).sum_coe
  have hJ : (V.joint p).entropy = ∑ my, negMulLog (V.joint p my) := rfl
  linarith

/-- Fano's inequality in terms of the capacity of the `n`-fold channel:
`log M * (1 - P_e) ≤ C(W.pow n) + log 2`. -/
theorem log_card_mul_one_sub_avgError_le [Fintype X] [NeZero M] (W : Channel X Y)
    (c : Code X Y n M) :
    log M * (1 - c.avgError W) ≤ (W.pow n).capacity + log 2 := by
  classical
  have h1 := c.fano W
  have h2 : (c.msgChannel W).mutualInfo Dist.uniform ≤ (W.pow n).capacity :=
    mutualInfo_comp_le_capacity (W.pow n) c.enc Dist.uniform
  linarith

end Code

end Channel

end LeanP1
