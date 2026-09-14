import LeanP1.InfoTheory.Fano

/-!
# Product channels and the capacity of `W.pow n`

Stage 8 of the channel-capacity project: `C(W.pow n) ≤ n * C(W)`.

## Strategy

* `Dist.prod`, `Channel.prod`: two distributions / channels used side by side.
* `Dist.entropy_le_entropy_map_fst_add_map_snd`: subadditivity `H(A, B) ≤ H(A) + H(B)` for any
  law on a product type, via the pointwise Gibbs inequality against the product of the marginals.
* `Channel.mutualInfo_prod_le`: `I(p, W₁ × W₂) ≤ I(p₁, W₁) + I(p₂, W₂)` with `p₁, p₂` the
  marginals of `p`; hence `Channel.capacity_prod_le`.
* `Channel.mapOutput`: relabeling the output alphabet through a bijection leaves the mutual
  information unchanged.
* `Channel.pow_succ_eq`: `W.pow (n + 1)` is `W × W.pow n` up to relabeling of inputs and
  outputs, and `Channel.capacity_pow_le` follows by induction.
-/

namespace LeanP1

open Real Finset

/-! ### Product distributions and subadditivity of entropy -/

/-- Gibbs inequality against a product weight `b * c`, including the degenerate cases
`b = 0` or `c = 0` (then the hypotheses force `a = 0`). -/
theorem _root_.Real.negMulLog_le_sub_mul_log {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a ≤ b) (hac : a ≤ c) :
    negMulLog a ≤ -a * log b - a * log c + b * c - a := by
  rcases hb.eq_or_lt with rfl | hb'
  · have : a = 0 := le_antisymm hab ha
    subst this; simp
  rcases hc.eq_or_lt with rfl | hc'
  · have : a = 0 := le_antisymm hac ha
    subst this; simp
  have h := Real.negMulLog_le_of_pos ha (mul_pos hb' hc')
  rw [log_mul hb'.ne' hc'.ne'] at h
  linarith

namespace Dist

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The product of two independent distributions. -/
noncomputable def prod (p : Dist α) (q : Dist β) : Dist (α × β) where
  pmf := fun ab => p ab.1 * q ab.2
  nonneg := fun ab => mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_eq_one := by
    simp only [Fintype.sum_prod_type, ← mul_sum, q.sum_coe, mul_one, p.sum_coe]

@[simp] theorem prod_apply (p : Dist α) (q : Dist β) (ab : α × β) :
    p.prod q ab = p ab.1 * q ab.2 := rfl

/-- The entropy of a product distribution is the sum of the entropies. -/
theorem entropy_prod (p : Dist α) (q : Dist β) : (p.prod q).entropy = p.entropy + q.entropy := by
  simp only [entropy, prod_apply, Fintype.sum_prod_type, negMulLog_mul, sum_add_distrib,
    ← sum_mul, ← mul_sum, sum_coe, one_mul]

section Marginals

theorem map_fst_apply [DecidableEq α] (r : Dist (α × β)) (a : α) :
    r.map Prod.fst a = ∑ b, r (a, b) := by
  rw [map_apply, Fintype.sum_prod_type, sum_comm]
  simp

theorem map_snd_apply [DecidableEq β] (r : Dist (α × β)) (b : β) :
    r.map Prod.snd b = ∑ a, r (a, b) := by
  rw [map_apply, Fintype.sum_prod_type]
  simp

/-- Subadditivity of entropy: `H(A, B) ≤ H(A) + H(B)` for any law `r` on `α × β`. -/
theorem entropy_le_entropy_map_fst_add_map_snd [DecidableEq α] [DecidableEq β]
    (r : Dist (α × β)) :
    r.entropy ≤ (r.map Prod.fst).entropy + (r.map Prod.snd).entropy := by
  have key : ∀ ab : α × β, negMulLog (r ab) ≤
      -(r ab) * log (r.map Prod.fst ab.1) - r ab * log (r.map Prod.snd ab.2)
      + r.map Prod.fst ab.1 * r.map Prod.snd ab.2 - r ab := by
    intro ab
    obtain ⟨a, b⟩ := ab
    dsimp only
    refine negMulLog_le_sub_mul_log (r.nonneg _) ((r.map _).nonneg _) ((r.map _).nonneg _) ?_ ?_
    · rw [map_fst_apply]
      exact single_le_sum (fun b' _ => r.nonneg (a, b')) (mem_univ b)
    · rw [map_snd_apply]
      exact single_le_sum (fun a' _ => r.nonneg (a', b)) (mem_univ a)
  have hsum := sum_le_sum fun ab (_ : ab ∈ univ) => key ab
  simp only [sum_sub_distrib, sum_add_distrib] at hsum
  have h1 : ∑ ab : α × β, -(r ab) * log (r.map Prod.fst ab.1) = (r.map Prod.fst).entropy := by
    simp only [entropy, negMulLog, Fintype.sum_prod_type, neg_mul, sum_neg_distrib, ← sum_mul,
      ← map_fst_apply]
  have h2 : ∑ ab : α × β, r ab * log (r.map Prod.snd ab.2) = -(r.map Prod.snd).entropy := by
    simp only [entropy, negMulLog, Fintype.sum_prod_type_right, neg_mul, sum_neg_distrib,
      ← sum_mul, ← map_snd_apply, neg_neg]
  have h3 : ∑ ab : α × β, r.map Prod.fst ab.1 * r.map Prod.snd ab.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, (r.map Prod.snd).sum_coe, mul_one]
    exact (r.map Prod.fst).sum_coe
  have h4 := r.sum_coe
  have hH : r.entropy = ∑ ab, negMulLog (r ab) := rfl
  linarith

end Marginals

/-! ### Relabeling through a bijection -/

theorem map_equiv_apply [DecidableEq β] (σ : α ≃ β) (p : Dist α) (b : β) :
    p.map σ b = p (σ.symm b) := by
  rw [map_apply, sum_eq_single (σ.symm b)]
  · simp
  · intro a _ ha
    have : σ a ≠ b := fun h => ha (by rw [← h, Equiv.symm_apply_apply])
    simp [this]
  · intro h
    exact absurd (mem_univ _) h

/-- Entropy is invariant under relabeling by a bijection. -/
theorem entropy_map_equiv [DecidableEq β] (σ : α ≃ β) (p : Dist α) :
    (p.map σ).entropy = p.entropy := by
  simp only [entropy, map_equiv_apply]
  exact Equiv.sum_comp σ.symm (fun a => negMulLog (p a))

end Dist

namespace Channel

/-! ### Product channels -/

section Prod

variable {X₁ X₂ Y₁ Y₂ : Type*} [Fintype Y₁] [Fintype Y₂]

/-- Two channels used side by side, on pairs of inputs. -/
noncomputable def prod (W₁ : Channel X₁ Y₁) (W₂ : Channel X₂ Y₂) : Channel (X₁ × X₂) (Y₁ × Y₂) :=
  fun x => (W₁ x.1).prod (W₂ x.2)

@[simp] theorem prod_apply (W₁ : Channel X₁ Y₁) (W₂ : Channel X₂ Y₂) (x : X₁ × X₂) (y : Y₁ × Y₂) :
    Channel.prod W₁ W₂ x y = W₁ x.1 y.1 * W₂ x.2 y.2 := rfl

variable [Fintype X₁] [Fintype X₂]

theorem condEntropy_prod (W₁ : Channel X₁ Y₁) (W₂ : Channel X₂ Y₂) (p : Dist (X₁ × X₂)) :
    (Channel.prod W₁ W₂).condEntropy p
      = condEntropy (fun x => W₁ x.1) p + condEntropy (fun x => W₂ x.2) p := by
  simp only [condEntropy, Channel.prod, Dist.entropy_prod, mul_add, sum_add_distrib]

theorem map_fst_output_prod [DecidableEq Y₁] (W₁ : Channel X₁ Y₁) (W₂ : Channel X₂ Y₂)
    (p : Dist (X₁ × X₂)) :
    ((Channel.prod W₁ W₂).output p).map Prod.fst = output (fun x => W₁ x.1) p := by
  ext y₁
  rw [Dist.map_fst_apply]
  simp only [output_apply, prod_apply]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← mul_sum, ← mul_sum, Dist.sum_coe, mul_one]

theorem map_snd_output_prod [DecidableEq Y₂] (W₁ : Channel X₁ Y₁) (W₂ : Channel X₂ Y₂)
    (p : Dist (X₁ × X₂)) :
    ((Channel.prod W₁ W₂).output p).map Prod.snd = output (fun x => W₂ x.2) p := by
  ext y₂
  rw [Dist.map_snd_apply]
  simp only [output_apply, prod_apply]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← mul_sum, ← sum_mul, Dist.sum_coe, one_mul]

/-- Mutual information is subadditive for product channels: with `p₁, p₂` the marginals of the
joint input law `p`, `I(p, W₁ × W₂) ≤ I(p₁, W₁) + I(p₂, W₂)`. -/
theorem mutualInfo_prod_le [DecidableEq X₁] [DecidableEq X₂] (W₁ : Channel X₁ Y₁)
    (W₂ : Channel X₂ Y₂) (p : Dist (X₁ × X₂)) :
    (Channel.prod W₁ W₂).mutualInfo p
      ≤ W₁.mutualInfo (p.map Prod.fst) + W₂.mutualInfo (p.map Prod.snd) := by
  classical
  have h := Dist.entropy_le_entropy_map_fst_add_map_snd ((Channel.prod W₁ W₂).output p)
  rw [map_fst_output_prod, map_snd_output_prod, output_comp W₁ Prod.fst p,
    output_comp W₂ Prod.snd p] at h
  rw [mutualInfo, mutualInfo, mutualInfo, condEntropy_prod, condEntropy_comp W₁ Prod.fst p,
    condEntropy_comp W₂ Prod.snd p]
  linarith

/-- The capacity of a product channel is at most the sum of the capacities. -/
theorem capacity_prod_le [Nonempty X₁] [Nonempty X₂] (W₁ : Channel X₁ Y₁) (W₂ : Channel X₂ Y₂) :
    (Channel.prod W₁ W₂).capacity ≤ W₁.capacity + W₂.capacity := by
  classical
  exact capacity_le fun p => (mutualInfo_prod_le W₁ W₂ p).trans
    (add_le_add (W₁.mutualInfo_le_capacity _) (W₂.mutualInfo_le_capacity _))

end Prod

/-! ### Relabeling the output alphabet -/

section MapOutput

variable {X Y Y' : Type*} [Fintype X] [Fintype Y] [Fintype Y'] [DecidableEq Y']

/-- Relabel the output alphabet of a channel through a bijection. -/
noncomputable def mapOutput (σ : Y ≃ Y') (W : Channel X Y) : Channel X Y' :=
  fun x => (W x).map σ

theorem output_mapOutput (σ : Y ≃ Y') (W : Channel X Y) (p : Dist X) :
    (mapOutput σ W).output p = (W.output p).map σ := by
  ext y'
  simp only [output_apply, mapOutput, Dist.map_equiv_apply]

theorem condEntropy_mapOutput (σ : Y ≃ Y') (W : Channel X Y) (p : Dist X) :
    (mapOutput σ W).condEntropy p = W.condEntropy p := by
  simp only [condEntropy, mapOutput, Dist.entropy_map_equiv]

/-- Mutual information is unchanged by relabeling the outputs. -/
theorem mutualInfo_mapOutput (σ : Y ≃ Y') (W : Channel X Y) (p : Dist X) :
    (mapOutput σ W).mutualInfo p = W.mutualInfo p := by
  rw [mutualInfo, mutualInfo, output_mapOutput, Dist.entropy_map_equiv, condEntropy_mapOutput]

end MapOutput

/-! ### `W.pow (n + 1)` as a product -/

/-- Split a word of length `n + 1` into its first letter and the remaining word. -/
def finSuccSplit (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp
  right_inv p := by
    ext <;> simp

@[simp] theorem finSuccSplit_apply {α : Type*} {n : ℕ} (f : Fin (n + 1) → α) :
    finSuccSplit α n f = (f 0, fun i => f i.succ) := rfl

variable {X Y : Type*} [Fintype Y]

/-- `n + 1` uses of `W` are one use of `W` alongside `n` uses, up to relabeling. -/
theorem pow_succ_eq [DecidableEq Y] (W : Channel X Y) (n : ℕ) :
    W.pow (n + 1) = fun x =>
      mapOutput (finSuccSplit Y n).symm (Channel.prod W (W.pow n)) (finSuccSplit X n x) := by
  funext x
  ext y
  simp only [pow_apply, mapOutput, Dist.map_equiv_apply, Equiv.symm_symm, prod_apply,
    finSuccSplit_apply, Fin.prod_univ_succ]

/-- **Capacity of the memoryless extension**: `C(W.pow n) ≤ n * C(W)`. -/
theorem capacity_pow_le [Fintype X] [Nonempty X] (W : Channel X Y) (n : ℕ) :
    (W.pow n).capacity ≤ n * W.capacity := by
  classical
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    refine capacity_le fun p => ?_
    have h := (W.pow 0).mutualInfo_le_log_card p
    simpa using h
  | succ n ih =>
    calc (W.pow (n + 1)).capacity ≤ (Channel.prod W (W.pow n)).capacity := by
          refine capacity_le fun p => ?_
          rw [pow_succ_eq,
            mutualInfo_comp (mapOutput (finSuccSplit Y n).symm (Channel.prod W (W.pow n)))
              (finSuccSplit X n) p,
            mutualInfo_mapOutput]
          exact mutualInfo_le_capacity _ _
      _ ≤ W.capacity + (W.pow n).capacity := capacity_prod_le W (W.pow n)
      _ ≤ W.capacity + n * W.capacity := by linarith
      _ = ((n + 1 : ℕ) : ℝ) * W.capacity := by push_cast; ring

end Channel

end LeanP1
