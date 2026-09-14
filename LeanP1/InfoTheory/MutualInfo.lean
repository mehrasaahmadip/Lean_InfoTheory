import LeanP1.InfoTheory.Entropy
import LeanP1.InfoTheory.Channel

/-!
# Conditional entropy and mutual information

Stage 4 of the channel-capacity project.

For a channel `W` and input distribution `p`:

* `H(Y | X) = ∑ x, p x * H(W x)` is the conditional entropy of the output given the input;
* `I(p, W) = H(pW) - H(Y | X)` is the mutual information between input and output.

## Main results

* `Channel.condEntropy_le_entropy_output`: conditioning reduces entropy, `H(Y | X) ≤ H(Y)`.
  This is Jensen's inequality for `negMulLog` and is the heart of `0 ≤ I(p, W)`.
* `Channel.mutualInfo_nonneg`: `0 ≤ I(p, W)`.
* `Channel.mutualInfo_le_log_card`: `I(p, W) ≤ log |Y|`.
* `Channel.entropy_joint`: chain rule `H(X, Y) = H(X) + H(Y | X)`.
* `Channel.mutualInfo_le_entropy`: `I(p, W) ≤ H(p)`, hence `I(p, W) ≤ log |X|`.
* `Channel.mutualInfo_comp`: relabeling the inputs through a map `f` is the same as pushing
  the input law forward along `f`.
-/

namespace LeanP1

namespace Channel

open Real Finset

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Conditional entropy `H(Y | X)` of the output given the input. -/
noncomputable def condEntropy (W : Channel X Y) (p : Dist X) : ℝ :=
  ∑ x, p x * (W x).entropy

/-- Mutual information `I(p, W) = H(Y) - H(Y | X)` between the input and the output. -/
noncomputable def mutualInfo (W : Channel X Y) (p : Dist X) : ℝ :=
  (W.output p).entropy - W.condEntropy p

theorem condEntropy_nonneg (W : Channel X Y) (p : Dist X) : 0 ≤ W.condEntropy p :=
  sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (W x).entropy_nonneg

theorem condEntropy_le_log_card (W : Channel X Y) (p : Dist X) :
    W.condEntropy p ≤ log (Fintype.card Y) := by
  calc W.condEntropy p = ∑ x, p x * (W x).entropy := rfl
    _ ≤ ∑ x, p x * log (Fintype.card Y) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (W x).entropy_le_log_card (p.nonneg x)
    _ = log (Fintype.card Y) := by rw [← sum_mul, p.sum_coe, one_mul]

/-- Conditioning reduces entropy: `H(Y | X) ≤ H(Y)`.  Jensen's inequality for the concave
function `negMulLog`, applied for each output symbol `y` to the weights `p x`. -/
theorem condEntropy_le_entropy_output (W : Channel X Y) (p : Dist X) :
    W.condEntropy p ≤ (W.output p).entropy := by
  have h : ∀ y, ∑ x, p x * negMulLog (W x y) ≤ negMulLog (∑ x, p x * W x y) := fun y => by
    simpa only [smul_eq_mul] using
      concaveOn_negMulLog.le_map_sum (t := univ) (w := fun x => p x) (p := fun x => W x y)
        (fun x _ => p.nonneg x) p.sum_coe (fun x _ => (W x).nonneg y)
  calc W.condEntropy p = ∑ x, ∑ y, p x * negMulLog (W x y) := by
        simp only [condEntropy, Dist.entropy, mul_sum]
    _ = ∑ y, ∑ x, p x * negMulLog (W x y) := sum_comm
    _ ≤ ∑ y, negMulLog (∑ x, p x * W x y) := sum_le_sum fun y _ => h y
    _ = (W.output p).entropy := by simp only [Dist.entropy, output_apply]

theorem mutualInfo_nonneg (W : Channel X Y) (p : Dist X) : 0 ≤ W.mutualInfo p :=
  sub_nonneg.mpr (W.condEntropy_le_entropy_output p)

theorem mutualInfo_le_entropy_output (W : Channel X Y) (p : Dist X) :
    W.mutualInfo p ≤ (W.output p).entropy :=
  sub_le_self _ (W.condEntropy_nonneg p)

theorem mutualInfo_le_log_card (W : Channel X Y) (p : Dist X) :
    W.mutualInfo p ≤ log (Fintype.card Y) :=
  (W.mutualInfo_le_entropy_output p).trans (W.output p).entropy_le_log_card

/-! ### The symmetric bound `I(p, W) ≤ H(p)` via the joint distribution -/

/-- `negMulLog` is subadditive on nonnegative families:
`negMulLog (∑ i, a i) ≤ ∑ i, negMulLog (a i)`.  (Each `a i ≤ ∑ a`, so `log (a i) ≤ log (∑ a)`.) -/
theorem _root_.Real.negMulLog_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    negMulLog (∑ i ∈ s, a i) ≤ ∑ i ∈ s, negMulLog (a i) := by
  have h1 : negMulLog (∑ i ∈ s, a i) = ∑ i ∈ s, -(a i) * log (∑ j ∈ s, a j) := by
    rw [negMulLog, ← sum_neg_distrib, sum_mul]
  rw [h1]
  refine sum_le_sum fun i hi => ?_
  rw [negMulLog]
  rcases (ha i hi).eq_or_lt with h0 | h0
  · simp [← h0]
  · have hle : log (a i) ≤ log (∑ j ∈ s, a j) := log_le_log h0 (single_le_sum ha hi)
    nlinarith [mul_le_mul_of_nonneg_left hle h0.le]

/-- The joint distribution of the input `x ∼ p` and the output `y ∼ W x`. -/
noncomputable def joint (W : Channel X Y) (p : Dist X) : Dist (X × Y) where
  pmf := fun xy => p xy.1 * W xy.1 xy.2
  nonneg := fun xy => mul_nonneg (p.nonneg _) ((W _).nonneg _)
  sum_eq_one := by
    simp only [Fintype.sum_prod_type, ← mul_sum, Dist.sum_coe, mul_one]

@[simp] theorem joint_apply (W : Channel X Y) (p : Dist X) (xy : X × Y) :
    W.joint p xy = p xy.1 * W xy.1 xy.2 := rfl

/-- Chain rule for entropy: `H(X, Y) = H(X) + H(Y | X)`. -/
theorem entropy_joint (W : Channel X Y) (p : Dist X) :
    (W.joint p).entropy = p.entropy + W.condEntropy p := by
  simp only [Dist.entropy, condEntropy, joint_apply, Fintype.sum_prod_type, negMulLog_mul,
    sum_add_distrib, ← sum_mul, ← mul_sum, Dist.sum_coe, one_mul]

/-- The entropy of the output is at most the entropy of the joint distribution. -/
theorem entropy_output_le_entropy_joint (W : Channel X Y) (p : Dist X) :
    (W.output p).entropy ≤ (W.joint p).entropy := by
  simp only [Dist.entropy, output_apply, joint_apply, Fintype.sum_prod_type_right]
  exact sum_le_sum fun y _ =>
    negMulLog_sum_le _ _ fun x _ => mul_nonneg (p.nonneg x) ((W x).nonneg y)

theorem mutualInfo_eq_add_sub (W : Channel X Y) (p : Dist X) :
    W.mutualInfo p = p.entropy + (W.output p).entropy - (W.joint p).entropy := by
  rw [entropy_joint, mutualInfo]; ring

/-- `I(p, W) ≤ H(p)`: the mutual information is at most the input entropy. -/
theorem mutualInfo_le_entropy (W : Channel X Y) (p : Dist X) : W.mutualInfo p ≤ p.entropy := by
  rw [mutualInfo_eq_add_sub]
  linarith [W.entropy_output_le_entropy_joint p]

theorem mutualInfo_le_log_card_input (W : Channel X Y) (p : Dist X) :
    W.mutualInfo p ≤ log (Fintype.card X) :=
  (W.mutualInfo_le_entropy p).trans p.entropy_le_log_card

/-! ### Relabeling the input alphabet -/

end Channel

namespace Dist

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- Push a distribution forward along a map: `(p.map f) b = ∑ a with f a = b, p a`. -/
noncomputable def map (f : α → β) (p : Dist α) : Dist β where
  pmf := fun b => ∑ a, if f a = b then p a else 0
  nonneg := fun b => sum_nonneg fun a _ => by
    split_ifs
    · exact p.nonneg a
    · exact le_rfl
  sum_eq_one := by
    rw [sum_comm]
    simp [p.sum_coe]

@[simp] theorem map_apply (f : α → β) (p : Dist α) (b : β) :
    p.map f b = ∑ a, if f a = b then p a else 0 := rfl

end Dist

namespace Channel

open Real Finset

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]

/-- Precomposing a channel with a relabeling `f` of the inputs gives the same output law as
pushing the input law forward along `f`. -/
theorem output_comp (W : Channel X Y) (f : Z → X) (p : Dist Z) :
    output (fun z => W (f z) : Channel Z Y) p = W.output (p.map f) := by
  ext y
  simp only [output_apply, Dist.map_apply, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp

theorem condEntropy_comp (W : Channel X Y) (f : Z → X) (p : Dist Z) :
    condEntropy (fun z => W (f z) : Channel Z Y) p = W.condEntropy (p.map f) := by
  simp only [condEntropy, Dist.map_apply, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp

/-- Mutual information is unchanged by relabeling the inputs. -/
theorem mutualInfo_comp (W : Channel X Y) (f : Z → X) (p : Dist Z) :
    mutualInfo (fun z => W (f z) : Channel Z Y) p = W.mutualInfo (p.map f) := by
  rw [mutualInfo, mutualInfo, output_comp, condEntropy_comp]

end Channel

end LeanP1
