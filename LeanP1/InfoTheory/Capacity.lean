import LeanP1.InfoTheory.MutualInfo

/-!
# Channel capacity

Stage 5 of the channel-capacity project.

The (information) capacity of a channel is the supremum of the mutual information over all
input distributions: `C(W) = sup_p I(p, W)`.

## Main results

* `Channel.mutualInfo_le_capacity`: every input distribution achieves at most `C(W)`.
* `Channel.capacity_nonneg`: `0 ≤ C(W)`.
* `Channel.capacity_le_log_card`: `C(W) ≤ log |Y|`.
* `Channel.capacity_le_log_card_input`: `C(W) ≤ log |X|`.
* `Channel.capacity_le` / `Channel.le_capacity`: the two halves of computing a capacity
  exactly: an upper bound valid for all inputs, and one input attaining it.
-/

namespace LeanP1

namespace Channel

open Real

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The capacity of `W`: the supremum of `I(p, W)` over all input distributions `p`. -/
noncomputable def capacity (W : Channel X Y) : ℝ := sSup (Set.range W.mutualInfo)

theorem bddAbove_range_mutualInfo (W : Channel X Y) : BddAbove (Set.range W.mutualInfo) :=
  ⟨log (Fintype.card Y), by rintro _ ⟨p, rfl⟩; exact W.mutualInfo_le_log_card p⟩

theorem mutualInfo_le_capacity (W : Channel X Y) (p : Dist X) : W.mutualInfo p ≤ W.capacity :=
  le_csSup W.bddAbove_range_mutualInfo ⟨p, rfl⟩

/-- To bound the capacity from below it suffices to exhibit one good input distribution. -/
theorem le_capacity {W : Channel X Y} {C : ℝ} (p : Dist X) (h : C ≤ W.mutualInfo p) :
    C ≤ W.capacity :=
  h.trans (W.mutualInfo_le_capacity p)

/-- To bound the capacity from above it suffices to bound `I(p, W)` for every `p`. -/
theorem capacity_le [Nonempty X] {W : Channel X Y} {C : ℝ} (h : ∀ p, W.mutualInfo p ≤ C) :
    W.capacity ≤ C :=
  csSup_le ⟨_, Dist.uniform, rfl⟩ (by rintro _ ⟨p, rfl⟩; exact h p)

theorem capacity_nonneg [Nonempty X] (W : Channel X Y) : 0 ≤ W.capacity :=
  le_capacity Dist.uniform (W.mutualInfo_nonneg _)

theorem capacity_le_log_card [Nonempty X] (W : Channel X Y) :
    W.capacity ≤ log (Fintype.card Y) :=
  capacity_le fun p => W.mutualInfo_le_log_card p

theorem capacity_le_log_card_input [Nonempty X] (W : Channel X Y) :
    W.capacity ≤ log (Fintype.card X) :=
  capacity_le fun p => W.mutualInfo_le_log_card_input p

/-- Feeding `W` through any relabeling of its inputs cannot beat the capacity of `W`. -/
theorem mutualInfo_comp_le_capacity {Z : Type*} [Fintype Z]
    (W : Channel X Y) (f : Z → X) (p : Dist Z) :
    mutualInfo (fun z => W (f z) : Channel Z Y) p ≤ W.capacity := by
  classical
  rw [mutualInfo_comp]
  exact W.mutualInfo_le_capacity _

end Channel

end LeanP1
