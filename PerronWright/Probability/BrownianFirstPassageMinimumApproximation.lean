import PerronWright.Probability.BrownianFirstPassageEndpointGeometry
import PerronWright.Probability.ContinuousPathLeastMinimum
import Mathlib.Topology.ClusterPt

/-! # First hits of levels approaching the actual minimum

For a fixed continuous path whose minimum lies below its starting value,
first passage to levels above that minimum converges to the genuine
earliest minimizer. Multiple minima are allowed: every first passage
already precedes the earliest minimizer, so compactness selects that
particular minimum without a unique-minimum assumption.
-/

open Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageMinimumApproximation

open BrownianPathLaw ContinuousPathFirstPassage ContinuousPathLeastMinimum
open BrownianFirstPassageUncappedLaw

theorem firstPassage_le_leastMinimizer (T : ℝ≥0) (f : Path) (level : ℝ)
    (hlevel : minimumValue T f ≤ level) :
    firstPassage level f ≤ leastMinimizer T f := by
  apply (firstPassage_le_iff level f (leastMinimizer T f)).mpr
  exact ⟨leastMinimizer T f,le_rfl,(leastMinimizer_value T f).le.trans hlevel⟩

theorem passageTime_le_leastMinimizer (T : ℝ≥0) (f : Path) (level : ℝ)
    (hlevel : minimumValue T f ≤ level) :
    passageTime level f ≤ leastMinimizer T f := by
  have hle := firstPassage_le_leastMinimizer T f level hlevel
  have hfin : firstPassage level f ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  rw [← ENNReal.coe_toNNReal hfin] at hle
  exact ENNReal.coe_le_coe.mp hle

theorem cluster_passageTime_minimum_value {ι : Type*} {L : Filter ι}
    (T : ℝ≥0) (f : Path) (levels : ι → ℝ)
    (hlevels : Tendsto levels L (𝓝 (minimumValue T f)))
    (hge : ∀ᶠ i in L, minimumValue T f ≤ levels i)
    (hstart : minimumValue T f < f 0)
    (t : ℝ≥0) (ht : MapClusterPt t L (fun i ↦ passageTime (levels i) f)) :
    f t = minimumValue T f := by
  let M := comap (fun i ↦ passageTime (levels i) f) (𝓝 t) ⊓ L
  have : M.NeBot := neBot_inf_comap_iff_map'.mpr ht
  have htime : Tendsto (fun i ↦ passageTime (levels i) f) M (𝓝 t) :=
    tendsto_comap.mono_left inf_le_left
  have hl : Tendsto levels M (𝓝 (minimumValue T f)) := hlevels.mono_left inf_le_right
  have hbefore : ∀ᶠ i in L, levels i < f 0 := hlevels.eventually (gt_mem_nhds hstart)
  have he : ∀ᶠ i in M, f (passageTime (levels i) f) = levels i := by
    filter_upwards [hge.filter_mono inf_le_right,hbefore.filter_mono inf_le_right] with i hgi hbi
    have hfin : firstPassage (levels i) f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top
      (firstPassage_le_leastMinimizer T f (levels i) hgi)
    exact firstPassage_exact_level (levels i) f hbi hfin
  exact tendsto_nhds_unique ((continuous_path f).tendsto t |>.comp htime)
    (hl.congr' (he.mono (fun _ hi ↦ hi.symm)))

theorem tendsto_passageTime_to_leastMinimizer {ι : Type*} {L : Filter ι}
    (T : ℝ≥0) (f : Path) (levels : ι → ℝ)
    (hlevels : Tendsto levels L (𝓝 (minimumValue T f)))
    (hge : ∀ᶠ i in L, minimumValue T f ≤ levels i)
    (hstart : minimumValue T f < f 0) :
    Tendsto (fun i ↦ passageTime (levels i) f) L (𝓝 (leastMinimizer T f)) := by
  apply (isCompact_Icc (a := (0 : ℝ≥0)) (b := leastMinimizer T f)).tendsto_nhds_of_unique_mapClusterPt
    (hge.mono (fun i hi ↦ ⟨zero_le,passageTime_le_leastMinimizer T f (levels i) hi⟩))
  intro t ht hc
  have hm := cluster_passageTime_minimum_value T f levels hlevels hge hstart t hc
  exact le_antisymm ht.2
    (leastMinimizer_le T f t (ht.2.trans (leastMinimizer_le_time T f)) hm)

theorem tendsto_minimum_offset_passageTime (T : ℝ≥0) (f : Path)
    (hstart : minimumValue T f < f 0) :
    Tendsto (fun δ : ℝ ↦ passageTime (minimumValue T f+δ) f)
      (𝓝[>] 0) (𝓝 (leastMinimizer T f)) := by
  have hl : Tendsto (fun δ : ℝ ↦ minimumValue T f+δ) (𝓝[>] 0)
      (𝓝 (minimumValue T f+0)) :=
    tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds)
  apply tendsto_passageTime_to_leastMinimizer T f _
    (by simpa only [add_zero] using hl) _ hstart
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact le_add_of_nonneg_right (le_of_lt hδ)

end PerronWright.BrownianFirstPassageMinimumApproximation
