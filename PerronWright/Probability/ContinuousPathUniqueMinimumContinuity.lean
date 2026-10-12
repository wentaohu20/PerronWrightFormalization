import PerronWright.Probability.ContinuousPathLeastMinimum
import Mathlib.Topology.ClusterPt

/-! # Continuity of the genuine earliest minimum at a unique minimum

The selector is the existing least minimizer, not an assumed continuous
selection. Its compact range and the actual continuous evaluation and
minimum functionals identify every cluster point. Multiple minima are
allowed away from the path at which continuity is proved.
-/

open Filter Topology Set
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.ContinuousPathUniqueMinimumContinuity

open BrownianPathLaw ContinuousPathLeastMinimum

theorem leastMinimizer_mem (T : ℝ≥0) (f : Path) :
    leastMinimizer T f ∈ Icc 0 T :=
  ⟨zero_le, leastMinimizer_le_time T f⟩

theorem cluster_leastMinimizer_value {ι : Type*} {L : Filter ι}
    (T : ℝ≥0) (F : ι → Path) (f : Path) (hF : Tendsto F L (𝓝 f))
    (t : ℝ≥0) (ht : MapClusterPt t L (fun i ↦ leastMinimizer T (F i))) :
    f t = minimumValue T f := by
  let M := comap (fun i ↦ leastMinimizer T (F i)) (𝓝 t) ⊓ L
  have : M.NeBot := neBot_inf_comap_iff_map'.mpr ht
  have hFM : Tendsto F M (𝓝 f) := hF.mono_left inf_le_right
  have hmin : Tendsto (fun i ↦ leastMinimizer T (F i)) M (𝓝 t) :=
    tendsto_comap.mono_left inf_le_left
  have heval := continuous_joint_eval.tendsto (f,t) |>.comp (hFM.prodMk_nhds hmin)
  have hvalue := (continuous_minimumValue T).tendsto f |>.comp hFM
  exact tendsto_nhds_unique heval (hvalue.congr' (Eventually.of_forall
    (fun i ↦ (leastMinimizer_value T (F i)).symm)))

theorem tendsto_leastMinimizer_of_unique {ι : Type*} {L : Filter ι}
    (T : ℝ≥0) (F : ι → Path) (f : Path) (hF : Tendsto F L (𝓝 f))
    (hunique : ∀ t : ℝ≥0, t ≤ T → f t = minimumValue T f →
      t = leastMinimizer T f) :
    Tendsto (fun i ↦ leastMinimizer T (F i)) L (𝓝 (leastMinimizer T f)) := by
  apply isCompact_Icc.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall (fun i ↦ leastMinimizer_mem T (F i)))
  intro t ht hc
  exact hunique t ht.2 (cluster_leastMinimizer_value T F f hF t hc)

theorem continuousAt_leastMinimizer_of_unique (T : ℝ≥0) (f : Path)
    (hunique : ∀ t : ℝ≥0, t ≤ T → f t = minimumValue T f →
      t = leastMinimizer T f) :
    ContinuousAt (leastMinimizer T) f :=
  tendsto_leastMinimizer_of_unique T id f tendsto_id hunique

end PerronWright.ContinuousPathUniqueMinimumContinuity
