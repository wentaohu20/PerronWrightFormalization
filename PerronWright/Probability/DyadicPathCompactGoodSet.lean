import PerronWright.Probability.DyadicPathModulus
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-! # Genuine compact dyadic good sets in the continuous-path space

These are closed sets with a common literal initial-value bound and
neighbor bounds. Their compactness in the actual compact-open topology
is proved using the quantitative modulus and Arzela--Ascoli.
-/

open Filter Topology Set
open scoped NNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.DyadicPathCompactGoodSet

open BrownianPathLaw DyadicFloorGeometry DyadicGeometricApproximation DyadicPathModulus

def goodSet (B R : ℝ) : Set Path := {f | ‖f 0‖ ≤ B ∧ NeighborBound f R}

theorem isClosed_goodSet (B R : ℝ) : IsClosed (goodSet B R) := by
  simp only [goodSet,NeighborBound,Set.ofPred_and,Set.ofPred_forall]
  apply IsClosed.inter (isClosed_le (continuous_eval 0).norm continuous_const)
  apply isClosed_iInter
  intro n
  apply isClosed_iInter
  intro k
  exact isClosed_le ((continuous_eval (coordinate n (k+1))).sub
    (continuous_eval (coordinate n k))).norm continuous_const

theorem measurableSet_goodSet (B R : ℝ) : MeasurableSet (goodSet B R) :=
  (isClosed_goodSet B R).measurableSet

theorem goodSet_uniformEquicontinuous (B : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    UniformEquicontinuous (fun f : goodSet B R ↦ fun t ↦ f.val t) :=
  neighbor_uniformEquicontinuous (fun f : goodSet B R ↦ f.val) hR (fun f ↦ f.property.2)

theorem goodSet_pointwise_compact_bound (B : ℝ) {R : ℝ} (hR : 0 ≤ R) (t : ℝ≥0) :
    ∃ Q : Set ℝ, IsCompact Q ∧ ∀ f ∈ goodSet B R, f t ∈ Q := by
  let D : ℝ := B+(index 0 t : ℝ)*R+R/(1-ratio)
  refine ⟨Icc (-D) D,isCompact_Icc,?_⟩
  intro f hf
  exact abs_le.mp (by
    simpa only [Real.norm_eq_abs] using path_norm_bound hR hf.2 hf.1 t)

theorem isCompact_goodSet (B : ℝ) {R : ℝ} (hR : 0 ≤ R) : IsCompact (goodSet B R) := by
  have : T2Space (UniformOnFun ℝ≥0 ℝ {K : Set ℝ≥0 | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr (fun t ↦
      mem_sUnion.mpr ⟨{t},isCompact_singleton,mem_singleton t⟩))
  have hemb : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set ℝ≥0 | IsCompact K} ∘ (fun f : Path ↦ fun t ↦ f t)) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hh : IsCompact (closure (goodSet B R)) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (fun _ hK ↦ hK) hemb
      (fun K _ ↦ (goodSet_uniformEquicontinuous B hR).equicontinuous.equicontinuousOn K)
      (fun _ _ t _ ↦ goodSet_pointwise_compact_bound B hR t)
  simpa only [(isClosed_goodSet B R).closure_eq] using hh

end PerronWright.DyadicPathCompactGoodSet
