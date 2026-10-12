import PerronWright.Probability.BrownianPositiveBridgeDyadicModulus
import PerronWright.Probability.BrownianPositiveBridgeStoppedSupport
import PerronWright.Probability.DyadicPathCompactGoodSet
import Mathlib.MeasureTheory.Measure.Tight

/-! # Genuine path-family tightness of small positive-endpoint bridges

All measures are the literal conditioned positive pinned bridge laws.
The compact sets are the proved compact-open dyadic good sets. The common
probability bounds are deduced from actual endpoint-inclusive increments,
not imposed as a tightness or modulus hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgePathTightness

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianPositiveBridgeDyadicModulus
open BrownianPositiveBridgeStoppedSupport BrownianDyadicModulus DyadicPathModulus
open DyadicPathCompactGoodSet

def smallEndpointFamily (T : ℝ≥0) (δ : ℝ) : Set (Measure Path) :=
  {μ | ∃ a : ℝ, 0 < a ∧ a < δ ∧ μ = positiveBridgeLaw a T}

theorem neighborBound_of_stopped_not_bad (T : ℝ≥0) (M : ℕ) (hTM : (T : ℝ) ≤ M)
    (R : ℝ) (hR : 0 ≤ R) (g : Path) (hg : g ∈ stoppedPaths T) (hgood : g ∉ badPaths T M R) :
    NeighborBound g R := by
  intro n k
  by_cases hk : k < M*2^n
  · have hnot : ¬ R*decay^n ≤ ‖FourthMomentDyadicModulus.increment (samples T) n k g‖ := by
      intro hbad
      apply hgood
      exact mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨⟨k,hk⟩,hbad⟩⟩
    have hb := (lt_of_not_ge hnot).le
    change ‖g (min (DyadicFloorGeometry.coordinate n (k+1)) T)-g (min (DyadicFloorGeometry.coordinate n k) T)‖ ≤ R*decay^n at hb
    simpa only [NeighborBound,pathSamples,hg (DyadicFloorGeometry.coordinate n (k+1)),
      hg (DyadicFloorGeometry.coordinate n k),decay,DyadicGeometricApproximation.ratio] using hb
  · have hk' : M*2^n ≤ k := le_of_not_gt hk
    have hcoord : T ≤ DyadicFloorGeometry.coordinate n k := by
      have hkR : (M : ℝ)*(2 : ℝ)^n ≤ (k : ℝ) := by exact_mod_cast hk'
      have hm : (M : ℝ) ≤ DyadicFloorGeometry.coordinate n k := by
        rw [DyadicFloorGeometry.coordinate_real]
        exact (le_div_iff₀ (by positivity : 0 < (2 : ℝ)^n)).mpr hkR
      exact hTM.trans hm
    have hnext : T ≤ DyadicFloorGeometry.coordinate n (k+1) := by
      have hkR : (DyadicFloorGeometry.coordinate n k : ℝ) ≤ DyadicFloorGeometry.coordinate n (k+1) := by
        rw [DyadicFloorGeometry.coordinate_real,DyadicFloorGeometry.coordinate_real]
        exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (by positivity)
      exact hcoord.trans hkR
    change ‖g (DyadicFloorGeometry.coordinate n (k+1))-g (DyadicFloorGeometry.coordinate n k)‖ ≤ _
    rw [hg (DyadicFloorGeometry.coordinate n (k+1)),hg (DyadicFloorGeometry.coordinate n k),
      min_eq_right hnext,min_eq_right hcoord,sub_self,norm_zero]
    exact mul_nonneg hR (pow_nonneg DyadicGeometricApproximation.ratio_nonneg n)

theorem eventually_uniform_compact_goodSet_bound (T : ℝ≥0) (hT : 0 < T)
    (M : ℕ) (hTM : (T : ℝ) ≤ M) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ R : ℝ, 0 < R →
      positiveBridgeLaw a T ((goodSet 1 R)ᶜ) ≤
        ENNReal.ofReal ((momentCoefficient T*(M : ℝ)/R^4)/(1-tailRatio)) := by
  filter_upwards [eventually_uniform_allLevel_bad_measure_bound T hT,
    eventually_ae_initial_norm_le_one T hT] with a hbad hinit
  intro R hR
  have hsubset : ∀ᵐ g ∂positiveBridgeLaw a T, g ∈ (goodSet 1 R)ᶜ → g ∈ badPaths T M R := by
    filter_upwards [ae_positiveBridgeLaw_stopped a T,hinit] with g hg h0
    intro hout
    by_contra hn
    exact hout ⟨h0,neighborBound_of_stopped_not_bad T M hTM R hR.le g hg hn⟩
  exact (measure_mono_ae hsubset).trans (hbad M R hR)

theorem exists_radius_small_bound (T : ℝ≥0) (M : ℕ) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ENNReal.ofReal ((momentCoefficient T*(M : ℝ)/R^4)/(1-tailRatio)) ≤ ε := by
  by_cases htop : ε = ∞
  · exact ⟨1,by norm_num,by rw [htop]; exact le_top⟩
  have hεR : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  let Q : ℝ := momentCoefficient T*(M : ℝ)/(1-tailRatio)
  have hQ : 0 ≤ Q := div_nonneg (mul_nonneg (momentCoefficient_nonneg T) (Nat.cast_nonneg M))
    (sub_pos.mpr tailRatio_lt_one).le
  let R : ℝ := 1+Q/ε.toReal
  have hR1 : 1 ≤ R := le_add_of_nonneg_right (div_nonneg hQ hεR.le)
  have hR : 0 < R := (by norm_num : (0 : ℝ) < 1).trans_le hR1
  have hpow : R ≤ R^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hR1 (by norm_num : (1 : ℕ) ≤ 4)
  have hQR : Q/R ≤ ε.toReal := by
    apply (div_le_iff₀ hR).mpr
    have he : ε.toReal*R = ε.toReal+Q := by
      dsimp [R]
      field_simp [ne_of_gt hεR]
    rw [he]
    linarith
  refine ⟨R,hR,?_⟩
  have he : (momentCoefficient T*(M : ℝ)/R^4)/(1-tailRatio) = Q/R^4 := by
    dsimp [Q]
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [he,← ENNReal.ofReal_toReal htop]
  exact ENNReal.ofReal_le_ofReal ((div_le_div_of_nonneg_left hQ hR hpow).trans hQR)

theorem exists_small_endpoint_tightFamily (T : ℝ≥0) (hT : 0 < T) :
    ∃ δ : ℝ, 0 < δ ∧ IsTightMeasureSet (smallEndpointFamily T δ) := by
  obtain ⟨M,hM⟩ := exists_nat_gt (T : ℝ)
  have hevent := eventually_uniform_compact_goodSet_bound T hT M hM.le
  obtain ⟨δ,hδ,hbound⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  refine ⟨δ,hδ,?_⟩
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨R,hR,hsmall⟩ := exists_radius_small_bound T M ε hε
  refine ⟨goodSet 1 R,isCompact_goodSet 1 hR.le,?_⟩
  rintro μ ⟨a,ha,haδ,rfl⟩
  have haBall : a ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ha]
    exact haδ
  exact (hbound ⟨haBall,ha⟩ R hR).trans hsmall

theorem exists_common_compact_sets (T : ℝ≥0) (hT : 0 < T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ K : Set Path, IsCompact K ∧ ∀ a : ℝ, 0 < a → a < δ → positiveBridgeLaw a T (Kᶜ) ≤ ε := by
  obtain ⟨δ,hδ,hfamily⟩ := exists_small_endpoint_tightFamily T hT
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  obtain ⟨K,hK,hbound⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hfamily ε hε
  exact ⟨K,hK,fun a ha haδ ↦ hbound _ ⟨a,ha,haδ,rfl⟩⟩

end PerronWright.BrownianPositiveBridgePathTightness
