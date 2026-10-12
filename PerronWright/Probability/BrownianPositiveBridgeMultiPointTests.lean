import PerronWright.Probability.BrownianPositiveBridgeMultiPointEntrance

/-! # Finite coupled Borel tests of the genuine small-endpoint densities

The bound follows from the literal Gaussian kernels: only entrance and
exit factors are divided by the endpoint, and the actual normalization
has the proved quadratic lower bound. Every finite-dimensional compact
positive rectangle is covered; no uniform-integrability interface is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeMultiPointTests

open BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel BrownianKilledBoundaryEntrance
open BrownianPositiveBridgeFiniteDimensionalEntrance BrownianPositiveBridgeFiniteDimensionalDensity
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianPositiveBridgeMultiPointEntrance

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

def internalBound (n : ℕ) (gaps : ℕ → ℝ≥0) : ℝ≥0∞ :=
  ∏ i : Fin n, ENNReal.ofReal ((Real.sqrt (2*Real.pi*(gaps (i.val+1) : ℝ)))⁻¹)

theorem internalBound_ne_top (n : ℕ) (gaps : ℕ → ℝ≥0) : internalBound n gaps ≠ ∞ := by
  unfold internalBound
  exact ENNReal.prod_ne_top (fun i _ ↦ ENNReal.ofReal_ne_top)

theorem internalDensity_le_bound (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (v : FreeVector (n+1)) :
    internalDensity n gaps v ≤ internalBound n gaps := by
  unfold internalDensity internalBound
  apply Finset.prod_le_prod (fun _ _ ↦ by positivity)
  intro i _
  exact density_le_prefactor _ _ (hgaps (i.val+1) (by omega)) _

def boundaryWindowBound (s t T : ℝ≥0) (b : ℝ) : ℝ :=
  (((2*b/(s : ℝ))*(Real.sqrt (2*Real.pi*(s : ℝ)))⁻¹)*
    ((2*b/(t : ℝ))*(Real.sqrt (2*Real.pi*(t : ℝ)))⁻¹))/
      ((T : ℝ)⁻¹*gaussianPDFReal 0 T 0)

theorem eventually_boundaryScaledReal_bound (s t T : ℝ≥0) (hs : 0 < s) (ht : 0 < t)
    (hT : 0 < T) (b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ x y : ℝ, x ≤ b → y ≤ b →
      boundaryScaledReal a s t T x y ≤ boundaryWindowBound s t T b := by
  have hTR : (0 : ℝ) < T := hT
  have hp := gaussianPDFReal_pos 0 T 0 (ne_of_gt hT)
  have hlow : (T : ℝ)⁻¹ < 2/(T : ℝ) := by
    have hi := inv_pos.mpr hTR
    rw [div_eq_mul_inv]
    linarith
  filter_upwards [self_mem_nhdsWithin,
    (normalization_div_sq_tendsto T hT).eventually_const_lt hlow] with a ha hn
  intro x y hx hy
  have hsa := div_nonneg (densityReal_nonneg a ha s hs x) ha.le
  have hta := div_nonneg (densityReal_nonneg a ha t ht y) ha.le
  have hprod := mul_le_mul (densityReal_div_start_le_window a ha s hs b x hb hx)
    (densityReal_div_start_le_window a ha t ht b y hb hy) hta (by positivity)
  have hdenlow : 0 < (T : ℝ)⁻¹*gaussianPDFReal 0 T 0 := mul_pos (inv_pos.mpr hTR) hp
  have hden : (T : ℝ)⁻¹*gaussianPDFReal 0 T 0 ≤
      ((1-Real.exp (-2*a^2/(T : ℝ)))/a^2)*gaussianPDFReal 0 T 0 :=
    mul_le_mul_of_nonneg_right hn.le hp.le
  unfold boundaryScaledReal boundaryWindowBound
  exact (div_le_div_of_nonneg_left (mul_nonneg hsa hta) hdenlow hden).trans
    (div_le_div_of_nonneg_right hprod hdenlow.le)

def multiWindowBound (n : ℕ) (gaps : ℕ → ℝ≥0) (b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (boundaryWindowBound (gaps 0) (gaps (n+1)) (sampleTime gaps (n+2)) b)*
    internalBound n gaps

theorem multiWindowBound_ne_top (n : ℕ) (gaps : ℕ → ℝ≥0) (b : ℝ) :
    multiWindowBound n gaps b ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top (internalBound_ne_top n gaps)

theorem eventually_rawMultiDensity_window_bound (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ v : FreeVector (n+1), (∀ i, v i ≤ b) →
      rawMultiDensity n a gaps v ≤ multiWindowBound n gaps b := by
  have hs := hgaps 0 (by omega)
  have ht := hgaps (n+1) (by omega)
  have hT : 0 < sampleTime gaps (n+2) := by
    rw [sampleTime_succ]
    exact ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ _))
  filter_upwards [self_mem_nhdsWithin,
    eventually_boundaryScaledReal_bound (gaps 0) (gaps (n+1)) (sampleTime gaps (n+2)) hs ht hT b hb]
    with a ha hbd
  intro v hv
  rw [rawMultiDensity_eq_scaled n a ha gaps hs ht hT v]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hbd _ _ (hv 0) (hv (Fin.last n))))
    (internalDensity_le_bound n gaps hgaps v)

theorem bounded_compact_test_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (K : Set (FreeVector (n+1)))
    (hK : IsCompact K) (b C : ℝ) (hb : 0 ≤ b) (hKb : ∀ v ∈ K, ∀ i, v i ≤ b)
    (Ψ : FreeVector (n+1) → ℝ≥0∞) (hΨ : Measurable Ψ)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ v in K, rawMultiDensity n a gaps v*Ψ v)
      (𝓝[>] 0) (𝓝 (∫⁻ v in K, entranceProduct n gaps v*Ψ v)) := by
  let μ : Measure (FreeVector (n+1)) := volume.restrict K
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let D : ℝ≥0∞ := multiWindowBound n gaps b*ENNReal.ofReal C
  have hm : ∀ᶠ a : ℝ in 𝓝[>] 0, Measurable (fun v ↦ rawMultiDensity n a gaps v*Ψ v) :=
    Eventually.of_forall (fun a ↦ (measurable_rawMultiDensity n a gaps).mul hΨ)
  have hbd : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ᵐ v ∂μ, rawMultiDensity n a gaps v*Ψ v ≤ D := by
    filter_upwards [eventually_rawMultiDensity_window_bound n gaps hgaps b hb] with a ha
    filter_upwards [ae_restrict_mem hK.measurableSet] with v hv
    exact mul_le_mul' (ha v (hKb v hv)) (hbound v)
  have hfin : (∫⁻ _v, D ∂μ) ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (multiWindowBound_ne_top n gaps b) ENNReal.ofReal_ne_top)
      (measure_ne_top μ univ)
  have hT : 0 < sampleTime gaps (n+2) := by
    rw [sampleTime_succ]
    exact (hgaps (n+1) (by omega)).trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ _))
  have hlim : ∀ᵐ v ∂μ, Tendsto (fun a : ℝ ↦ rawMultiDensity n a gaps v*Ψ v)
      (𝓝[>] 0) (𝓝 (entranceProduct n gaps v*Ψ v)) := Eventually.of_forall (fun v ↦
    ENNReal.Tendsto.mul_const (rawMultiDensity_tendsto n gaps (hgaps 0 (by omega))
      (hgaps (n+1) (by omega)) hT v)
      (Or.inr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound v))))
  exact tendsto_lintegral_filter_of_dominated_convergence (μ := μ) (fun _v ↦ D) hm hbd hfin hlim

theorem bounded_rectangle_test_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (l u : FreeVector (n+1))
    (b C : ℝ) (hb : 0 ≤ b) (hu : ∀ i, u i ≤ b)
    (Ψ : FreeVector (n+1) → ℝ≥0∞) (hΨ : Measurable Ψ)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ v in Icc l u, rawMultiDensity n a gaps v*Ψ v)
      (𝓝[>] 0) (𝓝 (∫⁻ v in Icc l u, entranceProduct n gaps v*Ψ v)) := by
  apply bounded_compact_test_tendsto n gaps hgaps (Icc l u) isCompact_Icc b C hb
    (fun v hv i ↦ (hv.2 i).trans (hu i)) Ψ hΨ hbound

end PerronWright.BrownianPositiveBridgeMultiPointTests
