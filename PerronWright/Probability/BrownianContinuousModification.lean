import PerronWright.Probability.BrownianRationalDyadicApproximation
import PerronWright.Probability.DyadicGeometricExtension

/-!
# A genuinely constructed continuous modification of the rational law

The process is the actual dyadic extension of the actual sampled rational
Gaussian coordinates. Its almost-sure continuity, measurability at each
time, and agreement with every original rational-time value are proved.
Real-time finite-dimensional Brownian laws are a separate next step;
this file does not assume or claim an `IsBrownianReal` realization.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.BrownianContinuousModification

open BrownianGaussianSkeleton BrownianDyadicGrid BrownianDyadicModulus
open BrownianRationalDyadicApproximation

def dyadicSamples (x : ℕ → ℝ) (n k : ℕ) : ℝ := rationalProcess (dyadicTime n k) x

def process (t : ℝ≥0) (x : ℕ → ℝ) : ℝ :=
  DyadicGeometricApproximation.extension (dyadicSamples x) t

theorem dyadicSamples_compatible (x : ℕ → ℝ) :
    DyadicGeometricApproximation.Compatible (dyadicSamples x) := by
  intro n k
  simp only [dyadicSamples,dyadicTime_succ_double]

theorem ae_dyadicSamples_localBound :
    ∀ᵐ x ∂rationalLaw, DyadicGeometricApproximation.LocalBound (dyadicSamples x) := by
  simpa only [DyadicGeometricApproximation.LocalBound,DyadicGeometricApproximation.ratio,
    dyadicSamples] using ae_all_window_neighbor_bound

/-- The constructed process has almost surely continuous paths, proved
from sampled-law Borel--Cantelli bounds and a deterministic extension. -/
theorem ae_continuous_process : ∀ᵐ x ∂rationalLaw, Continuous (fun t ↦ process t x) := by
  filter_upwards [ae_dyadicSamples_localBound] with x hx
  exact DyadicGeometricExtension.continuous_extension (dyadicSamples_compatible x) hx

theorem ae_samples_tendsto_process (t : ℝ≥0) :
    ∀ᵐ x ∂rationalLaw, Tendsto
      (fun n ↦ rationalProcess (dyadicTime n (DyadicFloorGeometry.index n t)) x)
      atTop (𝓝 (process t x)) := by
  filter_upwards [ae_dyadicSamples_localBound] with x hx
  exact DyadicGeometricApproximation.samples_tendsto_extension (dyadicSamples_compatible x) hx t

/-- Actual measurability of the continuous modification at every real
time, obtained as an almost-sure limit of measurable sampled coordinates. -/
theorem aemeasurable_process (t : ℝ≥0) : AEMeasurable (process t) rationalLaw := by
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n ↦ (measurable_pi_apply (Encodable.encode (dyadicTime n (DyadicFloorGeometry.index n t)))).aemeasurable)
  exact ae_samples_tendsto_process t

theorem ae_all_dyadic_process_eq : ∀ᵐ x ∂rationalLaw, ∀ n k : ℕ,
    process (DyadicFloorGeometry.coordinate n k) x = rationalProcess (dyadicTime n k) x := by
  filter_upwards [ae_dyadicSamples_localBound] with x hx
  intro n k
  exact DyadicGeometricApproximation.extension_dyadic (dyadicSamples_compatible x) hx n k

/-- The modification agrees simultaneously with every literal sampled
rational value. This is a proved property, not a modification hypothesis. -/
theorem ae_all_rational_process_eq : ∀ᵐ x ∂rationalLaw, ∀ q : RationalTime,
    process (rationalTimeReal q) x = rationalProcess q x := by
  filter_upwards [ae_dyadicSamples_localBound,ae_all_rational_approxTime_process_tendsto] with x hx hq
  intro q
  exact tendsto_nhds_unique
    (DyadicGeometricApproximation.samples_tendsto_extension (dyadicSamples_compatible x) hx (rationalTimeReal q))
    (hq q)

theorem rational_process_ae_eq (q : RationalTime) :
    process (rationalTimeReal q) =ᵐ[rationalLaw] rationalProcess q :=
  ae_all_rational_process_eq.mono (fun _ hx ↦ hx q)

theorem rational_process_hasLaw (q : RationalTime) :
    HasLaw (process (rationalTimeReal q)) (gaussianReal 0 (rationalTimeReal q)) rationalLaw :=
  (rational_hasLaw_eval q).congr (rational_process_ae_eq q)

theorem rational_process_hasLaw_sub (q r : RationalTime) :
    HasLaw (fun x ↦ process (rationalTimeReal q) x - process (rationalTimeReal r) x)
      (gaussianReal 0 (nndist (q.val : ℝ) (r.val : ℝ))) rationalLaw := by
  apply (rational_hasLaw_sub q r).congr
  filter_upwards [rational_process_ae_eq q,rational_process_ae_eq r] with x hq hr
  rw [hq,hr]

theorem rational_process_isGaussianProcess :
    IsGaussianProcess (fun q : RationalTime ↦ process (rationalTimeReal q)) rationalLaw :=
  rational_isGaussianProcess.congr (fun q ↦ (rational_process_ae_eq q).symm)

theorem process_zero_ae_eq_zero : ∀ᵐ x ∂rationalLaw, process 0 x = 0 := by
  let q : RationalTime := ⟨0,by norm_num⟩
  have hz : rationalTimeReal q = 0 := by
    apply NNReal.eq
    change ((0 : ℚ) : ℝ) = 0
    norm_num
  have h := rational_process_hasLaw q
  rw [hz] at h
  rw [gaussianReal_zero_var] at h
  exact h.ae_eq_of_dirac

end PerronWright.BrownianContinuousModification
