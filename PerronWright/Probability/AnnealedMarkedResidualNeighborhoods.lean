import PerronWright.Probability.AnnealedMarkedResidualConcentration

/-! # Actual set integrals outside joint weak mark neighborhoods -/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedMarkedResidualNeighborhoods

open AnnealedMarkedResidualLaw AnnealedMarkedResidualTransfer
  AnnealedMarkedResidualConcentration AnnealedProfileFunctionalObservable
  AnnealedTupleResidualCounting EmpiricalMarkConcentration ProfileFiniteCollection

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

/-- Weak-open neighborhoods yield genuinely measurable events in the
sampled state space via the finite type coordinates. -/
theorem componentMarks_preimage_of_open {q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i)
    (U : Set (Fin q → ProbabilityMeasure S)) (hU : IsOpen U) :
    MeasurableSet {p : StateFamily (S := S) k | componentMarks hk p ∈ U} := by
  have hc : Continuous (fun x : (i : Fin q) → Fin (k i) → S ↦
      fun i ↦ typesMark (hk i) (x i)) :=
    continuous_pi (fun i ↦ (typesMark_continuous (hk i)).comp (continuous_apply i))
  have hx : Measurable (fun p : StateFamily (S := S) k ↦ fun i ↦ (p i).1) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i).fst
  exact (hU.preimage hc).measurableSet.preimage hx

theorem densityMeasure_real_set_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (hF : Integrable F μ) (hn : ∀ ω, 0 ≤ F ω)
    (A : Set Ω) (hA : MeasurableSet A) :
    (μ.withDensity (fun ω ↦ ENNReal.ofReal (F ω))).real A = ∫ ω in A, F ω ∂μ := by
  rw [measureReal_def,withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal hF.restrict (Eventually.of_forall hn),
    ENNReal.toReal_ofReal (integral_nonneg hn)]

theorem weightedMeasure_outside_open_eq_integral {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ) (hn : 0 < n)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hweight : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n)) (k i) (r i))
    (U : Set (Fin q → ProbabilityMeasure S)) (hU : IsOpen U) :
    (weightedMeasure M hM lambda hk f s₀ hweight).real {p | componentMarks hk p ∉ U} =
      ∫ p in {p | componentMarks hk p ∉ U}, normalizedResidualObservable M hM lambda hk f s₀ p
        ∂productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hweight :=
  densityMeasure_real_set_eq_integral _ _
    (normalizedResidualObservable_integrable_alltime M hM lambda hn hk f s₀ hweight)
    (fun p ↦ (normalizedResidualObservable_pos M hM lambda hk f s₀ p).le) _
    (componentMarks_preimage_of_open hk U hU).compl

/-- A literal residual set integral, rather than an assumed marked
concentration property or an abstract weighted-mass interface. -/
theorem weightedResidual_outside_open_nhds_integral_tendsto_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hQP : M.QP)
    (R q : ℕ) (hq : 0 < q) (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C) (lambda : ℝ)
    (N : ℕ → ℕ) (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (f : ∀ n, Placements (N n) (k n)) (s₀ : S)
    (hweight : ∀ n i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda (N n)))
      (k n i) (r n i))
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (hkTop : ∀ i, Tendsto (fun n ↦ k n i) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i:ℝ) *
      ‖M.scalarField (CriticalScaling.time lambda (N n))‖ ≤ L)
    (hsize : ∀ᶠ n in atTop, (∑ i,(k n i:ℝ)) ≤ C*(N n:ℝ)^(2/3:ℝ))
    {s : ℝ} (hs : Tendsto (fun n ↦ (∑ i,k n i:ℕ)/(N n:ℝ)^(2/3:ℝ)) atTop (𝓝 s))
    (U : Set (Fin q → ProbabilityMeasure S)) (hU : IsOpen U) (hUn : U ∈ 𝓝 (perronMarks M hM q)) :
    Tendsto (fun n ↦ ∫ p in {p | componentMarks (hk n) p ∉ U},
      normalizedResidualObservable M hM lambda (hk n) (f n) s₀ p
      ∂productLaw M (k n) (r n) (fun _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) (hweight n))
        atTop (𝓝 0) := by
  have hh := weightedMeasure_outside_joint_weak_nhds_tendsto_zero M hM hQP R q hq L C hL hC lambda
    N k r hk f s₀ hweight hN hNt hkTop hr hg hsize hs U hUn
  simpa only [weightedMeasure_outside_open_eq_integral M hM lambda (hN _) (hk _) (f _) s₀ (hweight _) U hU] using hh

end PerronWright.AnnealedMarkedResidualNeighborhoods
