import PerronWright.Probability.BrownianEntranceProductGeometry

/-! # Genuine finite-gap entrance-product Laplace factorization

Tonelli independently transforms every actual Brownian edge. The first
and last edges are the proved entrance duration transform; each interior
edge is the true absorbing-zero Green kernel. No area moment identity or
finiteness of a transform is assumed in the product factorization.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceProductLaplace

open BrownianEntranceProductGeometry BrownianKilledFreeEntranceGeometry
open BrownianKilledFiniteDimensionalDensityCoordinates PositiveTimeConvolutionLaplace
open BrownianKilledAreaMomentResolvent BrownianKilledGreenKernel BrownianEntranceKernelLaplace

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

/-- Finite-dimensional Tonelli for separate nonnegative coordinate
factors, including infinite integrals and the empty product. -/
theorem lintegral_fin_prod (d : ℕ) (F : Fin d → ℝ → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i)) :
    (∫⁻ σ : Fin d → ℝ, ∏ i, F i (σ i)) = ∏ i, ∫⁻ t : ℝ, F i t := by
  induction d with
  | zero => simp only [Fin.prod_univ_zero,lintegral_one,volume_pi,Measure.pi_empty_univ]
  | succ d ih =>
    have hm : Measurable (fun σ : Fin (d+1) → ℝ ↦ ∏ i, F i (σ i)) := by
      apply Finset.measurable_prod
      intro i _
      exact (hF i).comp (measurable_pi_apply i)
    rw [lintegral_volume_freeCons d hm]
    simp only [freeCons,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    have htail : Measurable (fun σ : Fin d → ℝ ↦ ∏ i, F i.succ (σ i)) := by
      apply Finset.measurable_prod
      intro i _
      exact (hF i.succ).comp (measurable_pi_apply i)
    simp_rw [lintegral_const_mul _ htail,ih (fun i ↦ F i.succ) (fun i ↦ hF i.succ)]
    exact lintegral_mul_const _ (hF 0)

theorem laplaceWeight_sum (d : ℕ) (p : ℝ) (σ : Fin d → ℝ) :
    laplaceWeight p (∑ i, σ i) = ∏ i, laplaceWeight p (σ i) := by
  induction d with
  | zero => simp [laplaceWeight]
  | succ d ih =>
    rw [Fin.sum_univ_succ,Fin.prod_univ_succ,laplaceWeight_add,ih]

def entranceTransform (p z : ℝ) : ℝ≥0∞ :=
  if 0 < z then ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p))) else 0

def edgeTransform (n : ℕ) (p : ℝ) (i : Fin (n+2)) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  Fin.cases (entranceTransform p (v 0))
    (fun j ↦ Fin.lastCases (entranceTransform p (v (Fin.last n)))
      (fun k ↦ green p (v k.castSucc) (v k.succ)) j) i

theorem lintegral_edgeKernel_laplace (n : ℕ) (p : ℝ) (hp : 0 < p)
    (i : Fin (n+2)) (v : FreeVector (n+1)) :
    (∫⁻ t : ℝ, laplaceWeight p t*edgeKernel n i t v) = edgeTransform n p i v := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [edgeKernel,edgeTransform,Fin.cases_zero,entranceTransform] using
      lintegral_entrance_laplace_allStates p hp.le (v 0)
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simpa only [edgeKernel,edgeTransform,Fin.cases_succ,Fin.lastCases_last,entranceTransform] using
        lintegral_entrance_laplace_allStates p hp.le (v (Fin.last n))
    · simpa only [edgeKernel,edgeTransform,Fin.cases_succ,Fin.lastCases_castSucc,
        BrownianKilledAreaMomentResolvent.resolvent] using
        resolvent_zero_eq p hp (v k.castSucc) (v k.succ)

def transformedNumerator (n : ℕ) (p : ℝ) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  entranceTransform p (v 0)*(∏ k : Fin n, green p (v k.castSucc) (v k.succ))*
    entranceTransform p (v (Fin.last n))

theorem prod_edgeTransform (n : ℕ) (p : ℝ) (v : FreeVector (n+1)) :
    (∏ i, edgeTransform n p i v) = transformedNumerator n p v := by
  rw [Fin.prod_univ_succ,Fin.prod_univ_castSucc]
  simp only [edgeTransform,transformedNumerator,Fin.cases_zero,Fin.cases_succ,
    Fin.lastCases_castSucc,Fin.lastCases_last,mul_assoc]

theorem rawNumerator_laplace_allGaps (n : ℕ) (p : ℝ) (hp : 0 < p)
    (v : FreeVector (n+1)) :
    (∫⁻ σ : Fin (n+2) → ℝ, laplaceWeight p (∑ i, σ i)*rawNumerator n σ v) =
      transformedNumerator n p v := by
  have hm (i : Fin (n+2)) : Measurable (fun t : ℝ ↦ laplaceWeight p t*edgeKernel n i t v) :=
    (measurable_laplaceWeight p).mul ((measurable_edgeKernel n i).comp
      (measurable_id.prodMk measurable_const))
  simp only [laplaceWeight_sum,rawNumerator,← Finset.prod_mul_distrib]
  rw [lintegral_fin_prod (n+2) _ hm]
  simp_rw [lintegral_edgeKernel_laplace n p hp]
  exact prod_edgeTransform n p v

/-- Only positive duration vectors contribute: all nonpositive edge
durations vanish in the literal Brownian kernel. -/
theorem rawNumerator_laplace_positiveGaps (n : ℕ) (p : ℝ) (hp : 0 < p)
    (v : FreeVector (n+1)) :
    (∫⁻ σ in positiveGaps (n+2), laplaceWeight p (∑ i, σ i)*rawNumerator n σ v) =
      transformedNumerator n p v := by
  rw [← lintegral_indicator (measurableSet_positiveGaps (n+2))]
  rw [← rawNumerator_laplace_allGaps n p hp v]
  apply lintegral_congr
  intro σ
  by_cases hσ : σ ∈ positiveGaps (n+2)
  · rw [indicator_of_mem hσ]
  · rw [indicator_of_notMem hσ,rawNumerator_zero_off_positiveGaps n σ hσ,mul_zero]

theorem measurable_laplace_rawNumerator (n : ℕ) (p : ℝ) :
    Measurable (fun q : (Fin (n+2) → ℝ) × FreeVector (n+1) ↦
      laplaceWeight p (∑ i, q.1 i)*rawNumerator n q.1 q.2) := by
  have hs : Measurable (fun q : (Fin (n+2) → ℝ) × FreeVector (n+1) ↦ ∑ i, q.1 i) := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_pi_apply i).comp measurable_fst
  exact ((measurable_laplaceWeight p).comp hs).mul (measurable_rawNumerator n)

/-- State weights may be infinite. Tonelli exchanges state and all
positive durations before evaluating the actual edge transforms. -/
theorem weighted_rawNumerator_laplace (n : ℕ) (p : ℝ) (hp : 0 < p)
    {Ψ : FreeVector (n+1) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ σ in positiveGaps (n+2), laplaceWeight p (∑ i, σ i)*
      (∫⁻ v, rawNumerator n σ v*Ψ v)) =
        ∫⁻ v, transformedNumerator n p v*Ψ v := by
  have hm : Measurable (fun q : (Fin (n+2) → ℝ) × FreeVector (n+1) ↦
      laplaceWeight p (∑ i, q.1 i)*rawNumerator n q.1 q.2*Ψ q.2) :=
    (measurable_laplace_rawNumerator n p).mul (hΨ.comp measurable_snd)
  calc
    _ = ∫⁻ σ in positiveGaps (n+2), ∫⁻ v,
        laplaceWeight p (∑ i, σ i)*rawNumerator n σ v*Ψ v := by
      apply lintegral_congr
      intro σ
      have hD : Measurable (fun v : FreeVector (n+1) ↦ rawNumerator n σ v*Ψ v) :=
        ((measurable_rawNumerator n).comp (measurable_const.prodMk measurable_id)).mul hΨ
      rw [← lintegral_const_mul _ hD]
      apply lintegral_congr
      intro v
      ac_rfl
    _ = ∫⁻ v, ∫⁻ σ in positiveGaps (n+2),
        laplaceWeight p (∑ i, σ i)*rawNumerator n σ v*Ψ v :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro v
      have hD : Measurable (fun σ : Fin (n+2) → ℝ ↦
          laplaceWeight p (∑ i, σ i)*rawNumerator n σ v) :=
        (measurable_laplace_rawNumerator n p).comp (measurable_id.prodMk measurable_const)
      rw [lintegral_mul_const _ hD,rawNumerator_laplace_positiveGaps n p hp v]

end PerronWright.BrownianEntranceProductLaplace
