import PerronWright.Probability.AnnealedProfileFunctionalSampled

/-!
# Joint Perron concentration of the actual annealed profile functionals

Six continuous functionals are collected in a finite-dimensional metric
vector.  The exact selected empirical normalization has been proved before
applying the genuine pooled weak concentration theorem.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedProfileFunctionalConcentration

open AnnealedProfileFunctionalContinuous AnnealedProfileFunctionalSampled
  FreshTypeAveraging FreshTypeCumulantExpansion FreshTypeEmpiricalIdentities
  EmpiricalTypeMarks EmpiricalMarkConcentration ProfileFiniteCollection ProjectiveFiniteCollection
  AnnealedTupleResidualCounting AnnealedTupleResidualConnectedLawCoordinates

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

/-- Coordinates: degree, ordered kernel pair, second exposure moment,
third exposure moment, exposure variance, and third exposure cumulant. -/
def profileVector (M : CompactBJRModel S) (ν : ProbabilityMeasure S) : Fin 6 → ℝ :=
  ![degreeFunctional M ν,kernelPairFunctional M ν,exposureMomentFunctional M 2 ν,
    exposureMomentFunctional M 3 ν,varianceFunctional M ν,thirdCumulantFunctional M ν]

def perronVector (M : CompactBJRModel S) (hM : M.IsRegularCritical) : Fin 6 → ℝ :=
  ![1,M.alpha hM,M.alpha hM,M.beta hM,M.alpha hM-1,M.beta hM-3*M.alpha hM+2]

theorem profileVector_continuous (M : CompactBJRModel S) : Continuous (profileVector M) := by
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [profileVector] using degreeFunctional_continuous M
  · simpa [profileVector] using kernelPairFunctional_continuous M
  · simpa [profileVector] using exposureMomentFunctional_continuous M 2
  · simpa [profileVector] using exposureMomentFunctional_continuous M 3
  · simpa [profileVector] using varianceFunctional_continuous M
  · simpa [profileVector] using thirdCumulantFunctional_continuous M

theorem profileVector_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    profileVector M (perronMark M hM) = perronVector M hM := by
  simp only [profileVector,perronVector,degreeFunctional_perronMark,kernelPairFunctional_perronMark,
    exposureMomentFunctional_two_perronMark,exposureMomentFunctional_three_perronMark,
    varianceFunctional_perronMark,thirdCumulantFunctional_perronMark]

def normalizedSelectedVector {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) : Fin 6 → ℝ :=
  let K : ℝ := ∑ i, (k i : ℝ)
  let u := selectedTypes hk f (fun i ↦ (p i).1)
  ![K⁻¹ * totalDegree M u,K⁻¹ ^ 2 * pairKernelSum M u,
    K⁻¹ ^ 2 * exposureMoment M u 2,K⁻¹ ^ 3 * exposureMoment M u 3,
    K⁻¹ ^ 2 * exposureVariance M u,K⁻¹ ^ 3 * exposureThirdCumulant M u]

theorem profileVector_pooledMark_eq_normalizedSelectedVector {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hq : 0 < q) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) :
    profileVector M (pooledMark hq k hk p) = normalizedSelectedVector M hk f p := by
  unfold profileVector normalizedSelectedVector
  dsimp only
  rw [degreeFunctional_pooledMark_eq_selected M hq hk f p,
    kernelPairFunctional_pooledMark_eq_selected M hq hk f p,
    exposureMomentFunctional_pooledMark_eq_selected M hq hk f p 2,
    exposureMomentFunctional_pooledMark_eq_selected M hq hk f p 3,
    varianceFunctional_pooledMark_eq_selected M hq hk f p,
    thirdCumulantFunctional_pooledMark_eq_selected M hq hk f p]

/-- Ordinary measurability on the literal product sampling space follows
through the continuous type-only mark map, without assuming that the weak
and Giry sigma-algebras of probability measures have been identified. -/
theorem normalizedSelectedVector_measurable {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hq : 0 < q) (hk : ∀ i, 0 < k i) (f : Placements n k) :
    Measurable (normalizedSelectedVector M hk f) := by
  have he : normalizedSelectedVector M hk f =
      (profileVector M ∘ typesMark (pooled_card_pos hq k hk)) ∘ pooledTypes k := by
    funext p
    exact (profileVector_pooledMark_eq_normalizedSelectedVector M hq hk f p).symm
  rw [he]
  exact ((profileVector_continuous M).comp (typesMark_continuous _)).measurable.comp
    (pooledTypes_measurable k)

/-- Genuine joint concentration of all normalized selected moment and pair
quantities at their actual Perron values.  No random-moment convergence
interface is supplied as a hypothesis. -/
theorem normalizedSelectedVector_probability_tendsto_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (R q : ℕ) (hq : 0 < q) (L : ℝ) (hL : 0 ≤ L)
    (N : ℕ → ℕ) (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (f : ∀ n, Placements (N n) (k n))
    (g : ℕ → Fin q → C(S,ℝ))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i))
    (hKTop : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i : ℝ) * ‖g n i‖ ≤ L)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (productLaw M (k n) (r n) (g n) (hC n)).real
      {p | ε ≤ ‖normalizedSelectedVector M (hk n) (f n) p - perronVector M hM‖})
      atTop (𝓝 0) := by
  let F : ProbabilityMeasure S → ℝ := fun ν ↦ ‖profileVector M ν - perronVector M hM‖
  have hF : Continuous F := ((profileVector_continuous M).sub continuous_const).norm
  have hzero : F (perronMark M hM) = 0 := by
    simp only [F,profileVector_perronMark,sub_self,norm_zero]
  have h := pooled_continuousFunctional_probability_tendsto_zero
    M hM R q hq L hL k r hk g hC hKTop hr hg F hF ε hε
  rw [hzero] at h
  simpa only [F,sub_zero,abs_norm,profileVector_pooledMark_eq_normalizedSelectedVector M hq (hk _) (f _)] using h

end PerronWright.AnnealedProfileFunctionalConcentration
