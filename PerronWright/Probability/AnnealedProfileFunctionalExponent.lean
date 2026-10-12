import PerronWright.Probability.AnnealedProfileFunctionalConcentration

/-!
# Exact thermal and cubic decomposition of the literal residual exponent

All profile functionals below are functions of an actual probability
measure.  The selected finite-n exponent is identified with them by the
proved empirical coordinate identities, not an expansion hypothesis.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedProfileFunctionalExponent

open AnnealedProfileFunctionalContinuous AnnealedProfileFunctionalSampled
  FreshTypePerronCentering FreshTypeEmpiricalIdentities FreshTypeCumulantExpansion
  AnnealedTupleResidualCounting AnnealedTupleResidualConnectedLawCoordinates
  EmpiricalTypeMarks EmpiricalMarkConcentration ProjectiveFiniteCollection ProfileFiniteCollection
  ProjectiveKernelClosure

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def criticalFunctional (M : CompactBJRModel S) (ν : ProbabilityMeasure S) : ℝ :=
  -1/2 + degreeFunctional M ν - kernelPairFunctional M ν / 2 + varianceFunctional M ν / 2

def phiFunctional (M : CompactBJRModel S) (t : ℝ) (ν : ProbabilityMeasure S) : ℝ :=
  -1/2 + t * degreeFunctional M ν - t * kernelPairFunctional M ν / 2 +
    t^2 * varianceFunctional M ν / 2

/-- The coefficient remaining after removing the critical quadratic
functional and dividing the thermal part by `t-1`. -/
def thermalFunctional (M : CompactBJRModel S) (t : ℝ) (ν : ProbabilityMeasure S) : ℝ :=
  degreeFunctional M ν - kernelPairFunctional M ν / 2 + (t+1) * varianceFunctional M ν / 2

def gammaFunctional (M : CompactBJRModel S) (t : ℝ) (ν : ProbabilityMeasure S) : ℝ :=
  -1/6 - t^2 * varianceFunctional M ν / 2 - t^3 * thirdCumulantFunctional M ν / 6

theorem phi_eq_critical_add_thermal (M : CompactBJRModel S) (t : ℝ) (ν : ProbabilityMeasure S) :
    phiFunctional M t ν = criticalFunctional M ν + (t-1) * thermalFunctional M t ν := by
  unfold phiFunctional criticalFunctional thermalFunctional
  ring

theorem thermalFunctional_continuous (M : CompactBJRModel S) (t : ℝ) :
    Continuous (thermalFunctional M t) :=
  ((degreeFunctional_continuous M).sub ((kernelPairFunctional_continuous M).div_const 2)).add
    ((continuous_const.mul (varianceFunctional_continuous M)).div_const 2)

theorem gammaFunctional_continuous (M : CompactBJRModel S) (t : ℝ) :
    Continuous (gammaFunctional M t) :=
  (continuous_const.sub ((continuous_const.mul (varianceFunctional_continuous M)).div_const 2)).sub
    ((continuous_const.mul (thirdCumulantFunctional_continuous M)).div_const 6)

theorem thermalFunctional_joint_continuous (M : CompactBJRModel S) :
    Continuous (fun z : ℝ × ProbabilityMeasure S ↦ thermalFunctional M z.1 z.2) := by
  unfold thermalFunctional
  exact (((degreeFunctional_continuous M).comp continuous_snd).sub
    (((kernelPairFunctional_continuous M).comp continuous_snd).div_const 2)).add
      (((continuous_fst.add continuous_const).mul
        ((varianceFunctional_continuous M).comp continuous_snd)).div_const 2)

theorem gammaFunctional_joint_continuous (M : CompactBJRModel S) :
    Continuous (fun z : ℝ × ProbabilityMeasure S ↦ gammaFunctional M z.1 z.2) := by
  unfold gammaFunctional
  exact (continuous_const.sub (((continuous_fst.pow 2).mul
    ((varianceFunctional_continuous M).comp continuous_snd)).div_const 2)).sub
      (((continuous_fst.pow 3).mul
        ((thirdCumulantFunctional_continuous M).comp continuous_snd)).div_const 6)

theorem criticalFunctional_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    criticalFunctional M (perronMark M hM) = 0 := by
  simp only [criticalFunctional,degreeFunctional_perronMark,kernelPairFunctional_perronMark,
    varianceFunctional_perronMark]
  ring

theorem thermalFunctional_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) (t : ℝ) :
    thermalFunctional M t (perronMark M hM) =
      M.alpha hM / 2 + (t-1) * (M.alpha hM-1) / 2 := by
  simp only [thermalFunctional,degreeFunctional_perronMark,kernelPairFunctional_perronMark,
    varianceFunctional_perronMark]
  ring

theorem thermalFunctional_one_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    thermalFunctional M 1 (perronMark M hM) = M.alpha hM / 2 := by
  rw [thermalFunctional_perronMark]
  ring

theorem gammaFunctional_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) (t : ℝ) :
    gammaFunctional M t (perronMark M hM) =
      -1/6 - t^2 * (M.alpha hM-1) / 2 - t^3 * (M.beta hM-3*M.alpha hM+2) / 6 := by
  simp only [gammaFunctional,varianceFunctional_perronMark,thirdCumulantFunctional_perronMark]

theorem gammaFunctional_one_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    gammaFunctional M 1 (perronMark M hM) = -M.beta hM / 6 := by
  rw [gammaFunctional_perronMark]
  ring

/-- Exact finite-n decomposition.  The diagonal and retained third-cumulant
terms are explicit rather than discarded into an unproved remainder. -/
theorem pooledCumulantExponent_decomposition {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (t : ℝ) (hq : 0 < q)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (p : StateFamily (S := S) k) :
    let K : ℝ := ∑ i, (k i : ℝ)
    let ν := pooledMark hq k hk p
    let u := selectedTypes hk f (fun i ↦ (p i).1)
    pooledCumulantExponent M hM t hq hk f p =
      K * pooledQuadratic M hM hq k hk (residualKernel M) p / (2*(n:ℝ)) +
      ((t-1)*K^2/(n:ℝ)) * thermalFunctional M t ν +
      (K^3/(n:ℝ)^2) * gammaFunctional M t ν +
      t * diagonalKernelSum M u / (2*(n:ℝ)) +
      (t^3*K^4/(6*(n:ℝ)^3)) * thirdCumulantFunctional M ν := by
  dsimp only
  unfold pooledCumulantExponent thermalFunctional gammaFunctional
  dsimp only
  rw [degreeFunctional_pooledMark_eq_selected M hq hk f p,
    kernelPairFunctional_pooledMark_eq_selected M hq hk f p,
    varianceFunctional_pooledMark_eq_selected M hq hk f p,
    thirdCumulantFunctional_pooledMark_eq_selected M hq hk f p]
  have hK0 := (totalSize_pos hq k hk).ne'
  field_simp
  ring

end PerronWright.AnnealedProfileFunctionalExponent
