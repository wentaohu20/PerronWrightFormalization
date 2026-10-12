import PerronWright.Probability.FinitePoissonPointLaw
import Mathlib.Probability.Independence.Integration
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Exact Laplace functional of the constructed spatial law

The functional is evaluated on the actual finite random measure.  Its
Poisson formula follows from independent location integration and the
exponential series, with no point-process Laplace formula assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

noncomputable section

namespace PerronWright.FinitePoissonPointLaplace

open FinitePointMeasureCompact FinitePoissonPointLaw

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [BorelSpace E] [SecondCountableTopology E] [HasOuterApproxClosed E]

def expNeg (x : ℝ≥0) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(x : ℝ)))

theorem measurable_expNeg : Measurable expNeg := by
  unfold expNeg
  fun_prop

theorem expNeg_le_one (x : ℝ≥0) : expNeg x ≤ 1 := by
  unfold expNeg
  exact (ENNReal.ofReal_le_one).mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr x.property))

/-- The literal Laplace functional of a finite integer atomic measure. -/
def laplace (f : E → ℝ≥0) (η : PointMeasure E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(∫⁻ z, (f z : ℝ≥0∞)
    ∂((η : FiniteMeasure E) : Measure E)).toReal))

omit [SecondCountableTopology E] in
theorem measurable_laplace {f : E → ℝ≥0} (hf : Measurable f) :
    Measurable (laplace f) := by
  have hi : Measurable (fun η : PointMeasure E ↦
      ∫⁻ z, (f z : ℝ≥0∞) ∂((η : FiniteMeasure E) : Measure E)) :=
    (Measure.measurable_lintegral
      (measurable_coe_nnreal_ennreal.comp hf)).comp
      FinitePointMeasureMeasurable.measurable_toMeasure
  exact ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp hi.ennreal_toReal.neg)

omit [TopologicalSpace E] [BorelSpace E] [SecondCountableTopology E]
  [HasOuterApproxClosed E] in
/-- Finite atomicity makes the literal nonnegative integral finite,
even when the measurable test is not bounded. -/
theorem point_lintegral_ne_top {f : E → ℝ≥0} (hf : Measurable f)
    (η : PointMeasure E) :
    (∫⁻ z, (f z : ℝ≥0∞) ∂((η : FiniteMeasure E) : Measure E)) ≠ ⊤ := by
  obtain ⟨n, x, hx⟩ := η.property
  have he : η = ofAtomsPoint x := Subtype.ext hx
  rw [he]
  simp only [ofAtomsPoint_val, FiniteAtomicPointMeasure.ofAtoms_toMeasure,
    lintegral_finsetSum_measure]
  have hd (a : E) : (∫⁻ z, (f z : ℝ≥0∞) ∂Measure.dirac a) = (f a : ℝ≥0∞) :=
    lintegral_dirac' a (measurable_coe_nnreal_ennreal.comp hf)
  simp_rw [hd]
  exact ENNReal.sum_ne_top.mpr (fun i _ ↦ ENNReal.coe_ne_top)

omit [TopologicalSpace E] [BorelSpace E] [SecondCountableTopology E]
  [HasOuterApproxClosed E] in
theorem laplace_ofAtomsPoint {f : E → ℝ≥0} (hf : Measurable f)
    {n : ℕ} (x : Fin n → E) :
    laplace f (ofAtomsPoint x) = ∏ i, expNeg (f (x i)) := by
  unfold laplace
  simp only [ofAtomsPoint_val, FiniteAtomicPointMeasure.ofAtoms_toMeasure,
    lintegral_finsetSum_measure]
  have hd (a : E) : (∫⁻ z, (f z : ℝ≥0∞) ∂Measure.dirac a) = (f a : ℝ≥0∞) :=
    lintegral_dirac' a (measurable_coe_nnreal_ennreal.comp hf)
  simp_rw [hd]
  rw [ENNReal.toReal_sum (fun i _ ↦ ENNReal.coe_ne_top)]
  simp only [ENNReal.coe_toReal, ← Finset.sum_neg_distrib, Real.exp_sum]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (Real.exp_pos _).le)

theorem iidAtomsLaw_laplace (μ : Measure E) [IsProbabilityMeasure μ]
    {f : E → ℝ≥0} (hf : Measurable f) (n : ℕ) :
    (∫⁻ η, laplace f η ∂iidAtomsLaw μ n) =
      (∫⁻ z, expNeg (f z) ∂μ) ^ n := by
  rw [iidAtomsLaw, lintegral_map (measurable_laplace hf) (measurable_ofAtomsPoint n)]
  simp_rw [laplace_ofAtomsPoint hf]
  have hg : Measurable (fun z ↦ expNeg (f z)) := measurable_expNeg.comp hf
  have hi := iIndepFun_pi (μ := fun _ : Fin n ↦ μ)
    (X := fun _ z ↦ expNeg (f z)) (fun _ ↦ hg.aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
    (fun i ↦ hg.comp (measurable_pi_apply i))]
  simp_rw [(measurePreserving_eval (fun _ : Fin n ↦ μ) _).lintegral_comp hg]
  simp

/-- Exact Poisson probability generating function from its actual mass series. -/
theorem poisson_weighted_power (r : ℝ≥0) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    (∑' n : ℕ, poissonMeasure r {n} * c ^ n) =
      ENNReal.ofReal (Real.exp ((r : ℝ) * (c.toReal - 1))) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * c.toReal)).mul_left
    (Real.exp (-(r : ℝ)))
  have he : Real.exp (-(r : ℝ)) * NormedSpace.exp ((r : ℝ) * c.toReal) =
      Real.exp ((r : ℝ) * (c.toReal - 1)) := by
    rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hs
  have ht : HasSum (fun n : ℕ ↦
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) * c.toReal ^ n)
      (Real.exp ((r : ℝ) * (c.toReal - 1))) := by
    have hfn : (fun n : ℕ ↦
        (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) * c.toReal ^ n) =
        (fun n : ℕ ↦ Real.exp (-(r : ℝ)) *
          (((r : ℝ) * c.toReal) ^ n / (n.factorial : ℝ))) := by
      funext n
      rw [mul_pow]
      ring
    rw [hfn]
    exact hs
  rw [← ht.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) ht.summable]
  congr 1
  funext n
  rw [poissonMeasure_singleton, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow c.toReal_nonneg, ENNReal.ofReal_toReal hc]

/-- The spatial Laplace formula is proved for every measurable nonnegative test. -/
theorem law_laplace (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {f : E → ℝ≥0} (hf : Measurable f) :
    (∫⁻ η, laplace f η ∂law r μ) = ENNReal.ofReal
      (Real.exp ((r : ℝ) * ((∫⁻ z, expNeg (f z) ∂μ).toReal - 1))) := by
  have hc : (∫⁻ z, expNeg (f z) ∂μ) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _z, (1 : ℝ≥0∞) ∂μ := lintegral_mono (fun z ↦ expNeg_le_one (f z))
      _ = 1 := by simp
  simp only [law, lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul,
    iidAtomsLaw_laplace μ hf]
  exact poisson_weighted_power r (ne_top_of_le_ne_top ENNReal.one_ne_top hc)

end PerronWright.FinitePoissonPointLaplace
