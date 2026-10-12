import PerronWright.Probability.ConnectedTypeDomination
import PerronWright.Model.FiniteIrreducibleBJRBridge
import PerronWright.Analysis.FiniteIrreducibleRadiusResponse
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Actual finite irreducible weighted connected type-vector laws

Only the data-only finite BJR construction is used for the literal graph
weight and sampling measure. No B2 or regular-critical adapter is used.
The Perron law is the actual weighted finite Dirac sum. The connected
law and its type-vector marginal are actual probability measures, with
an exact field-tilt Laplace identity. Eventual positivity and profile
concentration from finite field coefficients are separate next steps.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleConnectedTypeLaw

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def perronMeasure (M : FiniteIrreducibleModel S) (hM : M.IsCritical) : Measure S :=
  ∑ a, ENNReal.ofReal (M.weight a * M.perronFunction hM a) • Measure.dirac a

instance perronMeasure_isProbability (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    IsProbabilityMeasure (perronMeasure M hM) := by
  constructor
  simp only [perronMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦
    (mul_pos (M.weight_pos a) (M.perronFunction_pos hM a)).le)]
  change ENNReal.ofReal (M.average (M.perronFunction hM)) = 1
  rw [M.perronFunction_average]
  simp

def perronLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical) : ProbabilityMeasure S :=
  ⟨perronMeasure M hM, inferInstance⟩

theorem integral_perronLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (f : S → ℝ) :
    (∫ a, f a ∂(perronLaw M hM : Measure S)) =
      ∑ a, M.weight a * M.perronFunction hM a * f a := by
  change (∫ a, f a ∂perronMeasure M hM) = _
  rw [perronMeasure, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (mul_pos (M.weight_pos _) (M.perronFunction_pos hM _)).le]
  · intro a _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

abbrev State (S : Type*) (k : ℕ) := ConnectedTypeLaw.State S k

def law (M : FiniteIrreducibleModel S) (g : C(S, ℝ)) (k r : ℕ)
    (hC : 0 < M.bjrModel.fieldConnectedWeight g k r) : Measure (State S k) :=
  ConnectedTypeLaw.law M.bjrModel g k r hC

instance law_isProbability (M : FiniteIrreducibleModel S) (g : C(S, ℝ)) (k r : ℕ)
    (hC : 0 < M.bjrModel.fieldConnectedWeight g k r) : IsProbabilityMeasure (law M g k r hC) :=
  ConnectedTypeLaw.law_isProbability _ _ _ _ _

def probability (M : FiniteIrreducibleModel S) (g : C(S, ℝ)) (k r : ℕ)
    (hC : 0 < M.bjrModel.fieldConnectedWeight g k r) : ProbabilityMeasure (State S k) :=
  ⟨law M g k r hC, inferInstance⟩

/-- The actual weighted law of the sampled type vector, after summing
over the actual eligible connected labelled graphs. -/
def typeVectorLaw (M : FiniteIrreducibleModel S) (g : C(S, ℝ)) (k r : ℕ)
    (hC : 0 < M.bjrModel.fieldConnectedWeight g k r) : ProbabilityMeasure (Fin k → S) :=
  (probability M g k r hC).map measurable_fst.aemeasurable

theorem laplace_eq_enumerator_ratio (M : FiniteIrreducibleModel S)
    (g f : C(S, ℝ)) (k r : ℕ) (hC : 0 < M.bjrModel.fieldConnectedWeight g k r) :
    (∫ p, Real.exp (ConnectedTypeLaw.typeSum f p.1) ∂law M g k r hC) =
      M.bjrModel.fieldConnectedWeight (g + f) k r / M.bjrModel.fieldConnectedWeight g k r :=
  ConnectedTypeLaw.laplace_eq_enumerator_ratio _ _ _ _ _ _

theorem typeVector_laplace_eq_enumerator_ratio (M : FiniteIrreducibleModel S)
    (g f : C(S, ℝ)) (k r : ℕ) (hC : 0 < M.bjrModel.fieldConnectedWeight g k r) :
    (∫ x, Real.exp (ConnectedTypeLaw.typeSum (k := k) f x)
      ∂(typeVectorLaw M g k r hC : Measure (Fin k → S))) =
      M.bjrModel.fieldConnectedWeight (g + f) k r / M.bjrModel.fieldConnectedWeight g k r := by
  rw [typeVectorLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (f := fun x : Fin k → S ↦ Real.exp (ConnectedTypeLaw.typeSum f x))
      measurable_fst.aemeasurable
      (Real.continuous_exp.comp (ConnectedTypeLaw.typeSum_continuous (k := k) f)).measurable.aestronglyMeasurable]
  exact laplace_eq_enumerator_ratio M g f k r hC

def centeredSum (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {k : ℕ} (f : C(S, ℝ)) (p : State S k) : ℝ :=
  ConnectedTypeLaw.typeSum f p.1 - (k : ℝ) * ∫ a, f a ∂(perronLaw M hM : Measure S)

theorem centered_laplace_eq_enumerator_ratio (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (g f : C(S, ℝ)) (k r : ℕ)
    (hC : 0 < M.bjrModel.fieldConnectedWeight g k r) :
    (∫ p, Real.exp (centeredSum M hM f p) ∂law M g k r hC) =
      Real.exp (-(k : ℝ) * ∫ a, f a ∂(perronLaw M hM : Measure S)) *
        (M.bjrModel.fieldConnectedWeight (g + f) k r / M.bjrModel.fieldConnectedWeight g k r) := by
  simp_rw [centeredSum, Real.exp_sub, div_eq_mul_inv]
  rw [integral_mul_const, laplace_eq_enumerator_ratio]
  rw [show -(k : ℝ) * (∫ a, f a ∂(perronLaw M hM : Measure S)) =
    -((k : ℝ) * ∫ a, f a ∂(perronLaw M hM : Measure S)) by ring, Real.exp_neg]
  ring

end PerronWright.FiniteIrreducibleConnectedTypeLaw
