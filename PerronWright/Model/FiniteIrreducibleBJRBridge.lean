import PerronWright.Model.FiniteIrreduciblePerronQuantities
import PerronWright.Model.CompactBJR
import PerronWright.Kernel.Complex

/-!
# The literal finite model as discrete continuous BJR data

The finite law is the actual weighted sum of Dirac measures.  Discrete
continuity and full support are proved, and its integral action is the
displayed weighted mean matrix.  This adapter deliberately supplies no B2
or `IsRegularCritical` proof: irreducibility permits periodic kernels.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

@[simp] theorem measure_singleton (M : FiniteIrreducibleModel S) (a : S) :
    M.measure {a} = ENNReal.ofReal (M.weight a) := by
  simp only [measure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_single a]
  · simp
  · intro b hb
    simp [hb]

@[simp] theorem measure_real_singleton (M : FiniteIrreducibleModel S) (a : S) :
    M.measure.real {a} = M.weight a := by
  rw [Measure.real, M.measure_singleton, ENNReal.toReal_ofReal (M.weight_pos a).le]

instance measure_isOpenPos (M : FiniteIrreducibleModel S) : M.measure.IsOpenPosMeasure where
  open_pos U _ hU := by
    obtain ⟨a, ha⟩ := hU
    have hmass : 0 < M.measure {a} := by
      rw [M.measure_singleton]
      exact ENNReal.ofReal_pos.mpr (M.weight_pos a)
    exact (hmass.trans_le (measure_mono (Set.singleton_subset_iff.mpr ha))).ne'

theorem integral_measure (M : FiniteIrreducibleModel S)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : S → E) :
    (∫ a, f a ∂M.measure) = ∑ a, M.weight a • f a := by
  rw [measure, integral_finsetSum_measure]
  · simp [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal,
      (M.weight_pos _).le]
  · intro a _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

def continuousKernel (M : FiniteIrreducibleModel S) : ContinuousKernel S where
  toContinuousMap := ⟨fun p ↦ M.kernel p.1 p.2, continuous_of_discreteTopology⟩
  symmetric' := M.symmetric
  nonneg' := M.kernel_nonneg

omit [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem continuousKernel_apply (M : FiniteIrreducibleModel S) (a b : S) :
    M.continuousKernel a b = M.kernel a b := rfl

def bjrModel (M : FiniteIrreducibleModel S) : CompactBJRModel S where
  mu := M.measure
  isProbabilityMeasure := inferInstance
  isOpenPosMeasure := inferInstance
  kernel := M.continuousKernel

@[simp] theorem bjrModel_mu (M : FiniteIrreducibleModel S) : M.bjrModel.mu = M.measure := rfl

@[simp] theorem bjrModel_kernel (M : FiniteIrreducibleModel S) :
    M.bjrModel.kernel = M.continuousKernel := rfl

theorem continuous_action_apply (M : FiniteIrreducibleModel S) (f : C(S, ℝ)) (a : S) :
    M.continuousKernel.action M.measure f a = M.action f a := by
  rw [ContinuousKernel.action_apply, M.integral_measure]
  simp only [continuousKernel_apply, smul_eq_mul, action]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem bjr_integralAction (M : FiniteIrreducibleModel S) (f : S → ℝ) :
    M.bjrModel.integralAction f = M.action f := by
  funext a
  change (∫ b, M.continuousKernel a b * f b ∂M.measure) = _
  rw [M.integral_measure]
  simp only [continuousKernel_apply, smul_eq_mul, action]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem degree_eq_weighted_sum (M : FiniteIrreducibleModel S) (a : S) :
    M.bjrModel.kernel.degree M.bjrModel.mu a = ∑ b, M.kernel a b * M.weight b := by
  change (∫ b, M.continuousKernel a b ∂M.measure) = _
  rw [M.integral_measure]
  simp only [continuousKernel_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

theorem continuous_complexAction_apply (M : FiniteIrreducibleModel S)
    (f : C(S, ℂ)) (a : S) :
    M.continuousKernel.complexAction M.measure f a =
      ∑ b, (M.kernel a b * M.weight b : ℝ) * f b := by
  rw [ContinuousKernel.complexAction_apply, M.integral_measure]
  simp only [continuousKernel_apply, Complex.real_smul, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

def continuousPerronFunction (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    C(S, ℝ) := ⟨M.perronFunction hcrit, continuous_of_discreteTopology⟩

theorem continuousPerronFunction_fixed (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    M.continuousKernel.action M.measure (M.continuousPerronFunction hcrit) =
      M.continuousPerronFunction hcrit := by
  ext a
  rw [M.continuous_action_apply]
  exact congrFun (M.perronFunction_fixed hcrit) a

end PerronWright.FiniteIrreducibleModel
