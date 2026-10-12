import PerronWright.Probability.BrownianPositiveBridgeFiniteDimensionalSource
import PerronWright.Probability.BrownianPositiveBridgeFiniteDimensionalDensity
import PerronWright.Probability.BrownianPositiveBridgeFiniteDimensionalLaw
import PerronWright.Probability.BrownianKilledFiniteDimensionalOrderedDensity

/-! # Literal internal coordinates of an actual positive pinned bridge

There are n internal points and one further exit gap. The density below
is the finite killed head product times its literal last exit kernel,
with the previously proved pinned normalization. Its equality with the
actual conditional law is proved in the subsequent files, not assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeMultiPointCoordinates

open BrownianPathLaw BrownianKilledFiniteDimensionalCoordinates
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalDensity
open BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel
open BrownianPositiveBridgeFiniteDimensionalDensity BrownianPositiveBridgeFiniteDimensionalLaw

def internalTimes (n : ℕ) (gaps : ℕ → ℝ≥0) (i : Fin n) : ℝ≥0 := sampleTime gaps (i.val+1)

def internalEval (n : ℕ) (gaps : ℕ → ℝ≥0) (g : Path) : FreeVector n := fun i ↦ g (internalTimes n gaps i)

theorem continuous_internalEval (n : ℕ) (gaps : ℕ → ℝ≥0) : Continuous (internalEval n gaps) :=
  continuous_pi (fun _ ↦ continuous_eval _)

theorem internalTimes_le_final (n : ℕ) (gaps : ℕ → ℝ≥0) (i : Fin n) :
    internalTimes n gaps i ≤ sampleTime gaps (n+1) :=
  sampleTime_monotone gaps (by omega)

def orthant (n : ℕ) (cuts : FreeVector n) : Set (FreeVector n) := {v | ∀ i, cuts i < v i}

theorem measurableSet_orthant (n : ℕ) (cuts : FreeVector n) : MeasurableSet (orthant n cuts) := by
  have he : orthant n cuts = ⋂ i, {v : FreeVector n | cuts i < v i} := by ext v; simp [orthant]
  rw [he]
  exact MeasurableSet.iInter (fun i ↦ (isOpen_lt continuous_const (continuous_apply i)).measurableSet)

def headLaw (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (cuts : FreeVector n) : Measure (FreeVector n) :=
  (freeTupleLaw a gaps n).restrict (orthant n cuts)

instance headLaw_isFinite (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (cuts : FreeVector n) :
    IsFiniteMeasure (headLaw n a gaps cuts) := by unfold headLaw; infer_instance

def exitHeadLaw (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (cuts : FreeVector n) : Measure ℝ :=
  (headLaw n a gaps cuts).map (lastState n a)

instance exitHeadLaw_isFinite (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (cuts : FreeVector n) :
    IsFiniteMeasure (exitHeadLaw n a gaps cuts) := by unfold exitHeadLaw; infer_instance

def exitIntegral (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (cuts : FreeVector n) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, density x (gaps n) (z+a) ∂exitHeadLaw n a gaps cuts

def exitRatio (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (cuts : FreeVector n) (z : ℝ) : ℝ≥0∞ :=
  exitIntegral n a gaps cuts z/gaussianPDF 0 (sampleTime gaps (n+1)) z

theorem finalTime_pos (n : ℕ) (gaps : ℕ → ℝ≥0) (hgap : 0 < gaps n) : 0 < sampleTime gaps (n+1) := by
  rw [sampleTime_succ]
  exact hgap.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ sampleTime gaps n))

theorem continuous_exitIntegral (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (hgap : 0 < gaps n) (cuts : FreeVector n) :
    Continuous (exitIntegral n a gaps cuts) := continuous_last_kernel_integral (exitHeadLaw n a gaps cuts) _ hgap a

theorem continuous_exitRatio (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (hgap : 0 < gaps n) (cuts : FreeVector n) :
    Continuous (exitRatio n a gaps cuts) :=
  continuous_exit_ratio (exitHeadLaw n a gaps cuts) _ _ hgap (finalTime_pos n gaps hgap) a

def multiDensity (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (v : FreeVector n) : ℝ≥0∞ :=
  (normalization a (sampleTime gaps (n+1)))⁻¹*
    (jointDensity n a gaps v*density (lastState n a v) (gaps n) a)/
      gaussianPDF 0 (sampleTime gaps (n+1)) 0

theorem measurable_multiDensity (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) : Measurable (multiDensity n a gaps) := by
  have hp : Measurable (fun v : FreeVector n ↦ (lastState n a v,a)) :=
    (continuous_lastState n a).measurable.prodMk measurable_const
  have hc := (measurable_joint_density (gaps n)).comp hp
  have hd : Measurable (fun v : FreeVector n ↦ density (lastState n a v) (gaps n) a) := by
    simpa only [Function.comp_def] using hc
  unfold multiDensity
  simp only [div_eq_mul_inv]
  exact (measurable_const.mul ((measurable_jointDensity n a gaps).mul hd)).mul_const _

end PerronWright.BrownianPositiveBridgeMultiPointCoordinates
