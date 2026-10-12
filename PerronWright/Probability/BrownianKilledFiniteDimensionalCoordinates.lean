import PerronWright.Probability.BrownianKilledSemigroupJointLaw
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Probability.Kernel.Composition.MapComap

/-! # Ordered Brownian sampling coordinates and actual killed chains

Nonnegative deterministic gaps define ordered sample times, including
time zero. The recursively constructed finite endpoint chain uses only
the genuine killed Brownian kernel already derived from independent
forward paths. Its coordinate append map is genuinely Borel measurable.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledFiniteDimensionalCoordinates

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianKilledTransitionKernel BrownianKilledSemigroup

abbrev EndpointVector (n : ℕ) := Fin (n+1) → ℝ

def sampleTime (gaps : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 := ∑ i ∈ Finset.range n, gaps i

@[simp] theorem sampleTime_zero (gaps : ℕ → ℝ≥0) : sampleTime gaps 0 = 0 := by
  simp [sampleTime]

theorem sampleTime_succ (gaps : ℕ → ℝ≥0) (n : ℕ) :
    sampleTime gaps (n+1) = sampleTime gaps n+gaps n := Finset.sum_range_succ _ _

theorem sampleTime_monotone (gaps : ℕ → ℝ≥0) : Monotone (sampleTime gaps) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [sampleTime_succ]
  exact le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ gaps n)

theorem sampleTime_ordered (times : ℕ → ℝ≥0) (hmono : Monotone times) (hzero : times 0 = 0)
    (n : ℕ) : sampleTime (fun j ↦ times (j+1)-times j) n = times n := by
  induction n with
  | zero => rw [sampleTime_zero,hzero]
  | succ n ih =>
    rw [sampleTime_succ,ih,add_tsub_cancel_of_le (hmono (Nat.le_succ n))]

def endpointTuple (n : ℕ) (x : ℝ) (gaps : ℕ → ℝ≥0) (f : Path) : EndpointVector n :=
  fun i ↦ x+f (sampleTime gaps i.val)

theorem continuous_endpointTuple (n : ℕ) (x : ℝ) (gaps : ℕ → ℝ≥0) :
    Continuous (endpointTuple n x gaps) :=
  continuous_pi (fun _ ↦ continuous_const.add (continuous_eval _))

@[simp] theorem endpointTuple_last (n : ℕ) (x : ℝ) (gaps : ℕ → ℝ≥0) (f : Path) :
    endpointTuple n x gaps f (Fin.last n) = x+f (sampleTime gaps n) := rfl

theorem endpointTuple_past (n : ℕ) (x : ℝ) (gaps : ℕ → ℝ≥0) (f : Path) :
    endpointTuple n x gaps (pastPath (sampleTime gaps n) f) = endpointTuple n x gaps f := by
  funext i
  change x+f (min (sampleTime gaps i.val) (sampleTime gaps n)) = x+f (sampleTime gaps i.val)
  rw [min_eq_left ((sampleTime_monotone gaps) (Nat.le_of_lt_succ i.isLt))]

def appendEndpoint (n : ℕ) (p : EndpointVector n × ℝ) : EndpointVector (n+1) :=
  Fin.snoc p.1 p.2

theorem continuous_appendEndpoint (n : ℕ) : Continuous (appendEndpoint n) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [appendEndpoint,Fin.snoc_last] using continuous_snd
  · simpa only [appendEndpoint,Fin.snoc_castSucc,Function.comp_def] using
      (continuous_apply j).comp continuous_fst

theorem endpointTuple_succ (n : ℕ) (x : ℝ) (gaps : ℕ → ℝ≥0) (f : Path) :
    endpointTuple (n+1) x gaps f =
      appendEndpoint n (endpointTuple n x gaps f,x+f (sampleTime gaps (n+1))) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [endpointTuple,appendEndpoint,Fin.snoc_last,Fin.val_last]
  · simp only [endpointTuple,appendEndpoint,Fin.snoc_castSucc,Fin.val_castSucc]

def endpointKernel (n : ℕ) (level : ℝ) (t : ℝ≥0) : Kernel (EndpointVector n) ℝ :=
  (killedKernel level t).comap (fun v ↦ v (Fin.last n)) (measurable_pi_apply _)

@[simp] theorem endpointKernel_apply (n : ℕ) (level : ℝ) (t : ℝ≥0) (v : EndpointVector n) :
    endpointKernel n level t v = transitionLaw level t (v (Fin.last n)) := rfl

instance endpointKernel_isFinite (n : ℕ) (level : ℝ) (t : ℝ≥0) :
    IsFiniteKernel (endpointKernel n level t) := by
  unfold endpointKernel
  infer_instance

/-- Killed ordered endpoint chain with the genuine initial survival gate. -/
def chainLaw (level x : ℝ) (gaps : ℕ → ℝ≥0) : (n : ℕ) → Measure (EndpointVector n)
  | 0 => if level < x then Measure.dirac (fun _ ↦ x) else 0
  | n+1 => ((chainLaw level x gaps n) ⊗ₘ endpointKernel n level (gaps n)).map (appendEndpoint n)

@[simp] theorem chainLaw_zero (level x : ℝ) (gaps : ℕ → ℝ≥0) :
    chainLaw level x gaps 0 = if level < x then Measure.dirac (fun _ ↦ x) else 0 := rfl

theorem chainLaw_succ (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    chainLaw level x gaps (n+1) =
      ((chainLaw level x gaps n) ⊗ₘ endpointKernel n level (gaps n)).map (appendEndpoint n) := rfl

instance chainLaw_isFinite (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    IsFiniteMeasure (chainLaw level x gaps n) := by
  induction n with
  | zero => rw [chainLaw_zero]; split_ifs <;> infer_instance
  | succ n ih => rw [chainLaw_succ]; infer_instance

/-- Exact iterated nonnegative kernel integration for an arbitrary
coupled endpoint test of the recursively built genuine killed chain. -/
theorem lintegral_chainLaw_succ (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ)
    {Φ : EndpointVector (n+1) → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ v, Φ v ∂chainLaw level x gaps (n+1)) =
      ∫⁻ v, ∫⁻ y, Φ (appendEndpoint n (v,y)) ∂transitionLaw level (gaps n) (v (Fin.last n))
        ∂chainLaw level x gaps n := by
  rw [chainLaw_succ,lintegral_map hΦ (continuous_appendEndpoint n).measurable]
  exact Measure.lintegral_compProd (hΦ.comp (continuous_appendEndpoint n).measurable)

end PerronWright.BrownianKilledFiniteDimensionalCoordinates
