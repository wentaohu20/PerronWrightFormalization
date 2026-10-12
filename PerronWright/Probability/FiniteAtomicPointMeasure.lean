import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Literal finite integer atomic measures and partition tests

Finite point measures are actual finite sums of Dirac masses. Their
integrals and set evaluations are proved from these sums, and the atom
map is continuous for mathlib's genuine finite-measure weak topology.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FiniteAtomicPointMeasure

variable {E : Type*} [MeasurableSpace E]

/-- The actual integer atomic measure of a finite list, retaining
multiplicities when atoms coincide. -/
def ofAtoms {n : ℕ} (x : Fin n → E) : FiniteMeasure E :=
  ⟨∑ i, Measure.dirac (x i), by infer_instance⟩

@[simp] theorem ofAtoms_toMeasure {n : ℕ} (x : Fin n → E) :
    (ofAtoms x : Measure E) = ∑ i, Measure.dirac (x i) := rfl

/-- The literal number of labelled atoms in a set. -/
def atomCount {n : ℕ} (x : Fin n → E) (A : Set E) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i ↦ x i ∈ A)).card

theorem ofAtoms_apply {n : ℕ} (x : Fin n → E) {A : Set E} (hA : MeasurableSet A) :
    (ofAtoms x : Measure E) A = (atomCount x A : ℝ≥0∞) := by
  classical
  simp [ofAtoms_toMeasure, Measure.finsetSum_apply, hA, Measure.dirac_apply',
    Set.indicator_apply, atomCount]

@[simp] theorem ofAtoms_mass {n : ℕ} (x : Fin n → E) : (ofAtoms x).mass = n := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass, ofAtoms_apply x MeasurableSet.univ]
  simp [atomCount]

theorem ofAtoms_apply_real {n : ℕ} (x : Fin n → E) {A : Set E} (hA : MeasurableSet A) :
    (ofAtoms x : Measure E).real A = (atomCount x A : ℝ) := by
  rw [measureReal_def, ofAtoms_apply x hA]
  simp

theorem ofAtoms_integrable [MeasurableSingletonClass E] {n : ℕ}
    (x : Fin n → E) (f : E → ℝ) : Integrable f (ofAtoms x : Measure E) := by
  rw [ofAtoms_toMeasure]
  exact integrable_finsetSum_measure.mpr (fun i _ ↦ integrable_dirac (by simp))

theorem ofAtoms_integral [MeasurableSingletonClass E] {n : ℕ}
    (x : Fin n → E) (f : E → ℝ) :
    (∫ z, f z ∂(ofAtoms x : Measure E)) = ∑ i, f (x i) := by
  rw [ofAtoms_toMeasure, integral_finsetSum_measure]
  · simp only [integral_dirac]
  · intro i _
    exact integrable_dirac (by simp)

/-- An actual finite list of atoms is a measurable random finite measure
for the evaluation sigma algebra, without any topological assumptions. -/
theorem measurable_ofAtoms (n : ℕ) : Measurable (ofAtoms : (Fin n → E) → FiniteMeasure E) := by
  apply Measurable.subtype_mk
  exact Finset.measurable_fun_sum _ (fun i _ ↦
    Measure.measurable_dirac.comp (measurable_pi_apply i))

theorem measurable_atomCount {n : ℕ} {A : Set E} (hA : MeasurableSet A) :
    Measurable (fun x : Fin n → E ↦ atomCount x A) := by
  classical
  have he : (fun x : Fin n → E ↦ atomCount x A) =
      fun x ↦ ∑ i : Fin n, A.indicator (fun _ ↦ (1 : ℕ)) (x i) := by
    funext x
    simp [atomCount, Set.indicator_apply]
  rw [he]
  exact Finset.measurable_fun_sum _ (fun i _ ↦
    (measurable_const.indicator hA).comp (measurable_pi_apply i))

/-- A finite partition encoded by an actual labelling function. -/
def partitionCounts {n d : ℕ} (x : Fin n → E) (p : E → Fin d) : Fin d → ℕ :=
  fun i ↦ atomCount x {z | p z = i}

theorem measurable_partitionCounts {n d : ℕ} {p : E → Fin d} (hp : Measurable p) :
    Measurable (fun x : Fin n → E ↦ partitionCounts x p) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_atomCount (hp (measurableSet_singleton i))

omit [MeasurableSpace E] in
/-- Summing finite partition counts recovers the literal list length. -/
theorem partitionCounts_sum {n d : ℕ} (x : Fin n → E) (p : E → Fin d) :
    (∑ i, partitionCounts x p i) = n := by
  classical
  simpa [partitionCounts, atomCount] using
    Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ (fun j ↦ p (x j))

/-- Integration of a partition step function is exactly the finite
linear combination of its actual cell counts. -/
theorem partition_integral [MeasurableSingletonClass E] {n d : ℕ}
    (x : Fin n → E) (p : E → Fin d) (c : Fin d → ℝ) :
    (∫ z, c (p z) ∂(ofAtoms x : Measure E)) =
      ∑ i, c i * (partitionCounts x p i : ℝ) := by
  classical
  rw [ofAtoms_integral]
  simp_rw [partitionCounts, atomCount, Finset.natCast_card_filter,
    Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- A uniform approximation on the actual atoms gives a scale-matched
integration error. It is a deterministic estimate, not a convergence
interface for point-process laws. -/
theorem partition_integral_error [MeasurableSingletonClass E] {n d : ℕ}
    (x : Fin n → E) (p : E → Fin d) (c : Fin d → ℝ) (f : E → ℝ)
    (ε : ℝ) (happrox : ∀ j, |f (x j) - c (p (x j))| ≤ ε) :
    |(∫ z, f z ∂(ofAtoms x : Measure E)) -
      ∑ i, c i * (partitionCounts x p i : ℝ)| ≤ (n : ℝ) * ε := by
  rw [← partition_integral x p c, ofAtoms_integral, ofAtoms_integral,
    ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun j _ ↦ happrox j)).trans_eq (by simp))

variable [TopologicalSpace E] [OpensMeasurableSpace E]

/-- Continuity into the actual weak topology, proved by the integral
criterion and the continuity of the individual atoms. -/
theorem continuous_ofAtoms (n : ℕ) :
    Continuous (ofAtoms : (Fin n → E) → FiniteMeasure E) := by
  rw [FiniteMeasure.continuous_iff_forall_continuous_lintegral]
  intro f
  simp only [ofAtoms_toMeasure, lintegral_finsetSum_measure]
  have hf : Measurable (fun z ↦ (f z : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable
  simp_rw [lintegral_dirac' _ hf]
  exact continuous_finsetSum _ (fun i _ ↦
    (ENNReal.continuous_coe.comp f.continuous).comp (continuous_apply i))

end PerronWright.FiniteAtomicPointMeasure
