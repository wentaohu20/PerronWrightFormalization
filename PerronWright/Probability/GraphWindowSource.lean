import PerronWright.Probability.ComponentWindowFactorialCounts
import PerronWright.Probability.CompactWindowCountLaw
import PerronWright.Probability.CriticalFloorCells
import Mathlib.MeasureTheory.Function.Floor

/-! # Exact window identities for arbitrary actual finite graph laws

The source is a probability measure on literal graphs with `n+1` vertices.
These are exact counting and integration identities, independent of any
criticality, moment limit, or target process assumption.
-/

open MeasureTheory Filter Topology
open scoped Real BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GraphWindowSource

open ComponentWindowPointMeasures ComponentWindowFactorialCounts
open FinitePointMeasureCompact CriticalFloorCells

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]

def windowLaw (a b : ℝ) (R n : ℕ) :
    ProbabilityMeasure (PointMeasure (SurplusWindow a b R)) :=
  ⟨(ρ n).map (windowPointMeasure a b R 1),
    Measure.isProbabilityMeasure_map
      (measurable_windowPointMeasure a b R 1 (n+1)).aemeasurable⟩

@[simp] theorem windowLaw_toMeasure (a b : ℝ) (R n : ℕ) :
    (windowLaw ρ a b R n : Measure (PointMeasure (SurplusWindow a b R))) =
      (ρ n).map (windowPointMeasure a b R 1) := rfl

theorem windowLaw_integrable (a b : ℝ) (R n : ℕ)
    {f : PointMeasure (SurplusWindow a b R) → ℝ} (hf : Measurable f) :
    Integrable f (windowLaw ρ a b R n :
      Measure (PointMeasure (SurplusWindow a b R))) := by
  rw [windowLaw_toMeasure]
  exact (integrable_map_measure hf.aestronglyMeasurable
    (measurable_windowPointMeasure a b R 1 (n+1)).aemeasurable).mpr Integrable.of_finite

theorem windowLaw_integral (a b : ℝ) (R n : ℕ)
    {f : PointMeasure (SurplusWindow a b R) → ℝ} (hf : Measurable f) :
    (∫ η, f η ∂(windowLaw ρ a b R n :
      Measure (PointMeasure (SurplusWindow a b R)))) =
      ∫ G, f (windowPointMeasure a b R 1 G) ∂ρ n := by
  rw [windowLaw_toMeasure]
  exact integral_map (measurable_windowPointMeasure a b R 1 (n+1)).aemeasurable
    hf.aestronglyMeasurable

def localExpectation {q : ℕ} (n : ℕ) (y : Fin q → ℝ) (r : Fin q → ℕ) : ℝ :=
  ((n+1 : ℕ) : ℝ) ^ (2*(q : ℝ)/3) *
    ∫ G, (ComponentCounts.count G (fun i ↦ CriticalScaling.size (y i) (n+1)) r : ℝ) ∂ρ n

omit [∀ n, IsProbabilityMeasure (ρ n)] in
theorem measurable_localExpectation {q : ℕ} (n : ℕ) (r : Fin q → ℕ) :
    Measurable (fun y : Fin q → ℝ ↦ localExpectation ρ n y r) := by
  let E : (Fin q → ℕ) → ℝ := fun k ↦ ((n+1 : ℕ) : ℝ)^(2*(q : ℝ)/3) *
    ∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n
  have hsize : Measurable (fun y : Fin q → ℝ ↦
      fun i ↦ CriticalScaling.size (y i) (n+1)) := by
    apply measurable_pi_lambda
    intro i
    change Measurable (fun y : Fin q → ℝ ↦ ⌊y i * ((n+1 : ℕ) : ℝ)^(2/3 : ℝ)⌋₊)
    have hc : Measurable (fun y : Fin q → ℝ ↦ y i) := measurable_pi_apply i
    exact (hc.mul_const (((n+1 : ℕ) : ℝ)^(2/3 : ℝ))).nat_floor
  exact (measurable_of_countable E).comp hsize

omit [∀ n, IsProbabilityMeasure (ρ n)] in
theorem localExpectation_eq_on_cell {n q : ℕ} (k r : Fin q → ℕ)
    {x : Fin q → ℝ} (hx : x ∈ cell (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) k) :
    localExpectation ρ n x r = ((n+1 : ℕ) : ℝ)^(2*(q : ℝ)/3) *
      ∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n := by
  have he := floor_eq_on_cell
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) _) k hx
  simp only [localExpectation, CriticalScaling.size, he]

omit [∀ n, IsProbabilityMeasure (ρ n)] in
theorem integrableOn_localExpectation_cell {n q : ℕ} (k r : Fin q → ℕ) :
    IntegrableOn (fun x ↦ localExpectation ρ n x r)
      (cell (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) k) volume := by
  let : IsFiniteMeasure (volume.restrict (cell (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) k)) :=
    isFiniteMeasure_restrict_cell _ k
  apply (integrable_const (((n+1 : ℕ) : ℝ)^(2*(q : ℝ)/3) *
    ∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n)).congr
  filter_upwards [ae_restrict_mem (measurableSet_cell _ k)] with x hx
  exact (localExpectation_eq_on_cell ρ k r hx).symm

omit [∀ n, IsProbabilityMeasure (ρ n)] in
theorem integral_localExpectation_cell {n q : ℕ} (k r : Fin q → ℕ) :
    (∫ x in cell (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) k, localExpectation ρ n x r) =
      ∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n := by
  calc
    _ = ∫ _x in cell (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) k,
        ((n+1 : ℕ) : ℝ)^(2*(q : ℝ)/3) *
          ∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n :=
      setIntegral_congr_fun (measurableSet_cell _ k)
        (fun _ hx ↦ localExpectation_eq_on_cell ρ k r hx)
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def,
        critical_cell_volume_toReal (Nat.succ_pos n)]
      have hp := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n))
        (2*(q : ℝ)/3)).ne'
      field_simp

omit [∀ n, IsProbabilityMeasure (ρ n)] in
theorem integral_localExpectation_grid {n q : ℕ}
    (A : Finset (Fin q → ℕ)) (r : Fin q → ℕ) :
    (∫ x in ⋃ k ∈ A, cell (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) k,
      localExpectation ρ n x r) =
      ∑ k ∈ A, ∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n := by
  rw [integral_biUnion_finset A (fun k _ ↦ measurableSet_cell _ k)
    (fun _ _ _ _ hkl ↦ disjoint_cells
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) _) hkl)
    (fun k _ ↦ integrableOn_localExpectation_cell ρ k r)]
  exact Finset.sum_congr rfl (fun k _ ↦ integral_localExpectation_cell ρ k r)

theorem windowLaw_descFactorial_integrable (a b : ℝ) (R n q : ℕ) :
    Integrable (fun η ↦ ((size η).descFactorial q : ℝ))
      (windowLaw ρ a b R n : Measure (PointMeasure (SurplusWindow a b R))) :=
  windowLaw_integrable ρ a b R n
    ((measurable_of_countable (fun m : ℕ ↦ (m.descFactorial q : ℝ))).comp measurable_size)

theorem windowLaw_descFactorial_expectation_eq_sum
    (a b : ℝ) (hb : 0 ≤ b) (R n q : ℕ) :
    (∫ η, ((size η).descFactorial q : ℝ) ∂(windowLaw ρ a b R n :
      Measure (PointMeasure (SurplusWindow a b R)))) =
      ∑ r ∈ surplusIndices q R,
        ∑ k ∈ integerWindow (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) (fun _ ↦ a) (fun _ ↦ b),
          (∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n) := by
  have hm : Measurable (fun η : PointMeasure (SurplusWindow a b R) ↦
      ((size η).descFactorial q : ℝ)) :=
    (measurable_of_countable (fun m : ℕ ↦ (m.descFactorial q : ℝ))).comp measurable_size
  rw [windowLaw_integral ρ a b R n hm]
  simp_rw [window_size_descFactorial_eq_sum _ (Nat.succ_pos n) a b hb R, Nat.cast_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    exact integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)
  · intro _ _
    exact Integrable.of_finite

def actualCountLaw (a b : ℝ) (R n : ℕ) : ProbabilityMeasure (Fin 1 → ℕ) :=
  CompactWindowCountLaw.countLaw (windowLaw ρ a b R n)

theorem actualCountLaw_factorial_integrable (a b : ℝ) (R n : ℕ) (q : Fin 1 → ℕ) :
    Integrable (FactorialCountDeterminacy.factorialPolynomial q)
      (actualCountLaw ρ a b R n : Measure (Fin 1 → ℕ)) := by
  unfold actualCountLaw CompactWindowCountLaw.countLaw
  rw [ProbabilityMeasure.toMeasure_map]
  apply (integrable_map_measure
    (measurable_of_countable (FactorialCountDeterminacy.factorialPolynomial q)).aestronglyMeasurable
    CompactWindowCountLaw.continuous_countVector.measurable.aemeasurable).mpr
  change Integrable (fun η ↦ FactorialCountDeterminacy.factorialPolynomial q
    (CompactWindowCountLaw.countVector η))
    (windowLaw ρ a b R n : Measure (PointMeasure (SurplusWindow a b R)))
  simpa only [Function.comp_apply, CompactWindowCountLaw.factorialPolynomial_countVector] using
    windowLaw_descFactorial_integrable ρ a b R n (q 0)

theorem actualCountLaw_factorialMoment (a b : ℝ) (R n : ℕ) (q : Fin 1 → ℕ) :
    FactorialCountDeterminacy.factorialMoment
      (actualCountLaw ρ a b R n : Measure (Fin 1 → ℕ)) q =
      ∫ η, ((size η).descFactorial (q 0) : ℝ)
        ∂(windowLaw ρ a b R n : Measure (PointMeasure (SurplusWindow a b R))) := by
  unfold FactorialCountDeterminacy.factorialMoment actualCountLaw CompactWindowCountLaw.countLaw
  rw [ProbabilityMeasure.toMeasure_map, integral_map
    CompactWindowCountLaw.continuous_countVector.measurable.aemeasurable
    (measurable_of_countable (FactorialCountDeterminacy.factorialPolynomial q)).aestronglyMeasurable]
  simp only [CompactWindowCountLaw.factorialPolynomial_countVector]

theorem windowLaw_mass_integrable (a b : ℝ) (R n : ℕ) :
    Integrable (fun η ↦ (mass η : ℝ))
      (windowLaw ρ a b R n : Measure (PointMeasure (SurplusWindow a b R))) :=
  windowLaw_integrable ρ a b R n
    (NNReal.continuous_coe.measurable.comp measurable_mass)

end PerronWright.GraphWindowSource
