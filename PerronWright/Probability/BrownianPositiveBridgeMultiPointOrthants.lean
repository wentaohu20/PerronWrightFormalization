import PerronWright.Probability.BrownianPositiveBridgeMultiPointCoordinates
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Lower orthants determine the full finite-coordinate Borel law

The finite-dimensional law below is determined on the whole product
Borel space, including coupled events, not merely coordinate marginals.
-/

open MeasureTheory Set MeasurableSpace
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000

namespace PerronWright.BrownianPositiveBridgeMultiPointOrthants

open BrownianKilledFiniteDimensionalDensityCoordinates BrownianPositiveBridgeMultiPointCoordinates

theorem real_Ioi_countablySpanning :
    IsCountablySpanning (range (Ioi : ℝ → Set ℝ)) := by
  refine ⟨fun m : ℕ ↦ Ioi (-(m : ℝ)),fun m ↦ ⟨-(m : ℝ),rfl⟩,?_⟩
  ext x
  simp only [mem_iUnion,mem_Ioi,mem_univ,iff_true]
  obtain ⟨m,hm⟩ := exists_nat_gt (-x)
  exact ⟨m,by linarith⟩

theorem orthant_range_eq_boxes (n : ℕ) :
    range (orthant n) = Set.pi univ '' Set.pi univ
      (fun _ : Fin n ↦ range (Ioi : ℝ → Set ℝ)) := by
  ext B
  constructor
  · rintro ⟨cuts,rfl⟩
    refine ⟨fun i ↦ Ioi (cuts i),?_,?_⟩
    · intro i _
      exact ⟨cuts i,rfl⟩
    · ext v
      simp [orthant,Set.mem_pi]
  · rintro ⟨sets,hsets,rfl⟩
    have hc : ∀ i : Fin n, ∃ c : ℝ, Ioi c = sets i := fun i ↦ hsets i (mem_univ i)
    choose cuts hcuts using hc
    refine ⟨cuts,?_⟩
    ext v
    simp only [orthant,mem_ofPred_eq,Set.mem_pi,mem_univ,true_implies,← hcuts,mem_Ioi]

theorem orthant_isPiSystem (n : ℕ) : IsPiSystem (range (orthant n)) := by
  rw [orthant_range_eq_boxes]
  exact IsPiSystem.pi (fun _ ↦ isPiSystem_Ioi)

theorem orthant_countablySpanning (n : ℕ) : IsCountablySpanning (range (orthant n)) := by
  rw [orthant_range_eq_boxes]
  exact IsCountablySpanning.pi (fun _ ↦ real_Ioi_countablySpanning)

theorem orthant_generateFrom (n : ℕ) :
    (inferInstance : MeasurableSpace (FreeVector n)) = generateFrom (range (orthant n)) := by
  rw [orthant_range_eq_boxes]
  exact (generateFrom_eq_pi (fun _ : Fin n ↦ (borel_eq_generateFrom_Ioi ℝ).symm)
    (fun _ ↦ real_Ioi_countablySpanning)).symm

theorem measure_eq_of_orthants (n : ℕ) (μ ν : Measure (FreeVector n)) [IsFiniteMeasure μ]
    (h : ∀ cuts : FreeVector n, μ (orthant n cuts) = ν (orthant n cuts)) : μ = ν := by
  obtain ⟨cover,hmem,hcover⟩ := orthant_countablySpanning n
  apply Measure.ext_of_generateFrom_of_iUnion (range (orthant n)) cover
    (orthant_generateFrom n) (orthant_isPiSystem n) hcover hmem
  · intro m
    exact measure_ne_top μ _
  · rintro B ⟨cuts,rfl⟩
    exact h cuts

end PerronWright.BrownianPositiveBridgeMultiPointOrthants
