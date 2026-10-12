import PerronWright.Probability.PointProcessNormalization
import PerronWright.Probability.FactorialDensityNormalization
import PerronWright.Model.FiniteIrreduciblePerronQuantities

/-! # Literal finite irreducible starred normalization

The positive size scale is the cube root of the actual finite Perron
cubic quantity. The critical parameter and q-dimensional Jacobian are
proved exactly. The graph measures below are literal component Dirac
sums with the actual empirical type probability marks left unchanged.
No Brownian identity or regular-critical adapter is used.
-/

open MeasureTheory
open scoped BigOperators Classical Real
noncomputable section

namespace PerronWright.FiniteIrreduciblePointProcessNormalization

open ComponentCounts EmpiricalTypeMarks
open ComponentPointProcesses (sizeRescale sizeRescale_measurable markedSizeRescale
  markedSizeRescale_measurable unmarked marked atom markedAtom)

variable {S : Type*} [Fintype S] [DecidableEq S]

def sizeScale (M : FiniteIrreducibleModel S) (hM : M.IsCritical) : ℝ :=
  M.beta hM ^ (1/3 : ℝ)

theorem sizeScale_pos (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    0 < sizeScale M hM := Real.rpow_pos_of_pos (M.beta_pos hM) _

theorem sizeScale_cube (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    sizeScale M hM ^ (3 : ℕ) = M.beta hM :=
  FactorialDensity.beta_cubeRoot_cube (M.beta_pos hM)

theorem sizeScale_square (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    sizeScale M hM ^ (2 : ℕ) = M.beta hM ^ (2/3 : ℝ) :=
  FactorialDensity.beta_cubeRoot_square (M.beta_pos hM)

/-- This is the paper's numeric parameter, not a Brownian law assertion. -/
def paperParameter (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (lambda : ℝ) : ℝ :=
  M.alpha hM * M.beta hM ^ (-2/3 : ℝ) * lambda

theorem paperParameter_eq_div_scale_square (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) :
    paperParameter M hM lambda = M.alpha hM * lambda / sizeScale M hM ^ (2 : ℕ) := by
  rw [sizeScale_square]
  unfold paperParameter
  have he : (-2/3 : ℝ) = -(2/3 : ℝ) := by ring
  rw [he,Real.rpow_neg (M.beta_pos hM).le,div_eq_mul_inv]
  ring

/-- The literal factorial density becomes the unit-(alpha,beta) density
in starred coordinates, including the inverse q-dimensional Jacobian. -/
theorem density_normalized_eq_unit_density (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) {q : ℕ} (y : Fin q → ℝ) (r : Fin q → ℕ)
    (hy : ∀ i, 0 < y i) :
    (sizeScale M hM)⁻¹ ^ q * FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r =
      FactorialDensity.density 1 1 (paperParameter M hM lambda)
        (fun i ↦ sizeScale M hM * y i) r :=
  FactorialDensity.density_starred_normalization (M.alpha hM) lambda (M.beta_pos hM) y r hy

def unmarkedStar (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (G : SimpleGraph (Fin n)) : Measure (ℝ × ℕ) :=
  (unmarked G).map (sizeRescale (sizeScale M hM))

theorem unmarkedStar_eq_sum (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    unmarkedStar M hM G = ∑ C : G.ConnectedComponent,
      Measure.dirac (sizeScale M hM * (componentSize C : ℝ) /
        (n : ℝ) ^ (2/3 : ℝ), componentSurplus C) := by
  unfold unmarkedStar unmarked
  rw [Measure.map_finset_sum' (sizeRescale_measurable _).aemeasurable]
  simp only [Measure.map_dirac' (sizeRescale_measurable _),sizeRescale,atom,mul_div_assoc]

variable [MeasurableSpace S]

def markedStar (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → S) :
    Measure ((ℝ × ℕ) × ProbabilityMeasure S) :=
  (marked G x).map (markedSizeRescale (sizeScale M hM))

theorem markedStar_eq_sum (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → S) :
    markedStar M hM G x = ∑ C : G.ConnectedComponent,
      Measure.dirac ((sizeScale M hM * (componentSize C : ℝ) /
        (n : ℝ) ^ (2/3 : ℝ),componentSurplus C),componentMark x C) := by
  unfold markedStar marked
  rw [Measure.map_finset_sum' (markedSizeRescale_measurable _).aemeasurable]
  simp only [Measure.map_dirac' (markedSizeRescale_measurable _),
    markedSizeRescale,sizeRescale,markedAtom,atom,mul_div_assoc]

end PerronWright.FiniteIrreduciblePointProcessNormalization
