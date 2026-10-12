import PerronWright.Probability.FreshTypeCumulantExpansion

/-!
# Actual selected residual: finite-n cumulant and present-edge bounds

The selected residual is the literal observable in the exact annealed
factorial-expectation formula.  Its logarithm is computed from its defining
positive factors; the analytic error below is derived from the model bound.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedResidualCumulantExpansion

open AnnealedGraph FreshTypeAveraging FreshTypeCumulantExpansion ComponentBlocks ExactFactorialExpectation
  SelectedConfiguration AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
  AnnealedResidualFixedBlock AnnealedTupleResidualConnectedLawGraphTuple
  AnnealedTupleResidualConnectedLawWeights AnnealedTupleResidualConnectedLawCoordinates

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

theorem edgeFactor_le_kernelBound (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t)
    {n : ℕ} (x : Fin n → S) (e : Sym2 (Fin n)) :
    M.edgeFactor t x e ≤ t * ‖M.kernel.toContinuousMap‖ := by
  induction e using Sym2.inductionOn with
  | _ i j =>
    simp only [CompactBJRModel.edgeFactor_mk]
    exact mul_le_mul_of_nonneg_left ((le_abs_self (M.kernel (x i) (x j))).trans
      (M.kernel.toContinuousMap.norm_coe_le_norm (x i,x j))) ht

def oddsCorrection {n : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (x : Fin n → S) (H : SimpleGraph (Fin n)) : ℝ :=
  ∏ e ∈ H.edgeFinset, normalizedOdds (M.edgeFactor t x e / (n : ℝ))

theorem oddsCorrection_pos {n : ℕ} (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t)
    (x : Fin n → S) (H : SimpleGraph (Fin n)) : 0 < oddsCorrection M t x H := by
  apply Finset.prod_pos
  intro e _
  exact normalizedOdds_pos (div_nonneg (M.edgeFactor_nonneg t ht x e) (Nat.cast_nonneg n))

/-- The exact present-edge correction is controlled even when some kernel
values vanish. -/
theorem log_oddsCorrection_bounds {n : ℕ} (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t)
    (x : Fin n → S) (H : SimpleGraph (Fin n)) :
    0 ≤ Real.log (oddsCorrection M t x H) ∧
      Real.log (oddsCorrection M t x H) ≤
        t * ‖M.kernel.toContinuousMap‖ * (H.edgeFinset.card : ℝ) / (n : ℝ) := by
  unfold oddsCorrection
  have hz (e : Sym2 (Fin n)) : 0 ≤ M.edgeFactor t x e / (n : ℝ) :=
    div_nonneg (M.edgeFactor_nonneg t ht x e) (Nat.cast_nonneg n)
  rw [Real.log_prod (fun e _ ↦ (normalizedOdds_pos (hz e)).ne')]
  constructor
  · exact Finset.sum_nonneg (fun e _ ↦ (log_normalizedOdds_bounds (hz e)).1)
  · calc
      _ ≤ ∑ e ∈ H.edgeFinset, M.edgeFactor t x e / (n : ℝ) :=
        Finset.sum_le_sum (fun e _ ↦ (log_normalizedOdds_bounds (hz e)).2)
      _ ≤ ∑ _e ∈ H.edgeFinset, t * ‖M.kernel.toContinuousMap‖ / (n : ℝ) := by
        apply Finset.sum_le_sum
        intro e _
        exact div_le_div_of_nonneg_right (edgeFactor_le_kernelBound M t ht x e) (Nat.cast_nonneg n)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

def freshCumulantPolynomial {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (t : ℝ) (n : ℕ) (x : I → S) : ℝ :=
  -(t / (n : ℝ)) * totalDegree M x + (t / (n : ℝ)) ^ 2 * exposureVariance M x / 2 -
    (t / (n : ℝ)) ^ 3 * exposureThirdCumulant M x / 6

def selectedCumulantExponent {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) (s₀ : S) : ℝ :=
  t * totalDegree M u - t *
    internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀ / (n : ℝ) +
      ((n - ∑ i, k i : ℕ) : ℝ) * freshCumulantPolynomial M t n u

def selectedErrorBound {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) : ℝ :=
  9 * ((n - ∑ i, k i : ℕ) : ℝ) *
      (t * exposureBound (I := ↥(selectedUnion (blocksOfPlacement hk f))) M / (n : ℝ)) ^ 4 +
    t * ‖M.kernel.toContinuousMap‖ * ((tupleGraph f H).edgeFinset.card : ℝ) / (n : ℝ)

theorem selectedResidual_pos {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) (s₀ : S) :
    0 < selectedResidual M t hk f H u s₀ := by
  unfold selectedResidual
  exact mul_pos (mul_pos (Real.exp_pos _) (pow_pos (isolationFactor_pos M t n u) _))
    (oddsCorrection_pos M t ht (combineTypes _ u (fun _ ↦ s₀)) (tupleGraph f H))

/-- Exact logarithm of the actual annealed residual observable. -/
theorem log_selectedResidual {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) (s₀ : S) :
    Real.log (selectedResidual M t hk f H u s₀) =
      t * totalDegree M u - t *
        internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀ / (n : ℝ) +
          ((n - ∑ i, k i : ℕ) : ℝ) * Real.log (isolationFactor M t n u) +
            Real.log (oddsCorrection M t (combineTypes _ u (fun _ ↦ s₀)) (tupleGraph f H)) := by
  have hA := isolationFactor_pos M t n u
  have hO := oddsCorrection_pos M t ht (combineTypes _ u (fun _ ↦ s₀)) (tupleGraph f H)
  change Real.log ((Real.exp _ * isolationFactor M t n u ^ (n-∑ i,k i)) *
    oddsCorrection M t (combineTypes _ u (fun _ ↦ s₀)) (tupleGraph f H)) = _
  rw [Real.log_mul (mul_pos (Real.exp_pos _) (pow_pos hA _)).ne' hO.ne',
    Real.log_mul (Real.exp_pos _).ne' (pow_pos hA _).ne',Real.log_exp,Real.log_pow]

/-- Proved uniform finite-n error for the literal selected residual. -/
theorem log_selectedResidual_cumulant_bound {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) (s₀ : S)
    (hsmall : t * exposureBound (I := ↥(selectedUnion (blocksOfPlacement hk f))) M /
      (n : ℝ) ≤ 1 / 2) :
    |Real.log (selectedResidual M t hk f H u s₀) - selectedCumulantExponent M t hk f u s₀| ≤
      selectedErrorBound M t hk f H := by
  have hF := log_isolationFactor_cumulant_bound M t ht n u hsmall
  have he : Real.log (isolationFactor M t n u) + (t/(n:ℝ))*totalDegree M u -
      (t/(n:ℝ))^2*exposureVariance M u/2 + (t/(n:ℝ))^3*exposureThirdCumulant M u/6 =
        Real.log (isolationFactor M t n u) - freshCumulantPolynomial M t n u := by
    unfold freshCumulantPolynomial
    ring
  rw [he] at hF
  have hO := log_oddsCorrection_bounds M t ht (combineTypes _ u (fun _ ↦ s₀)) (tupleGraph f H)
  rw [log_selectedResidual M t ht hk f H u s₀]
  unfold selectedCumulantExponent selectedErrorBound
  have he' : t * totalDegree M u - t * internalPairWeightOn M _ u s₀ / (n:ℝ) +
      ((n-∑ i,k i:ℕ):ℝ) * Real.log (isolationFactor M t n u) +
      Real.log (oddsCorrection M t (combineTypes _ u (fun _ ↦ s₀)) (tupleGraph f H)) -
      (t * totalDegree M u - t * internalPairWeightOn M _ u s₀ / (n:ℝ) +
        ((n-∑ i,k i:ℕ):ℝ) * freshCumulantPolynomial M t n u) =
    ((n-∑ i,k i:ℕ):ℝ) * (Real.log (isolationFactor M t n u) - freshCumulantPolynomial M t n u) +
      Real.log (oddsCorrection M t (combineTypes _ u (fun _ ↦ s₀)) (tupleGraph f H)) := by ring
  rw [he']
  calc
    _ ≤ |((n-∑ i,k i:ℕ):ℝ) * (Real.log (isolationFactor M t n u) - freshCumulantPolynomial M t n u)| +
      |Real.log (oddsCorrection M t (combineTypes _ u (fun _ ↦ s₀)) (tupleGraph f H))| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg hO.1]
      have h := mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg (n-∑ i,k i) : (0:ℝ) ≤ _)
      nlinarith only [h,hO.2]

/-- The true selected residual is sandwiched by the cumulant exponential
times a proved, deterministic error envelope. -/
theorem selectedResidual_cumulant_sandwich {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) (s₀ : S)
    (hsmall : t * exposureBound (I := ↥(selectedUnion (blocksOfPlacement hk f))) M /
      (n : ℝ) ≤ 1 / 2) :
    Real.exp (-selectedErrorBound M t hk f H) * Real.exp (selectedCumulantExponent M t hk f u s₀) ≤
      selectedResidual M t hk f H u s₀ ∧
    selectedResidual M t hk f H u s₀ ≤
      Real.exp (selectedErrorBound M t hk f H) * Real.exp (selectedCumulantExponent M t hk f u s₀) := by
  have h := abs_le.mp (log_selectedResidual_cumulant_bound M t ht hk f H u s₀ hsmall)
  have hp := selectedResidual_pos M t ht hk f H u s₀
  constructor
  · rw [← Real.exp_add,← Real.exp_log hp]
    exact Real.exp_le_exp.mpr (by linarith only [h.1])
  · rw [← Real.exp_add,← Real.exp_log hp]
    exact Real.exp_le_exp.mpr (by linarith only [h.2])

end PerronWright.AnnealedResidualCumulantExpansion
