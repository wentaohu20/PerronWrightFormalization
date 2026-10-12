import PerronWright.Probability.BrownianBoundaryGreenStateChain
import PerronWright.Probability.BrownianEntranceProductLaplace
import PerronWright.Probability.BrownianGreenInitialDerivativeIntegral

/-! # Actual entrance-product state integral is the initial boundary slope

The full height-weighted state vector is integrated by Tonelli. The
factorial is (n+1)!, since transformedNumerator n has n+1 sampled heights.
The one-height case is included, rather than assumed separately.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceLaplaceStateIntegral

open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFreeEntranceGeometry
open BrownianKilledAreaMomentResolvent BrownianKilledGreenKernel
open BrownianKilledBoundaryInsertionRecurrence BrownianBoundaryGreenStateChain
open BrownianEntranceProductGeometry BrownianEntranceProductLaplace
open BrownianGreenInitialDerivativeIntegral BrownianKilledBoundaryPolynomial

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

theorem transformedNumerator_zero_of_nonpos_coordinate (n : ℕ) (p : ℝ)
    (v : FreeVector (n+1)) (i : Fin (n+1)) (hi : v i ≤ 0) :
    transformedNumerator n p v = 0 := by
  refine Fin.cases ?_ (fun j ↦ ?_) i hi
  · intro h0
    simp only [transformedNumerator,entranceTransform,if_neg (not_lt.mpr h0),zero_mul]
  · intro hj
    have hg : green p (v j.castSucc) (v j.succ) = 0 := by
      rw [green,if_neg (fun h ↦ (not_lt.mpr hj) h.2)]
    have hz : (∏ k : Fin n, green p (v k.castSucc) (v k.succ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hg
    rw [transformedNumerator,hz,mul_zero,zero_mul]

theorem transformedNumerator_heightWeight_eq_ofReal_product (n : ℕ) (p : ℝ)
    (v : FreeVector (n+1)) :
    transformedNumerator n p v*stateHeightWeight (n+1) v =
      transformedNumerator n p v*ENNReal.ofReal (∏ i, v i) := by
  by_cases hnonneg : ∀ i, 0 ≤ v i
  · rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hnonneg i)]
    rfl
  · obtain ⟨i,hi⟩ := not_forall.mp hnonneg
    rw [transformedNumerator_zero_of_nonpos_coordinate n p v i (lt_of_not_ge hi).le,
      zero_mul,zero_mul]

theorem weighted_transformedNumerator_eq_anchored (n : ℕ) (p : ℝ) (hp : 0 < p)
    (v : FreeVector (n+1)) :
    transformedNumerator n p v*stateHeightWeight (n+1) v =
      boundarySlopeNN 0 p (v 0)*ENNReal.ofReal (v 0)*
        anchoredStateChain n p (v 0) (Fin.tail v) := by
  have hw : stateHeightWeight (n+1) v =
      ENNReal.ofReal (v 0)*stateHeightWeight n (Fin.tail v) := by
    simp only [stateHeightWeight,Fin.prod_univ_succ,Fin.tail]
  have hanchor : boundarySlopeNN 0 p (v 0)*ENNReal.ofReal (v 0)*
      anchoredStateChain n p (v 0) (Fin.tail v) =
      boundarySlopeNN 0 p (v 0)*
        (∏ i : Fin n, green p (v i.castSucc) (v i.succ))*
        boundarySlopeNN 0 p (v (Fin.last n))*stateHeightWeight (n+1) v := by
    rw [anchoredStateChain_eq_product,hw]
    simp only [prependInitial,lastState]
    rw [Fin.cons_self_tail]
    simp only [Fin.tail]
    simp_rw [resolvent_zero_eq p hp]
    ac_rfl
  rw [hanchor,transformedNumerator]
  by_cases hpos : ∀ i, 0 < v i
  · rw [entranceTransform,if_pos (hpos 0),entranceTransform,if_pos (hpos (Fin.last n))]
    simp only [boundarySlopeNN]
  · obtain ⟨i,hi⟩ := not_forall.mp hpos
    have hz : stateHeightWeight (n+1) v = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hi))
    rw [hz,mul_zero,mul_zero]

theorem measurable_weighted_transformedNumerator (n : ℕ) (p : ℝ) (hp : 0 < p) :
    Measurable (fun v : FreeVector (n+1) ↦
      transformedNumerator n p v*stateHeightWeight (n+1) v) := by
  have heq : (fun v : FreeVector (n+1) ↦ transformedNumerator n p v*stateHeightWeight (n+1) v) =
      (fun v ↦ boundarySlopeNN 0 p (v 0)*ENNReal.ofReal (v 0)*
        anchoredStateChain n p (v 0) (Fin.tail v)) :=
    funext (weighted_transformedNumerator_eq_anchored n p hp)
  rw [heq]
  have h0 : Measurable (fun v : FreeVector (n+1) ↦ v 0) := measurable_pi_apply 0
  have ht : Measurable (fun v : FreeVector (n+1) ↦ Fin.tail v) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply i.succ
  exact (((measurable_boundarySlopeNN 0 p).comp h0).mul h0.ennreal_ofReal).mul
    ((measurable_anchoredStateChain n p).comp (h0.prodMk ht))

theorem factorial_transformed_stateIntegral_eq_initial_slope
    (n : ℕ) (p : ℝ) (hp : 0 < p) :
    ((n+1).factorial : ℝ≥0∞)*
      (∫⁻ v : FreeVector (n+1), transformedNumerator n p v*stateHeightWeight (n+1) v) =
      ENNReal.ofReal ((boundaryPolynomial (n+1) (Real.sqrt (2*p))).derivative.eval 0) := by
  rw [lintegral_volume_freeCons n (measurable_weighted_transformedNumerator n p hp)]
  simp_rw [weighted_transformedNumerator_eq_anchored n p hp,freeCons,Fin.cons_zero,Fin.tail_cons]
  have hm (z : ℝ) : Measurable (anchoredStateChain n p z) := by
    have hh := (measurable_anchoredStateChain n p).comp
      (show Measurable (fun v : FreeVector n ↦ (z,v)) from
        measurable_const.prodMk measurable_id)
    simpa only [Function.comp_def] using hh
  simp_rw [lintegral_const_mul _ (hm _)]
  rw [Nat.factorial_succ,Nat.cast_mul,mul_assoc]
  have hpull : (n.factorial : ℝ≥0∞)*
      (∫⁻ z : ℝ, (boundarySlopeNN 0 p z*ENNReal.ofReal z)*
        (∫⁻ v : FreeVector n, anchoredStateChain n p z v)) =
      ∫⁻ z : ℝ, boundarySlopeNN 0 p z*ENNReal.ofReal z*boundarySlopeNN n p z := by
    rw [← lintegral_const_mul' _ _ (by simp : (n.factorial : ℝ≥0∞) ≠ ⊤)]
    apply lintegral_congr
    intro z
    calc
      _ = (boundarySlopeNN 0 p z*ENNReal.ofReal z)*
          ((n.factorial : ℝ≥0∞)*(∫⁻ v : FreeVector n, anchoredStateChain n p z v)) := by ac_rfl
      _ = _ := by rw [factorial_stateChain_eq_actual_boundary n p hp z]
  rw [hpull]
  change ((n+1 : ℕ) : ℝ≥0∞)*(∫⁻ z : ℝ,
    ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p)))*ENNReal.ofReal z*boundarySlopeNN n p z) = _
  exact actual_boundary_insertion_lintegral_eq_initial_slope n p hp

theorem factorial_weighted_rawNumerator_laplace_eq_initial_slope
    (n : ℕ) (p : ℝ) (hp : 0 < p) :
    ((n+1).factorial : ℝ≥0∞)*
      (∫⁻ σ in positiveGaps (n+2), PositiveTimeConvolutionLaplace.laplaceWeight p (∑ i, σ i)*
        (∫⁻ v : FreeVector (n+1), rawNumerator n σ v*stateHeightWeight (n+1) v)) =
      ENNReal.ofReal ((boundaryPolynomial (n+1) (Real.sqrt (2*p))).derivative.eval 0) := by
  rw [weighted_rawNumerator_laplace n p hp (measurable_stateHeightWeight (n+1))]
  exact factorial_transformed_stateIntegral_eq_initial_slope n p hp

theorem factorial_transformed_stateIntegral_ofReal_product_eq_initial_slope
    (n : ℕ) (p : ℝ) (hp : 0 < p) :
    ((n+1).factorial : ℝ≥0∞)*
      (∫⁻ v : FreeVector (n+1), transformedNumerator n p v*ENNReal.ofReal (∏ i, v i)) =
      ENNReal.ofReal ((boundaryPolynomial (n+1) (Real.sqrt (2*p))).derivative.eval 0) := by
  simp_rw [← transformedNumerator_heightWeight_eq_ofReal_product n p]
  exact factorial_transformed_stateIntegral_eq_initial_slope n p hp

end PerronWright.BrownianEntranceLaplaceStateIntegral
