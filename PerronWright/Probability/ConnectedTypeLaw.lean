import PerronWright.Probability.AnnealedTypedGraph
import PerronWright.Model.PerronQuantities

/-!
# The weighted connected type law and its exact Laplace transform

This is the connected-graph sampling law used by the paper's profile
estimates, not the random graph law itself.  Its normalizer is the literal
connected enumerator.  The field-tilting identity is proved from the
integrands, rather than supplied as an interface.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ConnectedTypeLaw

open AnnealedGraph

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The literal sampled types and the connected labelled graph. -/
abbrev State (S : Type*) (k : ℕ) := (Fin k → S) × SimpleGraph (Fin k)

/-- The fixed-surplus graph predicate used by the enumerator. -/
def Eligible {k : ℕ} (r : ℕ) (H : SimpleGraph (Fin k)) : Prop :=
  H.Connected ∧ H.edgeFinset.card = k + r - 1

/-- Unnormalized density of the connected type law at real field `g`. -/
def weight (M : CompactBJRModel S) (g : C(S, ℝ)) (k r : ℕ)
    (p : State S k) : ℝ :=
  if Eligible r p.2 then M.fieldGraphWeightIntegrand g p.2 p.1 else 0

theorem weight_nonneg (M : CompactBJRModel S) (g : C(S, ℝ)) (k r : ℕ)
    (p : State S k) : 0 ≤ weight M g k r p := by
  unfold weight
  split_ifs
  · exact M.fieldGraphWeightIntegrand_nonneg g p.2 p.1
  · exact le_rfl

theorem weight_continuous_slice (M : CompactBJRModel S) (g : C(S, ℝ)) (k r : ℕ)
    (H : SimpleGraph (Fin k)) : Continuous (fun x ↦ weight M g k r (x, H)) := by
  by_cases h : Eligible r H
  · simpa only [weight, if_pos h] using M.fieldGraphWeightIntegrand_continuous g H
  · simpa only [weight, if_neg h] using
      (continuous_const : Continuous (fun _ : Fin k → S ↦ (0 : ℝ)))

theorem weight_measurable (M : CompactBJRModel S) (g : C(S, ℝ)) (k r : ℕ) :
    Measurable (weight M g k r) :=
  measurable_from_prod_countable_left
    (fun H ↦ (weight_continuous_slice M g k r H).measurable)

theorem weight_integrable (M : CompactBJRModel S) (g : C(S, ℝ)) (k r : ℕ) :
    Integrable (weight M g k r) ((typeLaw M k).prod Measure.count) := by
  apply (integrable_prod_iff' (weight_measurable M g k r).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun H ↦ ?_), Integrable.of_finite⟩
  exact (weight_continuous_slice M g k r H).integrable_of_hasCompactSupport
    isClosed_closure.isCompact

/-- The total unnormalized mass is exactly the connected enumerator. -/
theorem integral_weight (M : CompactBJRModel S) (g : C(S, ℝ)) (k r : ℕ) :
    (∫ p, weight M g k r p ∂(typeLaw M k).prod Measure.count) =
      M.fieldConnectedWeight g k r := by
  rw [integral_prod _ (weight_integrable M g k r)]
  simp only [integral_count]
  rw [integral_finsetSum]
  · unfold CompactBJRModel.fieldConnectedWeight
    apply Finset.sum_congr rfl
    intro H _
    unfold weight Eligible
    split_ifs <;> simp [CompactBJRModel.fieldGraphWeight, typeLaw]
  · intro H _
    exact (weight_continuous_slice M g k r H).integrable_of_hasCompactSupport
      isClosed_closure.isCompact

/-- The normalized connected type law, defined whenever its literal
enumerator is positive.  Eventual positivity is proved below. -/
def law (M : CompactBJRModel S) (g : C(S, ℝ)) (k r : ℕ)
    (_hC : 0 < M.fieldConnectedWeight g k r) : Measure (State S k) :=
  ((typeLaw M k).prod Measure.count).withDensity
    (fun p ↦ ENNReal.ofReal (weight M g k r p / M.fieldConnectedWeight g k r))

instance law_isProbability (M : CompactBJRModel S) (g : C(S, ℝ)) (k r : ℕ)
    (hC : 0 < M.fieldConnectedWeight g k r) : IsProbabilityMeasure (law M g k r hC) := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hI := (weight_integrable M g k r).div_const (M.fieldConnectedWeight g k r)
  have hn : ∀ p, 0 ≤ weight M g k r p / M.fieldConnectedWeight g k r :=
    fun p ↦ div_nonneg (weight_nonneg M g k r p) hC.le
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall hn)]
  rw [integral_div, integral_weight, div_self hC.ne']
  simp

/-- A test field evaluated on the empirical type sum. -/
def typeSum {k : ℕ} (f : C(S, ℝ)) (x : Fin k → S) : ℝ := ∑ i, f (x i)

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
theorem typeSum_continuous {k : ℕ} (f : C(S, ℝ)) :
    Continuous (typeSum (k := k) f) :=
  continuous_finsetSum _ (fun i _ ↦ f.continuous.comp (continuous_apply i))

/-- Tilting the sampled type sum is exactly addition of the enumerating field. -/
theorem weight_tilt (M : CompactBJRModel S) (g f : C(S, ℝ)) (k r : ℕ)
    (p : State S k) :
    weight M g k r p * Real.exp (typeSum f p.1) = weight M (g + f) k r p := by
  unfold weight
  split_ifs
  · unfold CompactBJRModel.fieldGraphWeightIntegrand typeSum
    have he (i : Fin k) :
        Real.exp ((g + f) (p.1 i) - M.degreeFunction (p.1 i)) =
          Real.exp (g (p.1 i) - M.degreeFunction (p.1 i)) * Real.exp (f (p.1 i)) := by
      rw [← Real.exp_add]
      congr 1
      simp only [ContinuousMap.add_apply]
      ring
    simp_rw [he]
    rw [Finset.prod_mul_distrib, Real.exp_sum]
    ring
  · simp

/-- Exact Laplace transform of the connected type sum. -/
theorem laplace_eq_enumerator_ratio (M : CompactBJRModel S)
    (g f : C(S, ℝ)) (k r : ℕ) (hC : 0 < M.fieldConnectedWeight g k r) :
    (∫ p, Real.exp (typeSum f p.1) ∂law M g k r hC) =
      M.fieldConnectedWeight (g + f) k r / M.fieldConnectedWeight g k r := by
  have hd : Measurable (fun p : State S k ↦
      ENNReal.ofReal (weight M g k r p / M.fieldConnectedWeight g k r)) :=
    ENNReal.measurable_ofReal.comp ((weight_measurable M g k r).div_const _)
  unfold law
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  have he (p : State S k) :
      (ENNReal.ofReal (weight M g k r p / M.fieldConnectedWeight g k r)).toReal *
          Real.exp (typeSum f p.1) =
        weight M (g + f) k r p / M.fieldConnectedWeight g k r := by
    rw [ENNReal.toReal_ofReal (div_nonneg (weight_nonneg M g k r p) hC.le)]
    rw [div_mul_eq_mul_div, weight_tilt]
  simp_rw [smul_eq_mul, he]
  rw [integral_div, integral_weight]

/-- Centering at the Perron law simply extracts the deterministic exponential. -/
theorem centered_laplace_eq_enumerator_ratio (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (g f : C(S, ℝ)) (k r : ℕ)
    (hC : 0 < M.fieldConnectedWeight g k r) :
    (∫ p, Real.exp (typeSum f p.1 - (k : ℝ) * ∫ y, f y ∂M.perronLaw hM)
      ∂law M g k r hC) =
      Real.exp (-(k : ℝ) * ∫ y, f y ∂M.perronLaw hM) *
        (M.fieldConnectedWeight (g + f) k r / M.fieldConnectedWeight g k r) := by
  simp_rw [Real.exp_sub, div_eq_mul_inv]
  rw [integral_mul_const, laplace_eq_enumerator_ratio]
  have hn : -(k : ℝ) * (∫ y, f y ∂M.perronLaw hM) =
      -((k : ℝ) * ∫ y, f y ∂M.perronLaw hM) := by ring
  rw [hn, Real.exp_neg]
  ring

end PerronWright.ConnectedTypeLaw
