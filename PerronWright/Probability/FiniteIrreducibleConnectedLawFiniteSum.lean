import PerronWright.Probability.FiniteIrreducibleConnectedTypeLaw
import PerronWright.Probability.AnnealedTupleResidualConnectedLawCoordinates
import PerronWright.Probability.FiniteIrreducibleTypeFiberSums

/-!
# The actual finite connected-state base measure as a literal finite sum

The existing product type/graph measure is evaluated on actual singleton
states, with mass equal to the product of the positive target atom weights.
Finite fibre products and the pooled labelled type coordinates are proved.
No criticality, periodicity, or profile-limit premise is used.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleConnectedLawFiniteSum

open AnnealedGraph AnnealedTupleResidualCounting
open AnnealedTupleResidualConnectedLawGraphTuple
open AnnealedTupleResidualConnectedLawProduct
open AnnealedTupleResidualConnectedLawCoordinates
open FiniteIrreducibleTypePlacementMultiplicity FiniteIrreducibleTypeFiberSums

/-- Exact product regrouping by actual finite type fibres. -/
theorem prod_by_typeFibers {A S : Type*} [Fintype A] [Fintype S]
    (y : A → S) (F : S → ℝ) :
    (∏ v : A, F (y v)) = ∏ a : S, (F a) ^ fiberCount y a := by
  let e := Equiv.sigmaFiberEquiv y
  calc
    _ = ∏ p : (Σ a : S, {v : A // y v = a}), F (y (e p)) :=
      (e.prod_comp (fun v ↦ F (y v))).symm
    _ = ∏ p : (Σ a : S, {v : A // y v = a}), F p.1 := by
      apply Finset.prod_congr rfl
      intro p _
      change F (y p.2.val) = F p.1
      rw [p.2.property]
    _ = _ := by
      rw [Fintype.prod_sigma]
      simp only [Finset.prod_const, Finset.card_univ, fiberCount]

/-- The actual selected type vector of a dependent component-state tuple. -/
def pooledTypes {S : Type*} {q : ℕ} {k : Fin q → ℕ}
    (p : TupleState S k) (v : SelectedVertices k) : S := (p v.1).1 v.2

/-- Genuine finite coordinate bijection, including zero component sizes. -/
def stateTupleEquivTypesGraphs {S : Type*} {q : ℕ} (k : Fin q → ℕ) :
    TupleState S k ≃ ((SelectedVertices k → S) × GraphTuple k) where
  toFun p := (pooledTypes p, fun i ↦ (p i).2)
  invFun p := fun i ↦ (fun a ↦ p.1 ⟨i,a⟩, p.2 i)
  left_inv p := by
    funext i
    apply Prod.ext
    · funext a
      rfl
    · rfl
  right_inv p := by
    rcases p with ⟨y,H⟩
    rfl

section Model

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Actual atom mass of the product of unweighted connected-state measures. -/
def samplingWeight (M : FiniteIrreducibleModel S) {q : ℕ}
    (k : Fin q → ℕ) (p : TupleState S k) : ℝ :=
  ∏ i, ∏ a : Fin (k i), M.weight ((p i).1 a)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem samplingWeight_pos (M : FiniteIrreducibleModel S)
    {q : ℕ} (k : Fin q → ℕ) (p : TupleState S k) : 0 < samplingWeight M k p :=
  Finset.prod_pos (fun i _ ↦ Finset.prod_pos (fun a _ ↦ M.weight_pos ((p i).1 a)))

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem samplingWeight_eq_fiberProduct (M : FiniteIrreducibleModel S)
    {q : ℕ} (k : Fin q → ℕ) (p : TupleState S k) :
    samplingWeight M k p =
      ∏ a : S, (M.weight a) ^ fiberCount (pooledTypes p) a := by
  unfold samplingWeight
  change (∏ i, ∏ a, M.weight (pooledTypes p ⟨i,a⟩)) = _
  rw [← Fintype.prod_sigma (fun v : SelectedVertices k ↦ M.weight (pooledTypes p v))]
  exact prod_by_typeFibers (pooledTypes p) M.weight

theorem baseLaw_real_singleton (M : FiniteIrreducibleModel S)
    {q : ℕ} (k : Fin q → ℕ) (p : TupleState S k) :
    (baseLaw M.bjrModel k).real {p} = samplingWeight M k p := by
  have hatom (i : Fin q) :
      ((typeLaw M.bjrModel (k i)).prod Measure.count) {p i} =
        ENNReal.ofReal (∏ a : Fin (k i), M.weight ((p i).1 a)) := by
    change ((typeLaw M.bjrModel (k i)).prod Measure.count)
      {((p i).1, (p i).2)} = _
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
    simp only [typeLaw, Measure.pi_singleton, FiniteIrreducibleModel.bjrModel_mu,
      FiniteIrreducibleModel.measure_singleton, Measure.count_singleton, mul_one]
    exact (ENNReal.ofReal_prod_of_nonneg
      (fun a _ ↦ (M.weight_pos ((p i).1 a)).le)).symm
  have hmass : (baseLaw M.bjrModel k) {p} =
      ENNReal.ofReal (samplingWeight M k p) := by
    rw [baseLaw, Measure.pi_singleton]
    simp_rw [hatom]
    exact (ENNReal.ofReal_prod_of_nonneg (fun i _ ↦
      (Finset.prod_pos (fun a _ ↦ M.weight_pos ((p i).1 a))).le)).symm
  rw [Measure.real, hmass, ENNReal.toReal_ofReal (samplingWeight_pos M k p).le]

/-- Every weighted integral against the actual finite type/graph base law
is its literal finite atom sum. -/
theorem integral_baseLaw_eq_finite_sum (M : FiniteIrreducibleModel S)
    {q : ℕ} (k : Fin q → ℕ) (F : TupleState S k → ℝ) :
    (∫ p, F p ∂baseLaw M.bjrModel k) =
      ∑ p : TupleState S k, samplingWeight M k p * F p := by
  rw [integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul, baseLaw_real_singleton]

end Model

end PerronWright.FiniteIrreducibleConnectedLawFiniteSum

