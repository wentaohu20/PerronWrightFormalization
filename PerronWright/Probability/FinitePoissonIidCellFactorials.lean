import PerronWright.Probability.FinitePointMeasureMixedFactorials
import PerronWright.Probability.FinitePoissonIntensityLaw
import Mathlib.Probability.Independence.Basic

/-!
# Actual mixed factorial moments of iid spatial atoms

The disjoint-cell moments are obtained by counting labelled injective
atom tuples and integrating their actual coordinate events.  No count
distribution or moment formula is supplied as a hypothesis.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FinitePoissonIidCellFactorials

open FinitePointMeasureCompact FinitePointMeasureFintype
  FinitePointMeasureMixedFactorials FinitePoissonPointLaw

variable {E D : Type*} [MeasurableSpace E] [Fintype D]

def mixedFactorial (A : D → Set E) (q : D → ℕ) (η : PointMeasure E) : ℝ≥0∞ :=
  ∏ i, ((count η (A i)).descFactorial (q i) : ℝ≥0∞)

def slotEvent (A : D → Set E) (q : D → ℕ) {n : ℕ}
    (e : Slots q ↪ Fin n) : Set (Fin n → E) :=
  {x | ∀ s, x (e s) ∈ A s.1}

theorem measurableSet_slotEvent (A : D → Set E) (q : D → ℕ)
    (hA : ∀ i, MeasurableSet (A i)) {n : ℕ} (e : Slots q ↪ Fin n) :
    MeasurableSet (slotEvent A q e) := by
  simp only [slotEvent, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun s ↦ (hA s.1).preimage (measurable_pi_apply (e s)))

theorem ofFintype_fin_eq_ofAtomsPoint {n : ℕ} (x : Fin n → E) :
    ofFintype x = ofAtomsPoint x := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The mixed factorial counts genuine labelled injections into the atoms. -/
theorem mixedFactorial_ofAtomsPoint (A : D → Set E) (q : D → ℕ)
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) {n : ℕ} (x : Fin n → E) :
    mixedFactorial A q (ofAtomsPoint x) =
      ∑ e : Slots q ↪ Fin n, if x ∈ slotEvent A q e then 1 else 0 := by
  have hc := cellTuple_card x A q hAd
  rw [← ofFintype_fin_eq_ofAtomsPoint]
  simp only [mixedFactorial, count_ofFintype x (hA _)]
  rw [← Nat.cast_prod, ← hc]
  simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, slotEvent, Set.mem_ofPred_eq]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> rfl

/-- Each actual injected coordinate event has the product location probability. -/
theorem pi_slotEvent (μ : Measure E) [IsProbabilityMeasure μ]
    (A : D → Set E) (q : D → ℕ) (hA : ∀ i, MeasurableSet (A i))
    {n : ℕ} (e : Slots q ↪ Fin n) :
    Measure.pi (fun _ : Fin n ↦ μ) (slotEvent A q e) = ∏ i, (μ (A i)) ^ q i := by
  have hi := iIndepFun_pi (μ := fun _ : Fin n ↦ μ)
    (X := fun (_ : Fin n) (z : E) ↦ z) (fun _ ↦ measurable_id.aemeasurable)
  have he := (hi.precomp e.injective).measure_inter_preimage_eq_mul
    Finset.univ (sets := fun s : Slots q ↦ A s.1) (fun s _ ↦ hA s.1)
  have hm (s : Slots q) :
      Measure.pi (fun _ : Fin n ↦ μ) ((fun x ↦ x (e s)) ⁻¹' A s.1) = μ (A s.1) := by
    simpa only [(measurePreserving_eval (fun _ : Fin n ↦ μ) (e s)).map_eq] using
      (Measure.map_apply (μ := Measure.pi (fun _ : Fin n ↦ μ))
        (f := fun x : Fin n → E ↦ x (e s))
        (measurable_pi_apply (e s)) (hA s.1)).symm
  simp only [hm] at he
  simpa only [Finset.mem_univ, Set.iInter_true, slotEvent, Set.ofPred_forall, Set.preimage,
    Fintype.prod_sigma, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using he

variable [TopologicalSpace E] [BorelSpace E] [SecondCountableTopology E]
  [HasOuterApproxClosed E]

omit [SecondCountableTopology E] in
theorem measurable_mixedFactorial (A : D → Set E) (q : D → ℕ)
    (hA : ∀ i, MeasurableSet (A i)) : Measurable (mixedFactorial A q) := by
  apply Finset.measurable_prod
  intro i _
  exact (measurable_of_countable (fun n : ℕ ↦ (n.descFactorial (q i) : ℝ≥0∞))).comp
    (FinitePointMeasureMeasurable.measurable_count (hA i))

/-- The actual iid atom law has the exact disjoint-cell mixed factorial moments. -/
theorem iidAtomsLaw_lintegral_mixedFactorial (μ : Measure E) [IsProbabilityMeasure μ]
    (n : ℕ) (A : D → Set E) (q : D → ℕ)
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) :
    (∫⁻ η, mixedFactorial A q η ∂iidAtomsLaw μ n) =
      (n.descFactorial (∑ i, q i) : ℝ≥0∞) * ∏ i, (μ (A i)) ^ q i := by
  rw [iidAtomsLaw, lintegral_map (measurable_mixedFactorial A q hA)
    (measurable_ofAtomsPoint n)]
  simp_rw [mixedFactorial_ofAtomsPoint A q hAd hA]
  rw [lintegral_finsetSum Finset.univ
    (f := fun (e : Slots q ↪ Fin n) (x : Fin n → E) ↦
      if x ∈ slotEvent A q e then (1 : ℝ≥0∞) else 0)
    (fun e _ ↦ measurable_const.ite (measurableSet_slotEvent A q hA e) measurable_const)]
  have he (e : Slots q ↪ Fin n) :
      (∫⁻ x : Fin n → E, if x ∈ slotEvent A q e then (1 : ℝ≥0∞) else 0
        ∂Measure.pi (fun _ ↦ μ)) = ∏ i, (μ (A i)) ^ q i := by
    change (∫⁻ x : Fin n → E, (slotEvent A q e).indicator 1 x
      ∂Measure.pi (fun _ ↦ μ)) = _
    rw [lintegral_indicator_one (measurableSet_slotEvent A q hA e)]
    exact pi_slotEvent μ A q hA e
  simp_rw [he]
  simp [Fintype.card_embedding_eq, Slots]

end PerronWright.FinitePoissonIidCellFactorials
