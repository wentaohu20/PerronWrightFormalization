import PerronWright.Probability.BrownianEntranceFiniteDimensionalFamily
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Tuple

/-! # The proved entrance probability family on arbitrary finite time sets

Finite interior time sets are sorted only to use the actual Gaussian product
formula, then their coordinates are returned to their intrinsic time labels.
Projectivity is obtained from the common actual positive-bridge source.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceProjectiveFamily

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianEntranceFiniteDimensionalFamily

abbrev InteriorTime (T : ℝ≥0) := {t : ℝ≥0 // 0 < t ∧ t < T}

def sortedTimes (T : ℝ≥0) (J : Finset (InteriorTime T)) : Fin (J.card+2) → ℝ≥0 :=
  Fin.snoc (Fin.cons 0 (fun i : Fin J.card ↦ ((J.orderIsoOfFin rfl i).val).val)) T

theorem sortedTimes_zero (T : ℝ≥0) (J : Finset (InteriorTime T)) :
    sortedTimes T J 0 = 0 := by simp [sortedTimes,Fin.snoc_apply_zero]

theorem sortedTimes_last (T : ℝ≥0) (J : Finset (InteriorTime T)) :
    sortedTimes T J (Fin.last (J.card+1)) = T := by simp [sortedTimes]

theorem sortedTimes_internal (T : ℝ≥0) (J : Finset (InteriorTime T)) (i : Fin J.card) :
    sortedTimes T J i.succ.castSucc = ((J.orderIsoOfFin rfl i).val).val := by
  simp only [sortedTimes,Fin.snoc_castSucc,Fin.cons_succ]

theorem sortedTimes_strictMono (T : ℝ≥0) (hT : 0 < T) (J : Finset (InteriorTime T)) :
    StrictMono (sortedTimes T J) := by
  have hm : StrictMono (fun i : Fin J.card ↦ ((J.orderIsoOfFin rfl i).val).val) := by
    intro i j hij
    exact (J.orderIsoOfFin rfl).strictMono hij
  have hc : StrictMono (Fin.cons 0 (fun i : Fin J.card ↦ ((J.orderIsoOfFin rfl i).val).val)) :=
    Fin.strictMono_cons.mpr ⟨fun i ↦ (J.orderIsoOfFin rfl i).val.property.1,hm⟩
  rw [sortedTimes,← Fin.insertNth_last']
  apply (Fin.strictMono_insertNth_iff _ _ _).mpr
  refine ⟨hc,?_,?_⟩
  · intro i _hi
    cases i using Fin.cases with
    | zero => simpa using hT
    | succ i => simpa using (J.orderIsoOfFin rfl i).val.property.2
  · intro i hi
    have := Fin.is_lt i
    have he := Fin.le_iff_val_le_val.mp hi
    simp only [Fin.val_last,Fin.val_castSucc] at he
    omega

def unsort (T : ℝ≥0) (J : Finset (InteriorTime T)) (v : Fin J.card → ℝ) : J → ℝ :=
  fun j ↦ v ((J.orderIsoOfFin rfl).symm j)

theorem measurable_unsort (T : ℝ≥0) (J : Finset (InteriorTime T)) : Measurable (unsort T J) :=
  measurable_pi_lambda _ (fun _j ↦ measurable_pi_apply _)

def finiteLaw (T : ℝ≥0) (J : Finset (InteriorTime T)) : Measure (J → ℝ) :=
  (orderedLaw J.card (sortedTimes T J)).map (unsort T J)

theorem finiteLaw_empty (T : ℝ≥0) : finiteLaw T ∅ = Measure.dirac 0 := by
  change (Measure.dirac (0 : Fin 0 → ℝ)).map (unsort T ∅) = Measure.dirac 0
  rw [Measure.map_dirac' (measurable_unsort T ∅)]
  exact congrArg Measure.dirac (Subsingleton.elim _ _)

theorem finiteLaw_isProbability (T : ℝ≥0) (hT : 0 < T) (J : Finset (InteriorTime T)) :
    IsProbabilityMeasure (finiteLaw T J) := by
  let := orderedLaw_isProbability J.card (sortedTimes T J) (sortedTimes_strictMono T hT J)
  exact Measure.isProbabilityMeasure_map (measurable_unsort T J).aemeasurable

def finiteEval (T : ℝ≥0) (J : Finset (InteriorTime T)) (f : Path) : J → ℝ :=
  fun j ↦ f j.val.val

theorem continuous_finiteEval (T : ℝ≥0) (J : Finset (InteriorTime T)) :
    Continuous (finiteEval T J) := continuous_pi (fun _ ↦ continuous_eval_const _)

theorem unsort_orderedEval (T : ℝ≥0) (J : Finset (InteriorTime T)) (f : Path) :
    unsort T J (orderedEval J.card (sortedTimes T J) f) = finiteEval T J f := by
  funext j
  simp only [unsort,orderedEval,finiteEval,sortedTimes_internal,OrderIso.apply_symm_apply]

theorem actual_finite_bounded_test_tendsto (T : ℝ≥0) (hT : 0 < T)
    (J : Finset (InteriorTime T)) (C : ℝ) (Ψ : (J → ℝ) → ℝ≥0∞)
    (hΨ : Measurable Ψ) (hb : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ f, Ψ (finiteEval T J f) ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (∫⁻ v, Ψ v ∂finiteLaw T J)) := by
  have he := actual_ordered_bounded_test_tendsto J.card (sortedTimes T J)
    (sortedTimes_strictMono T hT J) (sortedTimes_zero T J) C
    (fun v ↦ Ψ (unsort T J v)) (hΨ.comp (measurable_unsort T J)) (fun v ↦ hb _)
  rw [sortedTimes_last] at he
  simp only [unsort_orderedEval] at he
  rw [finiteLaw,lintegral_map hΨ (measurable_unsort T J)]
  exact he

theorem actual_finite_borel_probability_tendsto (T : ℝ≥0) (hT : 0 < T)
    (J : Finset (InteriorTime T)) {B : Set (J → ℝ)} (hB : MeasurableSet B) :
    Tendsto (fun a : ℝ ↦ ((positiveBridgeLaw a T).map (finiteEval T J)) B)
      (𝓝[>] 0) (𝓝 (finiteLaw T J B)) := by
  have he := actual_finite_bounded_test_tendsto T hT J 1
    (B.indicator (fun _ ↦ 1)) (measurable_const.indicator hB)
    (fun v ↦ by by_cases hv : v ∈ B <;> simp [hv])
  have h1 : (fun _ : J → ℝ ↦ (1 : ℝ≥0∞)) = (1 : (J → ℝ) → ℝ≥0∞) := rfl
  have hl : (∫⁻ v, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) v ∂finiteLaw T J) = finiteLaw T J B := by
    rw [h1]; exact lintegral_indicator_one hB
  rw [hl] at he
  apply he.congr
  intro a
  rw [← lintegral_map (measurable_const.indicator hB) (continuous_finiteEval T J).measurable,
    h1,lintegral_indicator_one hB]

/-- A probability projective family, with consistency discharged from its
actual conditioned Brownian source rather than supplied as an interface. -/
theorem finiteLaw_projective (T : ℝ≥0) (hT : 0 < T) :
    IsProjectiveMeasureFamily (α := fun _ : InteriorTime T ↦ ℝ) (finiteLaw T) := by
  intro I J hJI
  have hm : Measurable (Finset.restrict₂ (π := fun _ : InteriorTime T ↦ ℝ) hJI) :=
    Finset.measurable_restrict₂ hJI
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hm hB]
  have hsmall := actual_finite_borel_probability_tendsto T hT J hB
  have hbig := actual_finite_borel_probability_tendsto T hT I
    (hm hB)
  apply tendsto_nhds_unique hsmall
  apply hbig.congr
  intro a
  rw [Measure.map_apply (continuous_finiteEval T J).measurable hB,
    Measure.map_apply (continuous_finiteEval T I).measurable (hm hB)]
  rfl

end PerronWright.BrownianEntranceProjectiveFamily
