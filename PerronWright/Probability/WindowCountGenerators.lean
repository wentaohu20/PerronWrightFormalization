import PerronWright.Probability.FinitePointMeasureCountDeterminacy
import PerronWright.Probability.ComponentWindowPointMeasures
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # A literal countable generating family for compact-window point laws

Rational size half-lines at individual surplus values, together with
the empty and whole cells, form a genuine countable generating pi-system
on the actual compact window. Their counts therefore determine the
actual weak-Borel point-measure probability law.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.WindowCountGenerators

open FinitePointMeasureCompact FinitePointMeasureMeasurable
open FinitePointMeasureCountDeterminacy ComponentWindowPointMeasures

abbrev Index (R : ℕ) := Option (Option (ℚ × Fin (R + 1)))

def sizeCell (R : ℕ) : Index R → Set ℝ
  | none => Set.univ
  | some none => ∅
  | some (some x) => Set.Iic (x.1 : ℝ)

def surplusCell (R : ℕ) : Index R → Finset ℕ
  | none => Finset.range (R + 1)
  | some none => ∅
  | some (some x) => {x.2.val}

def cell (a b : ℝ) (R : ℕ) (i : Index R) : Set (SurplusWindow a b R) :=
  windowEmbedding a b R ⁻¹' (sizeCell R i ×ˢ (surplusCell R i : Set ℕ))

@[simp] theorem cell_none (a b : ℝ) (R : ℕ) : cell a b R none = Set.univ := by
  ext z
  simp [cell, sizeCell, surplusCell, windowEmbedding, z.2.isLt]

@[simp] theorem cell_empty (a b : ℝ) (R : ℕ) : cell a b R (some none) = ∅ := by
  simp [cell, sizeCell, surplusCell]

@[simp] theorem cell_rat (a b : ℝ) (R : ℕ) (t : ℚ) (r : Fin (R + 1)) :
    cell a b R (some (some (t, r))) = {z | z.1.val ≤ (t : ℝ) ∧ z.2 = r} := by
  ext z
  simp [cell, sizeCell, surplusCell, windowEmbedding, Fin.ext_iff]

@[simp] theorem cell_pair (a b : ℝ) (R : ℕ) (x : ℚ × Fin (R + 1)) :
    cell a b R (some (some x)) = {z | z.1.val ≤ (x.1 : ℝ) ∧ z.2 = x.2} := by
  simpa only [Prod.mk.eta] using cell_rat a b R x.1 x.2

theorem measurableSet_sizeCell (R : ℕ) (i : Index R) : MeasurableSet (sizeCell R i) := by
  cases i with
  | none => exact MeasurableSet.univ
  | some i => cases i with
    | none => exact MeasurableSet.empty
    | some x => exact measurableSet_Iic

theorem volume_frontier_sizeCell (R : ℕ) (i : Index R) :
    (volume : Measure ℝ) (frontier (sizeCell R i)) = 0 := by
  cases i with
  | none => simp [sizeCell]
  | some i => cases i with
    | none => simp [sizeCell]
    | some x => simp [sizeCell]

theorem measurableSet_cell (a b : ℝ) (R : ℕ) (i : Index R) : MeasurableSet (cell a b R i) :=
  (measurable_windowEmbedding a b R)
    ((measurableSet_sizeCell R i).prod (surplusCell R i).measurableSet)

theorem univ_mem_range_cell (a b : ℝ) (R : ℕ) : Set.univ ∈ Set.range (cell a b R) :=
  ⟨none, cell_none a b R⟩

theorem isPiSystem_range_cell (a b : ℝ) (R : ℕ) : IsPiSystem (Set.range (cell a b R)) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
  cases i with
  | none => simp
  | some i => cases i with
    | none => refine ⟨some none, by simp⟩
    | some x => cases j with
      | none => refine ⟨some (some x), by simp⟩
      | some j => cases j with
        | none => refine ⟨some none, by simp⟩
        | some y =>
          by_cases hr : x.2 = y.2
          · refine ⟨some (some (min x.1 y.1, x.2)), ?_⟩
            ext z
            simp only [cell_pair, Set.mem_inter_iff, Set.mem_ofPred_eq, Rat.cast_min]
            constructor
            · rintro ⟨hz, hzx⟩
              exact ⟨⟨(le_min_iff.mp hz).1, hzx⟩,
                ⟨(le_min_iff.mp hz).2, hzx.trans hr⟩⟩
            · rintro ⟨⟨hx, hzx⟩, ⟨hy, _⟩⟩
              exact ⟨le_min hx hy, hzx⟩
          · refine ⟨some none, ?_⟩
            simp only [cell_empty, cell_pair]
            symm
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro z hz
            exact hr (hz.1.2.symm.trans hz.2.2)

/-- Actual Borel sigma generation is proved through the two coordinate
maps, not supplied as an abstract count-determination hypothesis. -/
theorem measurable_eq_generateFrom_cell (a b : ℝ) (R : ℕ) :
    (inferInstance : MeasurableSpace (SurplusWindow a b R)) =
      MeasurableSpace.generateFrom (Set.range (cell a b R)) := by
  let mE : MeasurableSpace (SurplusWindow a b R) := inferInstance
  let m : MeasurableSpace (SurplusWindow a b R) :=
    MeasurableSpace.generateFrom (Set.range (cell a b R))
  have hcell (i : Index R) : MeasurableSet[m] (cell a b R i) :=
    MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self i)
  have hfiber (r : Fin (R + 1)) : MeasurableSet[m] {z : SurplusWindow a b R | z.2 = r} := by
    obtain ⟨t, ht⟩ := exists_rat_gt b
    have he : cell a b R (some (some (t, r))) = {z : SurplusWindow a b R | z.2 = r} := by
      rw [cell_rat]
      ext z
      simp only [Set.mem_ofPred_eq, and_iff_right_iff_imp]
      intro _
      exact z.1.property.2.trans ht.le
    rw [← he]
    exact hcell _
  have hsize (t : ℚ) : MeasurableSet[m]
      ((fun z : SurplusWindow a b R ↦ z.1.val) ⁻¹' Set.Iic (t : ℝ)) := by
    have he : ((fun z : SurplusWindow a b R ↦ z.1.val) ⁻¹' Set.Iic (t : ℝ)) =
        ⋃ r : Fin (R + 1), cell a b R (some (some (t, r))) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iUnion, cell_rat, Set.mem_ofPred_eq]
      constructor
      · intro hz
        exact ⟨z.2, hz, rfl⟩
      · rintro ⟨r, hr, _⟩
        exact hr
    rw [he]
    exact @MeasurableSet.iUnion _ _ m _ _ (fun r ↦ hcell _)
  have hfst : @Measurable (SurplusWindow a b R) ℝ m inferInstance (fun z ↦ z.1.val) := by
    let : MeasurableSpace (SurplusWindow a b R) := m
    have heq : (inferInstance : MeasurableSpace ℝ) =
        MeasurableSpace.generateFrom (⋃ t : ℚ, {Set.Iic (t : ℝ)}) :=
      BorelSpace.measurable_eq.trans Real.borel_eq_generateFrom_Iic_rat
    rw [heq]
    apply measurable_generateFrom
    intro A hA
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hA
    have he : A = Set.Iic (t : ℝ) := Set.mem_singleton_iff.mp ht
    rw [he]
    exact hsize t
  have hsnd : @Measurable (SurplusWindow a b R) (Fin (R + 1)) m inferInstance (fun z ↦ z.2) := by
    let : MeasurableSpace (SurplusWindow a b R) := m
    intro A _
    have he : ((fun z : SurplusWindow a b R ↦ z.2) ⁻¹' A) =
        ⋃ r : Fin (R + 1), if r ∈ A then {z : SurplusWindow a b R | z.2 = r} else ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_iUnion]
      constructor
      · intro hz
        exact ⟨z.2, by simp [hz]⟩
      · rintro ⟨r, hr⟩
        split_ifs at hr with hrA
        · exact (by simpa only [Set.mem_ofPred_eq] using hr) ▸ hrA
        · exact False.elim hr
    rw [he]
    apply MeasurableSet.iUnion
    intro r
    split_ifs
    · exact hfiber r
    · exact MeasurableSet.empty
  have hfstSub : @Measurable (SurplusWindow a b R) (Set.Icc a b) m inferInstance
      (fun z ↦ z.1) := hfst.subtype_mk
  have hid : @Measurable (SurplusWindow a b R) (SurplusWindow a b R) m mE id :=
    hfstSub.prodMk hsnd
  apply le_antisymm
  · simpa only [MeasurableSpace.comap_id] using hid.comap_le
  · exact MeasurableSpace.generateFrom_le (by
      rintro A ⟨i, rfl⟩
      exact measurableSet_cell a b R i)

theorem finiteCountLaw_eq_countLaw {E K : Type*} [MeasurableSpace E] [MetricSpace E]
    [CompactSpace E] [BorelSpace E] [Nonempty E]
    (ν : ProbabilityMeasure (PointMeasure E)) (A : K → Set E)
    (hgen : (inferInstance : MeasurableSpace E) = MeasurableSpace.generateFrom (Set.range A))
    (I : Finset K) :
    finiteCountLaw ν A hgen I =
      (countLaw ν (fun i : I ↦ A i.val)
        (fun i ↦ cells_measurable A hgen i.val) : Measure (I → ℕ)) := by
  unfold finiteCountLaw CountFamilyDeterminacy.finiteLaw familyLaw countLaw
  change ((ν : Measure (PointMeasure E)).map
    (fun η i ↦ count η (A i))).map I.restrict =
      (ν : Measure (PointMeasure E)).map (fun (η : PointMeasure E) (i : I) ↦ count η (A i.val))
  have hrestrict : Measurable (I.restrict : (K → ℕ) → I → ℕ) :=
    measurable_pi_lambda _ (fun i : I ↦ measurable_pi_apply i.val)
  rw [Measure.map_map hrestrict
    (measurable_count_vector _ (cells_measurable A hgen))]
  rfl

/-- The literal rational size-surplus count family identifies the
whole actual weak-Borel point-measure probability law. -/
theorem probabilityMeasure_eq_of_finite_cell_countLaws (a b : ℝ) (R : ℕ) (hab : a ≤ b)
    (μ ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hfinite : ∀ I : Finset (Index R),
      countLaw μ (fun i : I ↦ cell a b R i.val) (fun i ↦ measurableSet_cell a b R i.val) =
      countLaw ν (fun i : I ↦ cell a b R i.val) (fun i ↦ measurableSet_cell a b R i.val)) :
    μ = ν := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  apply probabilityMeasure_eq_of_finite_countLaws μ ν (cell a b R)
    (measurable_eq_generateFrom_cell a b R) (isPiSystem_range_cell a b R)
    (univ_mem_range_cell a b R)
  intro I
  simp only [finiteCountLaw_eq_countLaw]
  exact congrArg ProbabilityMeasure.toMeasure (hfinite I)

end PerronWright.WindowCountGenerators
