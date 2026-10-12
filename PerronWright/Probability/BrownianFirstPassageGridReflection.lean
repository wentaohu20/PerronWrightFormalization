import PerronWright.Probability.BrownianFiniteReflectionLaw
import PerronWright.Probability.ContinuousPathFirstPassage
import Mathlib.Data.Nat.Find

/-! # Genuine finite-grid first-passage reflections preserve Brownian law

The index is the first grid time at or after the literal first passage,
capped at the final grid index. All fibers are proved measurable and
invariant under reflection at their selected time. Applying the proved
restriction argument thus gives an actual finite-grid reflection law,
with no reflection, strong-Markov, or stopping-time premise left over.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageGridReflection

open BrownianPathLaw BrownianPathIndependentIncrements BrownianFiniteReflectionLaw
open ContinuousPathFirstPassage

def gridPredicate (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) (f : Path) (j : ℕ) : Prop :=
  j ≤ m ∧ (firstPassage level f ≤ t j ∨ j = m)

theorem exists_gridPredicate (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) (f : Path) :
    ∃ j, gridPredicate level t m f j := ⟨m,le_rfl,Or.inr rfl⟩

def gridIndex (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) (f : Path) : Fin (m+1) :=
  ⟨Nat.find (exists_gridPredicate level t m f),
    Nat.lt_succ_of_le (Nat.find_spec (exists_gridPredicate level t m f)).1⟩

theorem gridIndex_eq_iff (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) (f : Path) (i : Fin (m+1)) :
    gridIndex level t m f = i ↔
      (firstPassage level f ≤ t i ∨ i.val = m) ∧
        ∀ j : ℕ, j < i.val → (t j : ℝ≥0∞) < firstPassage level f := by
  rw [Fin.ext_iff]
  change Nat.find (exists_gridPredicate level t m f) = i.val ↔ _
  rw [Nat.find_eq_iff]
  constructor
  · rintro ⟨hi,hprior⟩
    refine ⟨hi.2,?_⟩
    intro j hj
    apply lt_of_not_ge
    intro hcross
    exact hprior j hj ⟨by omega,Or.inl hcross⟩
  · rintro ⟨hi,hprior⟩
    refine ⟨⟨by omega,hi⟩,?_⟩
    intro j hj hpred
    rcases hpred.2 with hcross | hlast
    · exact (not_le_of_gt (hprior j hj)) hcross
    · omega

theorem measurable_gridIndex (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (gridIndex level t m) := by
  apply measurable_to_countable'
  intro i
  have hcross : MeasurableSet {f : Path | firstPassage level f ≤ t i ∨ i.val = m} := by
    by_cases hi : i.val = m
    · simpa only [hi,or_true,ofPred_true] using (MeasurableSet.univ : MeasurableSet (univ : Set Path))
    · simpa only [hi,or_false] using
        measurableSet_le (measurable_firstPassage level) measurable_const
  have hprior : MeasurableSet {f : Path | ∀ j : ℕ, j < i.val →
      (t j : ℝ≥0∞) < firstPassage level f} := by
    have he : {f : Path | ∀ j : ℕ, j < i.val → (t j : ℝ≥0∞) < firstPassage level f} =
        ⋂ j : ℕ, {f : Path | j < i.val → (t j : ℝ≥0∞) < firstPassage level f} := by ext f; simp
    rw [he]
    apply MeasurableSet.iInter
    intro j
    by_cases hj : j < i.val
    · simpa only [hj,true_implies] using
        measurableSet_lt measurable_const (measurable_firstPassage level)
    · simpa only [hj,false_implies,ofPred_true] using (MeasurableSet.univ : MeasurableSet (univ : Set Path))
  have he : gridIndex level t m ⁻¹' {i} =
      {f : Path | firstPassage level f ≤ t i ∨ i.val = m} ∩
        {f : Path | ∀ j : ℕ, j < i.val → (t j : ℝ≥0∞) < firstPassage level f} := by
    ext f
    exact gridIndex_eq_iff level t m f i
  rw [he]
  exact hcross.inter hprior

theorem firstPassage_le_reflectionPath (level : ℝ) (T s : ℝ≥0) (hs : s ≤ T) (f : Path) :
    firstPassage level (reflectionPath T f) ≤ s ↔ firstPassage level f ≤ s := by
  have he (v : ℝ≥0) (hv : v ≤ s) : reflectionPath T f v = f v := by
    rw [reflectionPath_eval,min_eq_left (hv.trans hs)]
    ring
  rw [firstPassage_le_iff,firstPassage_le_iff]
  constructor <;> rintro ⟨v,hv,hf⟩
  · exact ⟨v,hv,by simpa only [he v hv] using hf⟩
  · exact ⟨v,hv,by simpa only [he v hv] using hf⟩

/-- The actual first-passage fibers satisfy the reflection invariance;
this is a deterministic theorem, not an input to the final law. -/
theorem gridIndex_reflection_stable (level : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (m : ℕ) (i : Fin (m+1)) (f : Path) :
    gridIndex level t m (reflectionPath (t i) f) = i ↔ gridIndex level t m f = i := by
  rw [gridIndex_eq_iff,gridIndex_eq_iff]
  have hi := firstPassage_le_reflectionPath level (t i) (t i) le_rfl f
  have hj (j : ℕ) (hji : j < i.val) :
      (t j : ℝ≥0∞) < firstPassage level (reflectionPath (t i) f) ↔
        (t j : ℝ≥0∞) < firstPassage level f := by
    rw [← not_le,← not_le]
    exact not_congr (firstPassage_le_reflectionPath level (t i) (t j) (ht hji.le) f)
  constructor <;> rintro ⟨ha,hb⟩
  · exact ⟨(or_congr hi Iff.rfl).mp ha,fun j hji ↦ (hj j hji).mp (hb j hji)⟩
  · exact ⟨(or_congr hi Iff.rfl).mpr ha,fun j hji ↦ (hj j hji).mpr (hb j hji)⟩

def gridReflection (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) : Path → Path :=
  chosenReflection (fun i : Fin (m+1) ↦ t i) (gridIndex level t m)

theorem measurable_gridReflection (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (gridReflection level t m) :=
  measurable_chosenReflection _ (measurable_gridIndex level t m)

/-- Genuine capped-grid reflection of the actual Brownian process has
exactly its entire original path law. All fiber hypotheses are proved. -/
theorem gridReflection_law (level : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (m : ℕ) :
    pathLaw.map (gridReflection level t m) = pathLaw :=
  chosenReflection_law _ (measurable_gridIndex level t m)
    (gridIndex_reflection_stable level t ht m)

def dyadicGrid (n j : ℕ) : ℝ≥0 := (j : ℝ≥0)/(2 : ℝ≥0)^n

theorem monotone_dyadicGrid (n : ℕ) : Monotone (dyadicGrid n) := by
  intro i j hij
  unfold dyadicGrid
  gcongr

def dyadicReflection (level : ℝ) (n m : ℕ) : Path → Path := gridReflection level (dyadicGrid n) m

theorem measurable_dyadicReflection (level : ℝ) (n m : ℕ) :
    Measurable (dyadicReflection level n m) := measurable_gridReflection _ _ _

theorem dyadicReflection_law (level : ℝ) (n m : ℕ) :
    pathLaw.map (dyadicReflection level n m) = pathLaw :=
  gridReflection_law level _ (monotone_dyadicGrid n) m

end PerronWright.BrownianFirstPassageGridReflection
