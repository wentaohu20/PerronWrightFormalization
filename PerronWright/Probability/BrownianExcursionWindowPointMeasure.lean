import PerronWright.Probability.CountableFiniteAtomSampling
import PerronWright.Probability.BrownianLongExcursionLocalFiniteness
import PerronWright.Probability.GlobalPointChartAtomicAssembly

/-!
# Genuine finite windows of the full Brownian excursion process

The only exceptional branch is the complement of a proved Brownian
probability-one event. Windows use actual full-horizon rational
representatives, lengths and supplied surplus coordinates. They are
measurable into the existing weak-Borel finite point-measure space.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal CompactlySupported

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionWindowPointMeasure

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionComponents
open FullHorizonExcursionSection FullHorizonExcursionEndpoints
open BrownianLongExcursionLocalFiniteness ComponentGlobalPointProcess
open PositiveSizeSurplusExhaustion GlobalPointMeasureCharts FinitePointMeasureCompact
open CountableFiniteAtomSampling

abbrev Input := Path × (ℚ → ℕ)

def lengthValue (lambda : ℝ) (q : ℚ) (f : Path) : ℝ :=
  length (q : ℝ) (driftedReflectionPath lambda f)

theorem measurable_lengthValue (lambda : ℝ) (q : ℚ) : Measurable (lengthValue lambda q) :=
  (measurable_length (q : ℝ)).comp (measurable_driftedReflectionPath lambda)

def Good (lambda : ℝ) (f : Path) : Prop :=
  ∀ m : ℕ, (longAnchors (lower m) (driftedReflectionPath lambda f)).Finite

theorem measurableSet_good (lambda : ℝ) : MeasurableSet {f : Path | Good lambda f} := by
  have he : {f : Path | Good lambda f} =
      ⋂ m : ℕ, {f : Path | (longAnchors (lower m) (driftedReflectionPath lambda f)).Finite} := by
    ext f
    simp [Good]
  rw [he]
  exact MeasurableSet.iInter (fun m ↦ (measurableSet_finite_longAnchors (lower m)).preimage
    (measurable_driftedReflectionPath lambda))

theorem ae_good (lambda : ℝ) : ∀ᵐ f ∂pathLaw, Good lambda f := by
  apply ae_all_iff.mpr
  intro m
  exact (ae_pathLaw_long_excursions_finite lambda (lower m) (lower_pos m)).mono (fun _ h ↦ h.1)

def selected (lambda : ℝ) (m : ℕ) (p : Input) : Set ℚ :=
  {q | Good lambda p.1 ∧ Representative (driftedReflectionPath lambda p.1) q ∧
    lengthValue lambda q p.1 ∈ Icc (lower m) (upper m) ∧ p.2 q ≤ m}

theorem measurable_selected (lambda : ℝ) (m : ℕ) : Measurable (selected lambda m) := by
  apply measurable_set_iff.mpr
  intro q
  apply measurableSet_setOfPred.mp
  exact ((measurableSet_good lambda).preimage measurable_fst).inter
    (((measurableSet_representative q).preimage
      ((measurable_driftedReflectionPath lambda).comp measurable_fst)).inter
      (((measurable_lengthValue lambda q).comp measurable_fst measurableSet_Icc).inter
        (measurableSet_le ((measurable_pi_apply q).comp measurable_snd) measurable_const)))

theorem finite_selected (lambda : ℝ) (m : ℕ) (p : Input) : (selected lambda m p).Finite := by
  by_cases hg : Good lambda p.1
  · exact (hg m).subset (fun q hq ↦ ⟨hq.2.1,hq.2.2.1.1⟩)
  · have he : selected lambda m p = ∅ := by ext q; simp [selected,hg]
    rw [he]
    exact finite_empty

def windowAtom (lambda : ℝ) (m : ℕ) (q : ℚ) (p : Input) :
    SurplusWindow (lower m) (upper m) m :=
  if h : lengthValue lambda q p.1 ∈ Icc (lower m) (upper m) ∧ p.2 q ≤ m then
    (⟨lengthValue lambda q p.1,h.1⟩,⟨p.2 q,Nat.lt_succ_iff.mpr h.2⟩)
  else (⟨lower m,le_rfl,lower_le_upper m⟩,⟨0,by omega⟩)

theorem measurable_windowAtom (lambda : ℝ) (m : ℕ) (q : ℚ) :
    Measurable (windowAtom lambda m q) := by
  let A : Set Input := {p | lengthValue lambda q p.1 ∈ Icc (lower m) (upper m) ∧ p.2 q ≤ m}
  have hA : MeasurableSet A :=
    ((measurable_lengthValue lambda q).comp measurable_fst measurableSet_Icc).inter
      (measurableSet_le ((measurable_pi_apply q).comp measurable_snd) measurable_const)
  let F : A → SurplusWindow (lower m) (upper m) m := fun p ↦
    (⟨lengthValue lambda q p.1.1,p.2.1⟩,⟨p.1.2 q,Nat.lt_succ_iff.mpr p.2.2⟩)
  let z : SurplusWindow (lower m) (upper m) m :=
    (⟨lower m,le_rfl,lower_le_upper m⟩,⟨0,by omega⟩)
  have hNat : Measurable (fun p : A ↦ p.1.2 q) :=
    (measurable_pi_apply q).comp (measurable_snd.comp measurable_subtype_coe)
  have hMark : Measurable (fun p : A ↦ (⟨p.1.2 q,Nat.lt_succ_iff.mpr p.2.2⟩ : Fin (m + 1))) := by
    apply measurable_to_countable'
    intro r
    convert hNat (measurableSet_singleton r.val) using 1
    ext p
    simp only [mem_preimage,mem_singleton_iff,Fin.ext_iff]
  have hF : Measurable F :=
    (((measurable_lengthValue lambda q).comp (measurable_fst.comp measurable_subtype_coe)).subtype_mk).prodMk hMark
  have he : windowAtom lambda m q = (fun p ↦ if h : p ∈ A then F ⟨p,h⟩ else z) := by
    funext p
    by_cases hp : p ∈ A
    · have hb : lengthValue lambda q p.1 ∈ Icc (lower m) (upper m) ∧ p.2 q ≤ m := hp
      simp only [windowAtom,dif_pos hb,dif_pos hp,F]
    · have hb : ¬ (lengthValue lambda q p.1 ∈ Icc (lower m) (upper m) ∧ p.2 q ≤ m) := hp
      simp only [windowAtom,dif_neg hb,dif_neg hp]
      rfl
  rw [he]
  exact Measurable.dite hF measurable_const hA

def windowPointMeasure (lambda : ℝ) (m : ℕ) (p : Input) : Chart m :=
  pointMeasure (selected lambda m) (fun p q ↦ windowAtom lambda m q p) p

theorem measurable_windowPointMeasure (lambda : ℝ) (m : ℕ) :
    Measurable (windowPointMeasure lambda m) :=
  measurable_pointMeasure (selected lambda m) (measurable_selected lambda m) _
    (measurable_pi_lambda _ (fun q ↦ measurable_windowAtom lambda m q))

theorem windowPointMeasure_size (lambda : ℝ) (m : ℕ) (p : Input) :
    size (windowPointMeasure lambda m p) = (finite_selected lambda m p).toFinset.card :=
  size_pointMeasure _ _ _ _

theorem windowAtom_eq (lambda : ℝ) (m : ℕ) (q : ℚ) (p : Input)
    (hq : q ∈ selected lambda m p) :
    (windowAtom lambda m q p).1.val = lengthValue lambda q p.1 ∧
      (windowAtom lambda m q p).2.val = p.2 q := by
  simp only [windowAtom,dif_pos hq.2.2]
  trivial

theorem windowPointMeasure_integral (lambda : ℝ) (m : ℕ) (p : Input)
    (f : SurplusWindow (lower m) (upper m) m → ℝ) :
    (∫ z, f z ∂((windowPointMeasure lambda m p :
      FiniteMeasure (SurplusWindow (lower m) (upper m) m)) : Measure _)) =
      ∑ q ∈ (finite_selected lambda m p).toFinset, f (windowAtom lambda m q p) :=
  pointMeasure_integral _ _ _ _ f

end PerronWright.BrownianExcursionWindowPointMeasure
