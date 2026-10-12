import PerronWright.Probability.BrownianExcursionWindowPointMeasure

/-!
# The literal full size--surplus excursion atom measure

The measure is the genuine countable Dirac sum indexed by the already
proved nonrepeating rational representatives. Actual positive-size
local finiteness supplies every finite compact restriction.
-/

open MeasureTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal CompactlySupported

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionAtomicMeasure

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionSection
open BrownianExcursionWindowPointMeasure ComponentGlobalPointProcess
open PositiveSizeSurplusExhaustion FinitePointMeasureCompact
open CountableFiniteAtomSampling LocallyFinitePointMeasureVague

def positiveSize (lambda : ℝ) (q : ℚ) (p : Input) : Ioi (0 : ℝ) :=
  if h : 0 < lengthValue lambda q p.1 then ⟨lengthValue lambda q p.1,h⟩ else ⟨1,by norm_num⟩

def atom (lambda : ℝ) (p : Input) (q : ℚ) : PositiveSizeSurplus :=
  (positiveSize lambda q p,p.2 q)

theorem measurable_atom (lambda : ℝ) (q : ℚ) : Measurable (fun p : Input ↦ atom lambda p q) := by
  have hs : Measurable (positiveSize lambda q) := by
    let A : Set Input := {p | 0 < lengthValue lambda q p.1}
    let F : A → Ioi (0 : ℝ) := fun p ↦ ⟨lengthValue lambda q p.1.1,p.2⟩
    have hF : Measurable F := ((measurable_lengthValue lambda q).comp
      (measurable_fst.comp measurable_subtype_coe)).subtype_mk
    have he : positiveSize lambda q =
        (fun p ↦ if h : p ∈ A then F ⟨p,h⟩ else (⟨1,by norm_num⟩ : Ioi (0 : ℝ))) := by
      funext p
      by_cases hp : 0 < lengthValue lambda q p.1 <;> simp [positiveSize,A,F,hp]
    rw [he]
    exact Measurable.dite hF measurable_const
      (measurableSet_lt measurable_const ((measurable_lengthValue lambda q).comp measurable_fst))
  exact hs.prodMk ((measurable_pi_apply q).comp measurable_snd)

def active (lambda : ℝ) (p : Input) : Set ℚ :=
  {q | Good lambda p.1 ∧ Representative (driftedReflectionPath lambda p.1) q ∧
    0 < lengthValue lambda q p.1}

def measure (lambda : ℝ) (p : Input) : Measure PositiveSizeSurplus :=
  Measure.sum (fun q ↦ if q ∈ active lambda p then Measure.dirac (atom lambda p q) else 0)

theorem selected_eq_active_window (lambda : ℝ) (m : ℕ) (p : Input) :
    selected lambda m p = {q | q ∈ active lambda p ∧ atom lambda p q ∈ window m} := by
  ext q
  constructor
  · intro hq
    have hp : 0 < lengthValue lambda q p.1 := (lower_pos m).trans_le hq.2.2.1.1
    refine ⟨⟨hq.1,hq.2.1,hp⟩,?_⟩
    change (atom lambda p q).1.val ∈ Icc (lower m) (upper m) ∧ (atom lambda p q).2 ≤ m
    simpa only [atom,positiveSize,dif_pos hp] using hq.2.2
  · rintro ⟨ha,hw⟩
    refine ⟨ha.1,ha.2.1,?_⟩
    change (atom lambda p q).1.val ∈ Icc (lower m) (upper m) ∧ (atom lambda p q).2 ≤ m at hw
    simpa only [atom,positiveSize,dif_pos ha.2.2] using hw

theorem embedding_windowAtom (lambda : ℝ) (m : ℕ) (p : Input) (q : ℚ)
    (hq : q ∈ selected lambda m p) :
    positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) (windowAtom lambda m q p) =
      atom lambda p q := by
  have hp : 0 < lengthValue lambda q p.1 := (lower_pos m).trans_le hq.2.2.1.1
  apply Prod.ext
  · apply Subtype.ext
    simpa only [positiveWindowEmbedding,atom,positiveSize,dif_pos hp] using
      (windowAtom_eq lambda m q p hq).1
  · exact (windowAtom_eq lambda m q p hq).2

theorem map_windowPointMeasure (lambda : ℝ) (m : ℕ) (p : Input) :
    (((windowPointMeasure lambda m p :
      FiniteMeasure (SurplusWindow (lower m) (upper m) m)) : Measure _).map
        (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m))) =
      ((ofFinset (finite_selected lambda m p).toFinset (atom lambda p) :
        FiniteMeasure PositiveSizeSurplus) : Measure PositiveSizeSurplus) := by
  have ht : selected lambda m p = ((finite_selected lambda m p).toFinset : Set ℚ) := by
    ext q
    simp
  unfold BrownianExcursionWindowPointMeasure.windowPointMeasure
  rw [pointMeasure_eq_ofFinset _ _ _ _ ht,ofFinset_toMeasure,ofFinset_toMeasure]
  rw [Measure.map_finset_sum (measurable_positiveWindowEmbedding _ _ _ _).aemeasurable]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Measure.map_dirac' (measurable_positiveWindowEmbedding _ _ _ _),
    embedding_windowAtom lambda m p q (by simpa using hq)]

theorem measure_restrict_window (lambda : ℝ) (m : ℕ) (p : Input) :
    (measure lambda p).restrict (window m) =
      (((windowPointMeasure lambda m p :
        FiniteMeasure (SurplusWindow (lower m) (upper m) m)) : Measure _).map
          (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m))) := by
  rw [map_windowPointMeasure]
  unfold measure
  rw [restrict_sum_dirac _ _ _ (isCompact_window m).measurableSet]
  have he : {q | q ∈ active lambda p ∧ atom lambda p q ∈ window m} = selected lambda m p :=
    (selected_eq_active_window lambda m p).symm
  simp only [he]
  exact sum_dirac_eq_ofFinset _ (finite_selected lambda m p) _

theorem measure_window_lt_top (lambda : ℝ) (m : ℕ) (p : Input) :
    measure lambda p (window m) < ∞ := by
  have he := congrArg (fun μ : Measure PositiveSizeSurplus ↦ μ univ)
    (measure_restrict_window lambda m p)
  rw [Measure.restrict_apply MeasurableSet.univ,univ_inter,
    Measure.map_apply (measurable_positiveWindowEmbedding _ _ _ _) MeasurableSet.univ,
    preimage_univ] at he
  rw [he]
  exact measure_lt_top _ _

instance measure_finiteOnCompacts (lambda : ℝ) (p : Input) :
    IsFiniteMeasureOnCompacts (measure lambda p) := by
  constructor
  intro K hK
  obtain ⟨m,hm⟩ := exists_compact_subset_window hK
  exact (measure_mono hm).trans_lt (measure_window_lt_top lambda m p)

instance measure_locallyFinite (lambda : ℝ) (p : Input) :
    IsLocallyFiniteMeasure (measure lambda p) := inferInstance

theorem measure_isLocalPoint (lambda : ℝ) (p : Input) :
    IsLocallyFinitePointMeasure (measure lambda p) := by
  refine ⟨inferInstance,?_⟩
  intro K hK
  obtain ⟨m,hm⟩ := exists_compact_subset_window hK
  have hf : {q | q ∈ active lambda p ∧ atom lambda p q ∈ K}.Finite :=
    (finite_selected lambda m p).subset (fun q hq ↦
      (selected_eq_active_window lambda m p) ▸ ⟨hq.1,hm hq.2⟩)
  rw [measure,restrict_sum_dirac_eq_ofFinset _ _ K hK.measurableSet hf]
  obtain ⟨n,x,hx⟩ := (ofFinset hf.toFinset (atom lambda p)).property
  exact ⟨n,x,congrArg (fun μ : FiniteMeasure PositiveSizeSurplus ↦ (μ : Measure PositiveSizeSurplus)) hx⟩

def process (lambda : ℝ) (p : Input) : LocalPointMeasure PositiveSizeSurplus :=
  ⟨measure lambda p,measure_isLocalPoint lambda p⟩

@[simp] theorem process_toMeasure (lambda : ℝ) (p : Input) :
    (process lambda p : Measure PositiveSizeSurplus) = measure lambda p := rfl

end PerronWright.BrownianExcursionAtomicMeasure
