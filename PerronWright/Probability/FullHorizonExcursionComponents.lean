import PerronWright.Probability.ReflectionExcursionReturns
import PerronWright.Probability.BrownianWindowExcursionEndpoints

/-!
# Full-horizon positive components and exact window stability

These are components of the actual positivity set on the whole positive
time axis. A later zero bounds a component, and the cofinal zeros proved
for reflections of paths tending to minus infinity discharge that bound.
All sufficiently large clipped windows then give exactly this component.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.FullHorizonExcursionComponents

open BrownianPathLaw BrownianPathReflectionLaw BrownianWindowExcursions
open ContinuousPathReflection ReflectionExcursionReturns

def positiveSet (f : Path) : Set ℝ := Ioi 0 ∩ {t | 0 < realEval f t}

def component (f : Path) (q : ℝ) : Set ℝ := connectedComponentIn (positiveSet f) q

theorem isOpen_positiveSet (f : Path) : IsOpen (positiveSet f) :=
  isOpen_Ioi.inter (isOpen_lt continuous_const (continuous_realEval f))

theorem isOpen_component (f : Path) (q : ℝ) : IsOpen (component f q) :=
  (isOpen_positiveSet f).connectedComponentIn

theorem component_subset (f : Path) (q : ℝ) : component f q ⊆ positiveSet f :=
  connectedComponentIn_subset _ _

theorem mem_component_self {f : Path} {q : ℝ} (hq : q ∈ positiveSet f) :
    q ∈ component f q := mem_connectedComponentIn hq

theorem component_nonempty_iff (f : Path) (q : ℝ) :
    (component f q).Nonempty ↔ q ∈ positiveSet f := connectedComponentIn_nonempty_iff

theorem component_ordConnected (f : Path) (q : ℝ) : (component f q).OrdConnected :=
  isPreconnected_connectedComponentIn.ordConnected

theorem component_eq_of_mem {f : Path} {q r : ℝ} (hr : r ∈ component f q) :
    component f q = component f r := connectedComponentIn_eq hr

theorem component_bddBelow (f : Path) (q : ℝ) : BddBelow (component f q) :=
  ⟨0,fun _ hr ↦ (component_subset f q hr).1.le⟩

/-- A genuine zero after an anchor separates its component from all later times. -/
theorem component_lt_zero {f : Path} {q z : ℝ} (hqz : q < z)
    (hz : realEval f z = 0) : ∀ r ∈ component f q, r < z := by
  intro r hr
  have hq := (component_nonempty_iff f q).mp ⟨r,hr⟩
  by_contra h
  have hzr : z ≤ r := le_of_not_gt h
  have hc : z ∈ component f q := (component_ordConnected f q).uIcc_subset
    (mem_component_self hq) hr (mem_uIcc.mpr (Or.inl ⟨hqz.le,hzr⟩))
  have hp := (component_subset f q hc).2
  change 0 < realEval f z at hp
  simp only [hz,lt_self_iff_false] at hp

/-- No nonempty reflected excursion can extend to infinite time when the
unreflected continuous path actually tends to minus infinity. -/
theorem reflection_component_bddAbove (f : Path) (hlim : Tendsto f atTop atBot) (q : ℝ) :
    BddAbove (component (reflectionPath f) q) := by
  obtain ⟨t,hqt,hz⟩ := exists_zero_after (continuous_path f) hlim (Real.toNNReal q)
  have hqt' : q < (t : ℝ) := (Real.le_coe_toNNReal q).trans_lt hqt
  have hz' : realEval (reflectionPath f) (t : ℝ) = 0 := by
    simpa [realEval] using hz
  exact ⟨(t : ℝ),fun r hr ↦ (component_lt_zero hqt' hz' r hr).le⟩

theorem window_component_subset (H : ℝ) (f : Path) (q : ℝ) :
    BrownianWindowExcursions.component H f q ⊆ component f q := by
  apply connectedComponentIn_mono
  intro t ht
  exact ⟨ht.1.1,ht.2⟩

theorem window_component_eq_of_subset {H q : ℝ} {f : Path}
    (hsub : component f q ⊆ Ioo 0 H) :
    BrownianWindowExcursions.component H f q = component f q := by
  apply Subset.antisymm (window_component_subset H f q)
  by_cases hq : q ∈ positiveSet f
  · have hp : IsPreconnected (component f q) := isPreconnected_connectedComponentIn
    exact hp.subset_connectedComponentIn (mem_component_self hq)
      (fun t ht ↦ ⟨hsub ht,(component_subset f q ht).2⟩)
  · have he : component f q = ∅ := connectedComponentIn_eq_empty hq
    rw [he]
    exact empty_subset _

/-- Exact stabilization, not just convergence of clipped intervals. -/
theorem exists_stable_window (f : Path) (q : ℝ) (hb : BddAbove (component f q)) :
    ∃ H : ℝ, 0 < H ∧ q < H ∧ ∀ L ≥ H,
      BrownianWindowExcursions.component L f q = component f q := by
  obtain ⟨z,hz⟩ := hb
  let H := max 0 (max q z) + 1
  have h0 : 0 < H := by dsimp [H]; linarith [le_max_left (0 : ℝ) (max q z)]
  have hq : q < H := by
    dsimp [H]
    linarith [le_max_right (0 : ℝ) (max q z),le_max_left q z]
  have hzH : z < H := by
    dsimp [H]
    linarith [le_max_right (0 : ℝ) (max q z),le_max_right q z]
  refine ⟨H,h0,hq,fun L hL ↦ window_component_eq_of_subset ?_⟩
  intro r hr
  exact ⟨(component_subset f q hr).1,(hz hr).trans_lt (hzH.trans_le hL)⟩

theorem reflection_exists_stable_window (f : Path) (hlim : Tendsto f atTop atBot) (q : ℝ) :
    ∃ H : ℝ, 0 < H ∧ q < H ∧ ∀ L ≥ H,
      BrownianWindowExcursions.component L (reflectionPath f) q =
        component (reflectionPath f) q :=
  exists_stable_window _ q (reflection_component_bddAbove f hlim q)

def leftEndpoint (q : ℝ) (f : Path) : ℝ :=
  if q ∈ positiveSet f then sInf (component f q) else 0

def rightEndpoint (q : ℝ) (f : Path) : ℝ :=
  if q ∈ positiveSet f then sSup (component f q) else 0

def length (q : ℝ) (f : Path) : ℝ := rightEndpoint q f - leftEndpoint q f

theorem endpoints_eq_window {H q : ℝ} {f : Path} (hqH : q < H)
    (he : BrownianWindowExcursions.component H f q = component f q) :
    leftEndpoint q f = BrownianWindowExcursionEndpoints.leftEndpoint H q f ∧
      rightEndpoint q f = BrownianWindowExcursionEndpoints.rightEndpoint H q f := by
  have ha : q ∈ positiveWindow H f ↔ q ∈ positiveSet f := by
    change (0 < q ∧ q < H) ∧ 0 < realEval f q ↔ 0 < q ∧ 0 < realEval f q
    simp only [hqH,and_true]
  simp only [leftEndpoint,rightEndpoint,BrownianWindowExcursionEndpoints.leftEndpoint,
    BrownianWindowExcursionEndpoints.rightEndpoint,ha,he,and_self]

theorem component_eq_Ioo {f : Path} {q : ℝ} (hq : q ∈ positiveSet f)
    (hb : BddAbove (component f q)) :
    component f q = Ioo (leftEndpoint q f) (rightEndpoint q f) := by
  obtain ⟨H,_,hqH,he⟩ := exists_stable_window f q hb
  have hq' : q ∈ positiveWindow H f := ⟨⟨hq.1,hqH⟩,hq.2⟩
  have hep := endpoints_eq_window hqH (he H le_rfl)
  rw [← he H le_rfl,hep.1,hep.2]
  exact BrownianWindowExcursionEndpoints.component_eq_Ioo hq'

theorem endpoint_bounds {f : Path} {q : ℝ} (hq : q ∈ positiveSet f)
    (hb : BddAbove (component f q)) :
    0 ≤ leftEndpoint q f ∧ leftEndpoint q f < q ∧ q < rightEndpoint q f := by
  obtain ⟨H,_,hqH,he⟩ := exists_stable_window f q hb
  have hep := endpoints_eq_window hqH (he H le_rfl)
  have h := BrownianWindowExcursionEndpoints.endpoint_bounds
    (show q ∈ positiveWindow H f from ⟨⟨hq.1,hqH⟩,hq.2⟩)
  rw [hep.1,hep.2]
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem length_pos {f : Path} {q : ℝ} (hq : q ∈ positiveSet f)
    (hb : BddAbove (component f q)) : 0 < length q f :=
  sub_pos.mpr ((endpoint_bounds hq hb).2.1.trans (endpoint_bounds hq hb).2.2)

theorem leftEndpoint_zero {f : Path} {q : ℝ} (hq : q ∈ positiveSet f)
    (hb : BddAbove (component f q)) (hf0 : f 0 = 0) :
    realEval f (leftEndpoint q f) = 0 := by
  obtain ⟨H,_,hqH,he⟩ := exists_stable_window f q hb
  have hq' : q ∈ positiveWindow H f := ⟨⟨hq.1,hqH⟩,hq.2⟩
  have hep := endpoints_eq_window hqH (he H le_rfl)
  rw [hep.1]
  have hl := (BrownianWindowExcursionEndpoints.endpoint_bounds hq').1
  rcases hl.eq_or_lt with hz | hp
  · simp only [← hz,realEval,Real.toNNReal_zero]
    exact hf0
  · exact BrownianWindowExcursionEndpoints.leftEndpoint_zero_of_pos hq' hp

theorem rightEndpoint_zero {f : Path} {q : ℝ} (hq : q ∈ positiveSet f)
    (hb : BddAbove (component f q)) : realEval f (rightEndpoint q f) = 0 := by
  obtain ⟨H,_,hqH,he⟩ := exists_stable_window f q hb
  obtain ⟨z,hz⟩ := hb
  let L := max H z + 1
  have hHL : H ≤ L := by dsimp [L]; linarith [le_max_left H z]
  have hqL : q < L := hqH.trans_le hHL
  have hq' : q ∈ positiveWindow L f := ⟨⟨hq.1,hqL⟩,hq.2⟩
  have hep := endpoints_eq_window hqL (he L hHL)
  have hr : rightEndpoint q f ≤ z := by
    simp only [rightEndpoint,if_pos hq]
    exact csSup_le ((component_nonempty_iff f q).mpr hq) hz
  rw [hep.2]
  apply BrownianWindowExcursionEndpoints.rightEndpoint_zero_of_lt hq'
  rw [← hep.2]
  dsimp [L]
  linarith [le_max_right H z]

/-- Both endpoints of a genuine full-horizon reflected excursion are zeros. -/
theorem reflection_endpoints_zero (f : Path) (hlim : Tendsto f atTop atBot) {q : ℝ}
    (hq : q ∈ positiveSet (reflectionPath f)) :
    realEval (reflectionPath f) (leftEndpoint q (reflectionPath f)) = 0 ∧
      realEval (reflectionPath f) (rightEndpoint q (reflectionPath f)) = 0 := by
  have hb := reflection_component_bddAbove f hlim q
  exact ⟨leftEndpoint_zero hq hb (reflected_zero f),rightEndpoint_zero hq hb⟩

end PerronWright.FullHorizonExcursionComponents
