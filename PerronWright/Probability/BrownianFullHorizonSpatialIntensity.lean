import PerronWright.Probability.BrownianUnderGraphSpatialKernel

/-!
# Exact full under-graph intensity from disjoint unit time strips

Half-open strips really partition the nonnegative time axis. Their
intensities agree with the constructed closed-interval spatial laws,
because each vertical boundary has zero planar Lebesgue measure.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullHorizonSpatialIntensity

open BrownianPathLaw BrownianUnderGraphIntensity BrownianReflectedAreaCounts

def timeStrip (j : ℕ) : Set (ℝ × ℝ) := {z | (j : ℝ) ≤ z.1 ∧ z.1 < (j : ℝ) + 1}

def fullRegion (lambda : ℝ) (f : Path) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 < z.2 ∧ z.2 < surface lambda f z.1}

def stripRegion (lambda : ℝ) (f : Path) (j : ℕ) : Set (ℝ × ℝ) :=
  timeStrip j ∩ fullRegion lambda f

def intensity (lambda : ℝ) (f : Path) : Measure (ℝ × ℝ) := volume.restrict (fullRegion lambda f)

instance (lambda : ℝ) (f : Path) : SigmaFinite (intensity lambda f) := by
  unfold intensity
  infer_instance

theorem measurableSet_timeStrip (j : ℕ) : MeasurableSet (timeStrip j) :=
  (measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_const)

theorem measurableSet_fullRegion (lambda : ℝ) (f : Path) : MeasurableSet (fullRegion lambda f) :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd ((continuous_surface lambda f).measurable.comp measurable_fst)))

theorem measurableSet_stripRegion (lambda : ℝ) (f : Path) (j : ℕ) :
    MeasurableSet (stripRegion lambda f j) :=
  (measurableSet_timeStrip j).inter (measurableSet_fullRegion lambda f)

theorem timeStrip_pairwise_disjoint : Pairwise (fun i j ↦ Disjoint (timeStrip i) (timeStrip j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro z hi hj
  change (i : ℝ) ≤ z.1 ∧ z.1 < (i : ℝ) + 1 at hi
  change (j : ℝ) ≤ z.1 ∧ z.1 < (j : ℝ) + 1 at hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    linarith
  · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    linarith

theorem stripRegion_pairwise_disjoint (lambda : ℝ) (f : Path) :
    Pairwise (fun i j ↦ Disjoint (stripRegion lambda f i) (stripRegion lambda f j)) :=
  fun _i _j hij ↦ (timeStrip_pairwise_disjoint hij).mono inter_subset_left inter_subset_left

theorem fullRegion_eq_union (lambda : ℝ) (f : Path) :
    fullRegion lambda f = ⋃ j : ℕ, stripRegion lambda f j := by
  ext z
  constructor
  · intro hz
    exact mem_iUnion_of_mem ⌊z.1⌋₊ ⟨⟨Nat.floor_le hz.1,Nat.lt_floor_add_one z.1⟩,hz⟩
  · intro hz
    obtain ⟨j,hj⟩ := mem_iUnion.mp hz
    exact hj.2

theorem volume_vertical (t : ℝ) : volume {z : ℝ × ℝ | z.1 = t} = 0 := by
  have he : {z : ℝ × ℝ | z.1 = t} = {t} ×ˢ univ := by ext z; simp
  rw [he,Measure.volume_eq_prod,Measure.prod_prod]
  simp

theorem region_ae_stripRegion (lambda : ℝ) (f : Path) (j : ℕ) :
    region lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f =ᵐ[volume] stripRegion lambda f j := by
  have hae : ∀ᵐ z : ℝ × ℝ ∂volume, z.1 ≠ (j : ℝ) + 1 := by
    apply ae_iff.mpr
    simpa only [not_not] using volume_vertical ((j : ℝ) + 1)
  filter_upwards [hae] with z hz
  apply propext
  change ((j : ℝ) ≤ z.1 ∧ z.1 ≤ (j : ℝ) + 1) ∧
      0 < z.2 ∧ z.2 < surface lambda f z.1 ↔
    ((j : ℝ) ≤ z.1 ∧ z.1 < (j : ℝ) + 1) ∧
      0 ≤ z.1 ∧ 0 < z.2 ∧ z.2 < surface lambda f z.1
  constructor
  · rintro ⟨⟨hl,hr⟩,hp⟩
    exact ⟨⟨hl,lt_of_le_of_ne hr hz⟩,(Nat.cast_nonneg j).trans hl,hp⟩
  · rintro ⟨⟨hl,hr⟩,_,hp⟩
    exact ⟨⟨hl,hr.le⟩,hp⟩

theorem restrict_stripRegion (lambda : ℝ) (f : Path) (j : ℕ) :
    volume.restrict (stripRegion lambda f j) =
      (BrownianUnderGraphPoissonLaw.intensity lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f : Measure (ℝ × ℝ)) :=
  (Measure.restrict_congr_set (region_ae_stripRegion lambda f j)).symm

/-- The genuine full intensity is exactly the countable sum of the actual
finite strip intensities, including every boundary without double mass. -/
theorem intensity_eq_sum (lambda : ℝ) (f : Path) :
    intensity lambda f = Measure.sum (fun j : ℕ ↦
      (BrownianUnderGraphPoissonLaw.intensity lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f : Measure (ℝ × ℝ))) := by
  rw [intensity,fullRegion_eq_union,Measure.restrict_iUnion
    (stripRegion_pairwise_disjoint lambda f) (measurableSet_stripRegion lambda f)]
  congr 1
  funext j
  exact restrict_stripRegion lambda f j

theorem intensity_apply_eq_tsum (lambda : ℝ) (f : Path)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    intensity lambda f A = ∑' j : ℕ,
      volume (A ∩ region lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f) := by
  rw [intensity_eq_sum,Measure.sum_apply _ hA]
  apply tsum_congr
  intro j
  exact Measure.restrict_apply hA

theorem measurableSet_joint_fullRegion : MeasurableSet
    {p : (ℝ × Path) × (ℝ × ℝ) | p.2 ∈ fullRegion p.1.1 p.1.2} := by
  have hs : Measurable (fun p : (ℝ × Path) × (ℝ × ℝ) ↦ surface p.1.1 p.1.2 p.2.1) :=
    continuous_joint_surface.measurable.comp (measurable_fst.prodMk measurable_snd.fst)
  exact (measurableSet_le measurable_const measurable_snd.fst).inter
    ((measurableSet_lt measurable_const measurable_snd.snd).inter
      (measurableSet_lt measurable_snd.snd hs))

theorem measurable_intensity_all_parameters : Measurable
    (fun p : ℝ × Path ↦ intensity p.1 p.2) := by
  apply Measure.measurable_measure.mpr
  intro A hA
  have hm := measurable_measure_prodMk_left (ν := (volume : Measure (ℝ × ℝ)))
    ((hA.preimage measurable_snd).inter measurableSet_joint_fullRegion)
  convert hm using 1
  funext p
  exact Measure.restrict_apply hA

end PerronWright.BrownianFullHorizonSpatialIntensity
