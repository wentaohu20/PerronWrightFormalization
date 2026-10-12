import PerronWright.Probability.FullHorizonExcursionEndpoints
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Literal excursion occupation and the genuine length-biased section

The connected positivity components have their proved nonrepeating rational
section. A time in one component has exactly its actual endpoints. Joint
membership is measurable by rational open intervals, so the actual occupation
test is measurable without assuming an excursion enumeration or a moment.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FullHorizonExcursionOccupation

open BrownianPathLaw FullHorizonExcursionComponents FullHorizonExcursionSection
open FullHorizonExcursionEndpoints

theorem endpoints_eq_of_component_mem {g : Path} {q t : ℝ}
    (ht : t ∈ component g q) :
    leftEndpoint t g = leftEndpoint q g ∧ rightEndpoint t g = rightEndpoint q g ∧
      length t g = length q g := by
  have hq := (component_nonempty_iff g q).mp ⟨t,ht⟩
  have ha := component_subset g q ht
  have he := component_eq_of_mem ht
  have hl : leftEndpoint t g = leftEndpoint q g := by
    simp only [leftEndpoint,if_pos hq,if_pos ha,he]
  have hr : rightEndpoint t g = rightEndpoint q g := by
    simp only [rightEndpoint,if_pos hq,if_pos ha,he]
  exact ⟨hl,hr,by simp only [length,hl,hr]⟩

private theorem mem_component_iff_rat_bounds (g : Path) (q t : ℝ) :
    t ∈ component g q ↔ ∃ a b : ℚ,
      (a : ℝ) ∈ component g q ∧ (b : ℝ) ∈ component g q ∧ t ∈ Ioo (a : ℝ) (b : ℝ) := by
  constructor
  · intro ht
    obtain ⟨l,u,htu,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp ((isOpen_component g q).mem_nhds ht)
    obtain ⟨a,hla,hat⟩ := exists_rat_btwn htu.1
    obtain ⟨b,htb,hbu⟩ := exists_rat_btwn htu.2
    exact ⟨a,b,hsub ⟨hla,hat.trans htu.2⟩,hsub ⟨htu.1.trans htb,hbu⟩,hat,htb⟩
  · rintro ⟨a,b,ha,hb,hat,htb⟩
    exact (component_ordConnected g q).uIcc_subset ha hb
      (mem_uIcc.mpr (Or.inl ⟨hat.le,htb.le⟩))

theorem measurableSet_joint_componentMembership (q : ℝ) :
    MeasurableSet {p : Path × ℝ | p.2 ∈ component p.1 q} := by
  have hm : MeasurableSet (⋃ a : ℚ, ⋃ b : ℚ,
      {p : Path × ℝ | (a : ℝ) ∈ component p.1 q ∧
        (b : ℝ) ∈ component p.1 q ∧ p.2 ∈ Ioo (a : ℝ) (b : ℝ)}) := by
    apply MeasurableSet.iUnion
    intro a
    apply MeasurableSet.iUnion
    intro b
    exact ((measurableSet_componentMembership q (a : ℝ)).preimage measurable_fst).inter
      (((measurableSet_componentMembership q (b : ℝ)).preimage measurable_fst).inter
        (measurableSet_Ioo.preimage measurable_snd))
  convert hm using 1
  ext p
  simp only [mem_ofPred_eq,mem_iUnion]
  exact mem_component_iff_rat_bounds p.1 q p.2

def occupation (H : (Path × ℝ × ℝ) → ℝ≥0∞) (f g : Path) (t : ℝ) : ℝ≥0∞ :=
  if t ∈ positiveSet g then H (f,leftEndpoint t g,length t g) else 0

theorem occupation_eq_representative_sum (H : (Path × ℝ × ℝ) → ℝ≥0∞)
    (f g : Path) (t : ℝ) :
    occupation H f g t = ∑' q : ℚ,
      if Representative g q then
        (component g (q : ℝ)).indicator (fun _ ↦ H (f,leftEndpoint (q : ℝ) g,length (q : ℝ) g)) t
      else 0 := by
  by_cases ht : t ∈ positiveSet g
  · obtain ⟨q,hq,he⟩ := exists_representative ht
    have hqt : t ∈ component g (q : ℝ) := he.symm ▸ mem_component_self ht
    have hz (r : ℚ) (hrq : r ≠ q) :
        (if Representative g r then
          (component g (r : ℝ)).indicator (fun _ ↦ H (f,leftEndpoint (r : ℝ) g,length (r : ℝ) g)) t
        else 0) = 0 := by
      by_cases hr : Representative g r
      · have hrt : t ∉ component g (r : ℝ) := by
          intro hrt
          exact (Set.disjoint_left.mp (representative_components_disjoint hr hq hrq)) hrt hqt
        simp only [if_pos hr,indicator_of_notMem hrt]
      · simp only [if_neg hr]
    rw [tsum_eq_single q hz]
    have hep := endpoints_eq_of_component_mem hqt
    simp only [occupation,if_pos ht,if_pos hq,indicator_of_mem hqt,hep.1,hep.2.2]
  · have hz (q : ℚ) :
        (if Representative g q then
          (component g (q : ℝ)).indicator (fun _ ↦ H (f,leftEndpoint (q : ℝ) g,length (q : ℝ) g)) t
        else 0) = 0 := by
      by_cases hq : Representative g q
      · have hqt : t ∉ component g (q : ℝ) := fun h ↦ ht (component_subset g (q : ℝ) h)
        simp only [if_pos hq,indicator_of_notMem hqt]
      · simp only [if_neg hq]
    simp only [occupation,if_neg ht,hz,tsum_zero]

theorem measurable_joint_occupation (H : (Path × ℝ × ℝ) → ℝ≥0∞) (hH : Measurable H) :
    Measurable (fun p : Path × (Path × ℝ) ↦ occupation H p.1 p.2.1 p.2.2) := by
  have hm (q : ℚ) : Measurable (fun p : Path × (Path × ℝ) ↦
      if Representative p.2.1 q then
        (component p.2.1 (q : ℝ)).indicator
          (fun _ ↦ H (p.1,leftEndpoint (q : ℝ) p.2.1,length (q : ℝ) p.2.1)) p.2.2
      else 0) := by
    have hrep : MeasurableSet {p : Path × (Path × ℝ) | Representative p.2.1 q} :=
      (measurableSet_representative q).preimage measurable_snd.fst
    have hmem : MeasurableSet {p : Path × (Path × ℝ) | p.2.2 ∈ component p.2.1 (q : ℝ)} :=
      (measurableSet_joint_componentMembership (q : ℝ)).preimage measurable_snd
    have hmark : Measurable (fun p : Path × (Path × ℝ) ↦
        H (p.1,leftEndpoint (q : ℝ) p.2.1,length (q : ℝ) p.2.1)) := by
      have hmap : Measurable (fun p : Path × (Path × ℝ) ↦
          (p.1,leftEndpoint (q : ℝ) p.2.1,length (q : ℝ) p.2.1)) :=
        measurable_fst.prodMk (((measurable_leftEndpoint (q : ℝ)).comp measurable_snd.fst).prodMk
          ((measurable_length (q : ℝ)).comp measurable_snd.fst))
      exact hH.comp hmap
    simpa only [Set.indicator_apply] using
      Measurable.ite hrep (Measurable.ite hmem hmark measurable_const) measurable_const
  simpa only [occupation_eq_representative_sum] using Measurable.tsum hm

theorem lintegral_occupation_eq_length_sum (H : (Path × ℝ × ℝ) → ℝ≥0∞)
    (f g : Path) (hb : ∀ q : ℚ, BddAbove (component g (q : ℝ))) :
    (∫⁻ t : ℝ, occupation H f g t) = ∑' q : ℚ,
      if Representative g q then ENNReal.ofReal (length (q : ℝ) g)*
        H (f,leftEndpoint (q : ℝ) g,length (q : ℝ) g) else 0 := by
  simp_rw [occupation_eq_representative_sum]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro q
    by_cases hq : Representative g q
    · simp only [if_pos hq]
      rw [lintegral_indicator (isOpen_component g (q : ℝ)).measurableSet,
        lintegral_const,component_eq_Ioo hq.1 (hb q),
        Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioo]
      unfold length
      exact mul_comm _ _
    · simp only [if_neg hq,lintegral_zero]
  · intro q
    by_cases hq : Representative g q
    · simp only [if_pos hq]
      exact ((measurable_const : Measurable (fun _t : ℝ ↦
        H (f,leftEndpoint (q : ℝ) g,length (q : ℝ) g))).indicator
          (isOpen_component g (q : ℝ)).measurableSet).aemeasurable
    · simp only [if_neg hq]
      exact measurable_const.aemeasurable

end PerronWright.FullHorizonExcursionOccupation
