import PerronWright.Probability.BrownianMinimumFutureWholeLaw
import PerronWright.Probability.BrownianPathMinimumUnique
import PerronWright.Probability.BrownianFirstPassageZeroDrift

/-! # Strict positivity and actual positive-time return of the entrance source

Unique Brownian prefix minima give positivity at every positive prefix time,
not just at a countable collection of evaluations. The return time is the
literal infimum of strictly positive sublevel times. Its post-unit passage
identity is derived from that hit set, and genuine fresh Brownian future
finiteness is then transferred through the proved whole-path product law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumFutureFirstReturn

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathLeastMinimum
open ContinuousPathIntervalMinimum ContinuousPathFirstPassage
open BrownianMinimumFutureEntranceSource BrownianMinimumFuturePostUnit

private theorem strict_prefix_iff_rational_minima (g : Path) :
    (∀ t : ℝ≥0, 0 < t → t ≤ 1 → 0 < g t) ↔
      ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ 1 →
        0 < intervalMinimum (Real.toNNReal (q : ℝ)) 1 g := by
  constructor
  · intro hg q hq0 hq1
    have hq : Real.toNNReal (q : ℝ) ≤ 1 := Real.toNNReal_le_iff_le_coe.mpr hq1
    obtain ⟨t,ht,he,_⟩ := exists_intervalMinimum _ _ hq g
    rw [he]
    exact hg t ((Real.toNNReal_pos.mpr hq0).trans_le ht.1) ht.2
  · intro hg t ht0 ht1
    obtain ⟨q,hq0,hqt⟩ := exists_rat_btwn (show (0 : ℝ) < (t : ℝ) from ht0)
    have hqt' : Real.toNNReal (q : ℝ) ≤ t := Real.toNNReal_le_iff_le_coe.mpr hqt.le
    have hq1 : (q : ℝ) ≤ 1 := hqt.le.trans ht1
    exact (hg q hq0 hq1).trans_le
      (intervalMinimum_le _ _ (hqt'.trans ht1) g t ⟨hqt',ht1⟩)

theorem measurableSet_strict_positive_unit_prefix :
    MeasurableSet {g : Path | ∀ t : ℝ≥0, 0 < t → t ≤ 1 → 0 < g t} := by
  have hm : MeasurableSet {g : Path | ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ 1 →
      0 < intervalMinimum (Real.toNNReal (q : ℝ)) 1 g} := by
    have hq (q : ℚ) : MeasurableSet {g : Path | 0 < (q : ℝ) → (q : ℝ) ≤ 1 →
        0 < intervalMinimum (Real.toNNReal (q : ℝ)) 1 g} := by
      by_cases hq0 : 0 < (q : ℝ)
      · by_cases hq1 : (q : ℝ) ≤ 1
        · simpa only [hq0,hq1,true_implies] using
            measurableSet_lt measurable_const (continuous_intervalMinimum _ _).measurable
        · simp only [hq0,hq1,true_implies,false_implies,Set.ofPred_true]
          exact MeasurableSet.univ
      · simp only [hq0,false_implies,Set.ofPred_true]
        exact MeasurableSet.univ
    simpa only [Set.ofPred_forall] using MeasurableSet.iInter hq
  have he : {g : Path | ∀ t : ℝ≥0, 0 < t → t ≤ 1 → 0 < g t} =
      {g : Path | ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ 1 →
        0 < intervalMinimum (Real.toNNReal (q : ℝ)) 1 g} :=
    Set.ext (fun g ↦ strict_prefix_iff_rational_minima g)
  rw [he]
  exact hm

/-- Almost surely the actual rescaled post-minimum path is strictly positive
at every positive time up to and including its unit endpoint. -/
theorem ae_unitMinimumFuture_strict_positive_prefix :
    ∀ᵐ f : Path ∂pathLaw, ∀ t : ℝ≥0, 0 < t → t ≤ 1 → 0 < unitMinimumFuture f t := by
  filter_upwards [BrownianPathMinimumUnique.ae_unique_minimum 1,ae_remainingDuration_pos]
    with f hf hr
  intro t ht0 ht1
  let u := leastMinimizer 1 f+remainingDuration f*t
  have hu1 : u ≤ 1 := by
    calc
      _ ≤ leastMinimizer 1 f+remainingDuration f*1 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left ht1 bot_le)
      _ = 1 := by
        rw [mul_one,remainingDuration,add_tsub_cancel_of_le (leastMinimizer_le_time 1 f)]
  have hlu : leastMinimizer 1 f < u :=
    lt_add_of_pos_right _ (mul_pos hr ht0)
  have hm : minimumValue 1 f < f u :=
    lt_of_le_of_ne (minimumValue_le 1 f u hu1) (by
      intro he
      exact hlu.ne' (hf u hu1 he.symm))
  rw [unitMinimumFuture_eval]
  exact div_pos (sub_pos.mpr hm) (Real.sqrt_pos.mpr (show 0 < (remainingDuration f : ℝ) from hr))

theorem ae_unitSourceLaw_strict_positive_prefix :
    ∀ᵐ g : Path ∂unitSourceLaw, ∀ t : ℝ≥0, 0 < t → t ≤ 1 → 0 < g t :=
  (ae_map_iff measurable_unitMinimumFuture.aemeasurable
    measurableSet_strict_positive_unit_prefix).mpr ae_unitMinimumFuture_strict_positive_prefix

theorem ae_unitSourceLaw_endpoint_pos : ∀ᵐ g : Path ∂unitSourceLaw, 0 < g 1 :=
  ae_unitSourceLaw_strict_positive_prefix.mono (fun _ hg ↦ hg 1 zero_lt_one le_rfl)

/-- Unlike first passage, the literal return excludes the initial time.
The infimum is taken in ENNReal, so an empty positive-time hit set has
return time infinity without a separate convention. -/
def firstReturnZero (g : Path) : ℝ≥0∞ :=
  sInf ((fun t : ℝ≥0 ↦ (t : ℝ≥0∞)) '' {t : ℝ≥0 | 0 < t ∧ g t ≤ 0})

theorem before_firstReturnZero (g : Path) (t : ℝ≥0) (ht : 0 < t)
    (hbefore : (t : ℝ≥0∞) < firstReturnZero g) : 0 < g t := by
  apply lt_of_not_ge
  intro hgt
  have hle : firstReturnZero g ≤ (t : ℝ≥0∞) := sInf_le ⟨t,⟨ht,hgt⟩,rfl⟩
  exact (not_le_of_gt hbefore) hle

/-- Strict prefix positivity identifies the literal positive-time hit-set
infimum with the actual post-unit negative-level passage, including infinity. -/
theorem firstReturnZero_eq_post_unit_passage (g : Path)
    (hg : ∀ t : ℝ≥0, 0 < t → t ≤ 1 → 0 < g t) :
    firstReturnZero g = 1+firstPassage (-g 1) (futurePath 1 g) := by
  apply le_antisymm
  · by_cases hfin : firstPassage (-g 1) (futurePath 1 g) = ⊤
    · rw [hfin,add_top]
      exact le_top
    · let τ := (firstPassage (-g 1) (futurePath 1 g)).toNNReal
      have hh := firstPassage_attained (-g 1) (futurePath 1 g) hfin
      have hhit : g (1+τ) ≤ 0 := by
        rw [futurePath_eval] at hh
        change g (1+τ)-g 1 ≤ -g 1 at hh
        linarith
      have hpos : 0 < (1 : ℝ≥0)+τ := add_pos_of_pos_of_nonneg zero_lt_one bot_le
      have hle : firstReturnZero g ≤ ((1+τ : ℝ≥0) : ℝ≥0∞) :=
        sInf_le ⟨1+τ,⟨hpos,hhit⟩,rfl⟩
      simpa only [ENNReal.coe_add,ENNReal.coe_one,τ,ENNReal.coe_toNNReal hfin] using hle
  · apply le_sInf
    rintro x ⟨t,⟨ht0,hgt⟩,rfl⟩
    have ht1 : 1 < t := lt_of_not_ge (fun ht ↦ (not_le_of_gt (hg t ht0 ht)) hgt)
    have hh : firstPassage (-g 1) (futurePath 1 g) ≤ ((t-1 : ℝ≥0) : ℝ≥0∞) := by
      apply (firstPassage_le_iff (-g 1) (futurePath 1 g) (t-1)).mpr
      refine ⟨t-1,le_rfl,?_⟩
      rw [futurePath_eval,add_tsub_cancel_of_le ht1.le]
      linarith
    calc
      _ ≤ (1 : ℝ≥0∞)+((t-1 : ℝ≥0) : ℝ≥0∞) := add_le_add le_rfl hh
      _ = (t : ℝ≥0∞) := by
        rw [← ENNReal.coe_one,← ENNReal.coe_add,add_tsub_cancel_of_le ht1.le]

theorem ae_unitSourceLaw_firstReturn_eq :
    ∀ᵐ g : Path ∂unitSourceLaw,
      firstReturnZero g = 1+firstPassage (-g 1) (futurePath 1 g) :=
  ae_unitSourceLaw_strict_positive_prefix.mono
    (fun g hg ↦ firstReturnZero_eq_post_unit_passage g hg)

/-- Finiteness is proved using the actual prefix/fresh-Brownian product law.
The negative level is the genuine random prefix endpoint, not a fixed value. -/
theorem ae_unitSourceLaw_post_unit_passage_finite :
    ∀ᵐ g : Path ∂unitSourceLaw, firstPassage (-g 1) (futurePath 1 g) ≠ ⊤ := by
  let μ := unitSourceLaw.map (pastPath 1)
  let : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (measurable_pastPath 1).aemeasurable
  have hp : ∀ᵐ p : Path ∂μ, 0 < p 1 := by
    apply (ae_map_iff (measurable_pastPath 1).aemeasurable
      (measurableSet_lt measurable_const (continuous_eval 1).measurable)).mpr
    simpa only [pastPath_eval,min_self] using ae_unitSourceLaw_endpoint_pos
  have hm : Measurable (fun z : Path × Path ↦ firstPassage (-z.1 1) z.2) :=
    measurable_joint_firstPassage.comp
      (((continuous_eval 1).measurable.comp measurable_fst).neg.prodMk measurable_snd)
  have hprod : ∀ᵐ z : Path × Path ∂μ.prod pathLaw, firstPassage (-z.1 1) z.2 ≠ ⊤ := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_eq_fun hm measurable_const).compl)).mpr
    filter_upwards [hp] with p hpos
    exact BrownianFirstPassageZeroDrift.ae_firstPassage_ne_top (-p 1) (neg_neg_of_pos hpos)
  change ∀ᵐ z : Path × Path ∂(unitSourceLaw.map (pastPath 1)).prod pathLaw,
    firstPassage (-z.1 1) z.2 ≠ ⊤ at hprod
  rw [← actual_source_past_future_jointLaw] at hprod
  have h := ae_of_ae_map
    ((measurable_pastPath 1).prodMk (measurable_futurePath 1)).aemeasurable hprod
  simpa only [pastPath_eval,min_self] using h

theorem ae_unitSourceLaw_firstReturn_finite :
    ∀ᵐ g : Path ∂unitSourceLaw, firstReturnZero g ≠ ⊤ := by
  filter_upwards [ae_unitSourceLaw_firstReturn_eq,ae_unitSourceLaw_post_unit_passage_finite]
    with g he hfin
  rw [he]
  exact ENNReal.add_ne_top.mpr ⟨by norm_num,hfin⟩

theorem aemeasurable_firstReturnZero : AEMeasurable firstReturnZero unitSourceLaw := by
  have hm : Measurable (fun g : Path ↦ (1 : ℝ≥0∞)+firstPassage (-g 1) (futurePath 1 g)) :=
    measurable_const.add (measurable_joint_firstPassage.comp
      ((continuous_eval 1).measurable.neg.prodMk (measurable_futurePath 1)))
  exact hm.aemeasurable.congr (ae_unitSourceLaw_firstReturn_eq.mono (fun _ he ↦ he.symm))

theorem ae_unitSourceLaw_firstReturn_gt_one :
    ∀ᵐ g : Path ∂unitSourceLaw, (1 : ℝ≥0∞) < firstReturnZero g := by
  filter_upwards [ae_unitSourceLaw_endpoint_pos,ae_unitSourceLaw_firstReturn_eq] with g hpos he
  have hpass : firstPassage (-g 1) (futurePath 1 g) ≠ 0 := by
    intro hz
    obtain ⟨t,ht,hh⟩ := (firstPassage_le_iff (-g 1) (futurePath 1 g) 0).mp (hz ▸ le_rfl)
    have ht0 : t = 0 := le_antisymm ht bot_le
    subst t
    rw [futurePath_eval,add_zero,sub_self] at hh
    linarith
  rw [he]
  exact ENNReal.lt_add_right (by norm_num) hpass

theorem ae_unitSourceLaw_firstReturn_exact_zero :
    ∀ᵐ g : Path ∂unitSourceLaw, g (firstReturnZero g).toNNReal = 0 := by
  filter_upwards [ae_unitSourceLaw_endpoint_pos,ae_unitSourceLaw_firstReturn_eq,
    ae_unitSourceLaw_post_unit_passage_finite] with g hpos he hfin
  have hh := firstPassage_exact_level (-g 1) (futurePath 1 g) (by
    rw [futurePath_eval,add_zero,sub_self]
    exact neg_neg_of_pos hpos) hfin
  rw [he,ENNReal.toNNReal_add (by norm_num) hfin,ENNReal.toNNReal_one]
  rw [futurePath_eval] at hh
  linarith

end PerronWright.BrownianMinimumFutureFirstReturn
