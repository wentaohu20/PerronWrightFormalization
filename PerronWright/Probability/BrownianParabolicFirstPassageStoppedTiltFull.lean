import PerronWright.Probability.BrownianParabolicFirstPassageStoppedTilt
import PerronWright.Probability.BrownianParabolicFirstPassageStrongMarkovFull
import PerronWright.Probability.BrownianFirstPassageZeroDrift

/-! # Actual uncapped negative-level parabolic stopped-path density

True-hit cutoffs increase to the whole stopped law. Actual Brownian and
parabolic hitting finiteness close that monotone-convergence argument;
there is no uniform-integrability or optional-stopping premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicFirstPassageStoppedTiltFull

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassageReflection BrownianFirstPassageStrongMarkov BrownianFirstPassageUncappedLaw
open BrownianParabolicFirstPassageStoppedTilt BrownianParabolicFirstPassageFinite
open BrownianParabolicFirstPassagePastFibers

def actualDriverPassagePast (lambda level : ℝ) (f : Path) : ℝ≥0 × Path :=
  passagePast level (BrownianPathReflectionLaw.driftPath lambda f)

theorem measurable_actualDriverPassagePast (lambda level : ℝ) :
    Measurable (actualDriverPassagePast lambda level) :=
  (measurable_passagePast level).comp (measurable_actual_driftPath lambda)

private theorem cutoff_past_test (level : ℝ) (T : ℝ≥0) (f : Path)
    (Φ : ℝ≥0 × Path → ℝ≥0∞) :
    (if (boundedPast level T f).1 < T then Φ (boundedPast level T f) else 0) =
      if firstPassage level f < (T : ℝ≥0∞) then Φ (passagePast level f) else 0 := by
  have he : cappedTime level T f < T ↔ firstPassage level f < (T : ℝ≥0∞) := by
    simp only [← ENNReal.coe_lt_coe,cappedTime_coe,min_lt_iff,lt_irrefl,or_false]
  by_cases ht : firstPassage level f < (T : ℝ≥0∞)
  · have hc : cappedTime level T f = passageTime level f := by
      unfold cappedTime passageTime
      rw [min_eq_left ht.le]
    change (if cappedTime level T f < T then Φ (boundedPast level T f) else 0) = _
    rw [if_pos (he.mpr ht),if_pos ht]
    unfold boundedPast passagePast
    rw [hc]
  · change (if cappedTime level T f < T then Φ (boundedPast level T f) else 0) = _
    rw [if_neg (mt he.mp ht),if_neg ht]

private theorem lintegral_eq_iSup_hit_cutoffs (τ : Path → ℝ≥0∞) (hτ : Measurable τ)
    (G : Path → ℝ≥0∞) (hG : Measurable G) (hfinite : ∀ᵐ f ∂pathLaw, τ f ≠ ⊤) :
    (∫⁻ f : Path, G f ∂pathLaw) =
      ⨆ n : ℕ, ∫⁻ f : Path, (if τ f < (n : ℝ≥0∞) then G f else 0) ∂pathLaw := by
  calc
    _ = ∫⁻ f : Path, ⨆ n : ℕ, (if τ f < (n : ℝ≥0∞) then G f else 0) ∂pathLaw := by
      apply lintegral_congr_ae
      filter_upwards [hfinite] with f hf
      obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt hf
      apply Eq.symm
      apply le_antisymm
      · apply iSup_le
        intro m
        by_cases hm : τ f < (m : ℝ≥0∞)
        · simpa only [if_pos hm] using (le_refl (G f))
        · simpa only [if_neg hm] using (show (0 : ℝ≥0∞) ≤ G f from zero_le)
      · simpa only [if_pos hn] using
          (le_iSup (fun m : ℕ ↦ if τ f < (m : ℝ≥0∞) then G f else 0) n)
    _ = _ := lintegral_iSup
      (fun n ↦ Measurable.ite (measurableSet_lt hτ measurable_const) hG measurable_const)
      (by
        intro n m hnm f
        by_cases hn : τ f < (n : ℝ≥0∞)
        · have hm : τ f < (m : ℝ≥0∞) := hn.trans_le (Nat.cast_le.mpr hnm)
          simpa only [if_pos hn,if_pos hm] using (le_refl (G f))
        · simp only [if_neg hn]
          exact zero_le)

theorem actual_parabolic_passage_lintegral (lambda level : ℝ) (hlevel : level < 0)
    {Φ : ℝ≥0 × Path → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f : Path, Φ (actualDriverPassagePast lambda level f) ∂pathLaw) =
      ∫⁻ p : ℝ≥0 × Path, stoppedDensity lambda p*Φ p ∂pathLaw.map (passagePast level) := by
  have hdriver : Measurable (fun f : Path ↦ firstPassage level
      (BrownianPathReflectionLaw.driftPath lambda f)) :=
    (measurable_firstPassage level).comp (measurable_actual_driftPath lambda)
  have hd := lintegral_eq_iSup_hit_cutoffs _ hdriver
    (fun f ↦ Φ (actualDriverPassagePast lambda level f))
    (hΦ.comp (measurable_actualDriverPassagePast lambda level))
    (ae_parabolicFirstPassage_ne_top lambda level)
  have hb := lintegral_eq_iSup_hit_cutoffs (firstPassage level) (measurable_firstPassage level)
    (fun f ↦ stoppedDensity lambda (passagePast level f)*Φ (passagePast level f))
    (((measurable_stoppedDensity lambda).mul hΦ).comp (measurable_passagePast level))
    (BrownianFirstPassageZeroDrift.ae_firstPassage_ne_top level hlevel)
  have hm : Measurable (fun p : ℝ≥0 × Path ↦ stoppedDensity lambda p*Φ p) :=
    (measurable_stoppedDensity lambda).mul hΦ
  rw [lintegral_map hm (measurable_passagePast level),hd,hb]
  congr 1
  funext n
  let Ψ : ℝ≥0 × Path → ℝ≥0∞ :=
    fun p ↦ if p.1 < (n : ℝ≥0) then Φ p else 0
  have hΨ : Measurable Ψ := Measurable.ite
    (measurableSet_lt measurable_fst measurable_const) hΦ measurable_const
  have he := actual_parabolic_stoppedPassage_lintegral lambda level (n : ℝ≥0) hΨ
  have hmΨ : Measurable (fun p : ℝ≥0 × Path ↦ stoppedDensity lambda p*Ψ p) :=
    (measurable_stoppedDensity lambda).mul hΨ
  rw [lintegral_map hmΨ (measurable_boundedPast level (n : ℝ≥0))] at he
  have hl : (∫⁻ f : Path, Ψ (actualDriverBoundedPast lambda level (n : ℝ≥0) f) ∂pathLaw) =
      ∫⁻ f : Path, (if firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) <
        (n : ℝ≥0∞) then Φ (actualDriverPassagePast lambda level f) else 0) ∂pathLaw := by
    apply lintegral_congr
    intro f
    simpa only [Ψ,actualDriverBoundedPast,actualDriverPassagePast,ENNReal.coe_natCast] using
      cutoff_past_test level (n : ℝ≥0) (BrownianPathReflectionLaw.driftPath lambda f) Φ
  have hr : (∫⁻ f : Path, stoppedDensity lambda (boundedPast level (n : ℝ≥0) f)*
      Ψ (boundedPast level (n : ℝ≥0) f) ∂pathLaw) =
      ∫⁻ f : Path, (if firstPassage level f < (n : ℝ≥0∞) then
        stoppedDensity lambda (passagePast level f)*Φ (passagePast level f) else 0) ∂pathLaw := by
    apply lintegral_congr
    intro f
    have hc := cutoff_past_test level (n : ℝ≥0) f
      (fun p ↦ stoppedDensity lambda p*Φ p)
    simpa only [Ψ,mul_ite,mul_zero,ENNReal.coe_natCast] using hc
  exact hl.symm.trans (he.trans hr)

theorem actual_parabolic_passage_law (lambda level : ℝ) (hlevel : level < 0) :
    pathLaw.map (actualDriverPassagePast lambda level) =
      (pathLaw.map (passagePast level)).withDensity (stoppedDensity lambda) := by
  apply Measure.ext_of_lintegral
  intro Φ hΦ
  rw [lintegral_map hΦ (measurable_actualDriverPassagePast lambda level),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_stoppedDensity lambda) hΦ]
  exact actual_parabolic_passage_lintegral lambda level hlevel hΦ

theorem lintegral_stoppedDensity_passage_eq_one (lambda level : ℝ) (hlevel : level < 0) :
    (∫⁻ p : ℝ≥0 × Path, stoppedDensity lambda p ∂pathLaw.map (passagePast level)) = 1 := by
  have he := actual_parabolic_passage_lintegral lambda level hlevel (Φ := fun _ ↦ 1) measurable_const
  simpa only [mul_one,lintegral_one,measure_univ] using he.symm

end PerronWright.BrownianParabolicFirstPassageStoppedTiltFull
