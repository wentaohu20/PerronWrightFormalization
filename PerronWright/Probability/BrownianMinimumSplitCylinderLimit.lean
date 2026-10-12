import PerronWright.Probability.BrownianSurvivalWholeCylinderTests
import PerronWright.Probability.BrownianMinimumSplitCandidate
import PerronWright.Probability.BrownianMinimumSplitWindowNonnegativeLimit

/-! # Genuine past/depth integration of whole-future cylinder limits

Both path pieces are retained. Domination is under the actual Brownian
negative-level first-passage source, and is integrable because the literal
candidate weight has already been proved to have finite mass. No joint
minimum-split identity is supplied as a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumSplitCylinderLimit

open BrownianPathLaw BrownianFirstPassageUncappedLaw BrownianFirstPassageEndpointGeometry
open BrownianMinimumSplitCandidate BrownianMinimumFutureEntranceSource BrownianPathDilationLaw
open BrownianSurvivalEntranceScaling BrownianSurvivalWholeCylinderTests
open BrownianMinimumWindowSurvivalBounds ContinuousPathFirstPassage
open ContinuousPathMinimumSplitBandAverage
open BrownianMinimumSplitWindowLevelIntegral

private def finiteEval {m n : ℕ} (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (q : (ℝ≥0 × Path) × (ℝ × Path)) : (ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ)) :=
  ((q.1.1,fun i ↦ q.1.2 (σ i)),q.2.1,fun j ↦ q.2.2 (τ j))

private theorem continuous_finiteEval {m n : ℕ} (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0) :
    Continuous (finiteEval σ τ) :=
  (continuous_fst.fst.prodMk (continuous_pi (fun i ↦ (continuous_eval (σ i)).comp
    continuous_fst.snd))).prodMk (continuous_snd.fst.prodMk
      (continuous_pi (fun j ↦ (continuous_eval (τ j)).comp continuous_snd.snd)))

private def splitTest {m n : ℕ} (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ) :
    ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ :=
  Ψ.compContinuous ⟨finiteEval σ τ,continuous_finiteEval σ τ⟩

private def taggedPast (q : ℝ × Path) : ℝ≥0 × Path := passagePast (-q.1) q.2

private theorem measurable_taggedPast : Measurable taggedPast :=
  measurable_joint_passagePast.comp (measurable_fst.neg.prodMk measurable_snd)

private def pastBase : Measure (ℝ × Path) := (volume.restrict (Ioi (0 : ℝ))).prod pathLaw

private def futureTest {m n : ℕ} (σ : Fin m → ℝ≥0) (_τ : Fin n → ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ)
    (q : ℝ × Path) : (Fin n → ℝ) →ᵇ ℝ := Ψ.compContinuous
  ⟨fun v ↦ (((taggedPast q).1,fun i ↦ (taggedPast q).2 (σ i)),-q.1,v),
    continuous_const.prodMk (continuous_const.prodMk continuous_id)⟩

private def sourceKernel {m n : ℕ} (T : ℝ≥0) (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ)
    (δ : ℝ) (q : ℝ × Path) : ℝ≥0∞ :=
  if (taggedPast q).1 < T then
    (∫⁻ g in survival (-δ) (remainingTime T ((taggedPast q).1 : ℝ)),
      ENNReal.ofReal ((splitTest σ τ Ψ) (taggedPast q,-q.1,g)) ∂pathLaw)/ENNReal.ofReal δ
  else 0

private def limitKernel {m n : ℕ} (T : ℝ≥0) (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ)
    (q : ℝ × Path) : ℝ≥0∞ := sourcePastWeight T q*
  ∫⁻ g, ENNReal.ofReal ((splitTest σ τ Ψ) (sourcePoint T (q,g))) ∂unitSourceLaw

private theorem measurable_sourceKernel {m n : ℕ} (T : ℝ≥0) (σ : Fin m → ℝ≥0)
    (τ : Fin n → ℝ≥0) (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ)
    (δ : ℝ) : Measurable (sourceKernel T σ τ Ψ δ) := by
  have ht : Measurable (fun q : (ℝ × Path) × Path ↦
      (taggedPast q.1,-q.1.1,q.2)) :=
    (measurable_taggedPast.comp measurable_fst).prodMk
      (measurable_fst.fst.neg.prodMk measurable_snd)
  have hm := ((splitTest σ τ Ψ).continuous.measurable.comp ht).ennreal_ofReal
  have hp : Measurable (fun q : (ℝ × Path) × Path ↦
      (((taggedPast q.1).1 : ℝ),q.2)) :=
    (NNReal.continuous_coe.measurable.comp
      (measurable_taggedPast.comp measurable_fst).fst).prodMk measurable_snd
  let S : Set ((ℝ × Path) × Path) :=
    {q | q.2 ∈ survival (-δ) (remainingTime T ((taggedPast q.1).1 : ℝ))}
  have hS : MeasurableSet S := by
    have h := (BrownianFirstPassageMinimumWindowGeometry.measurableSet_futureSurvival δ T).preimage hp
    simpa only [S,BrownianFirstPassageMinimumWindowGeometry.futureSurvival,
      Set.preimage_ofPred_eq] using h
  have hi := (hm.indicator hS).lintegral_prod_right' (ν := pathLaw)
  simp only [Function.comp_def] at hi
  have he : (fun q : ℝ × Path ↦ ∫⁻ g,
      S.indicator (fun q ↦ ENNReal.ofReal ((splitTest σ τ Ψ) (taggedPast q.1,-q.1.1,q.2))) (q,g)
      ∂pathLaw) = fun q ↦ ∫⁻ g in survival (-δ) (remainingTime T ((taggedPast q).1 : ℝ)),
        ENNReal.ofReal ((splitTest σ τ Ψ) (taggedPast q,-q.1,g)) ∂pathLaw := by
    funext q
    rw [← lintegral_indicator (measurableSet_survival (-δ) (remainingTime T ((taggedPast q).1 : ℝ)))]
    rfl
  rw [he] at hi
  exact Measurable.ite (measurableSet_lt measurable_taggedPast.fst measurable_const)
    (hi.div_const _) measurable_const

private theorem weight_ne_top (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ q, sourcePastWeight T q ∂pastBase) ≠ ⊤ := by
  let := candidateLaw_isFinite T hT
  have h := measure_ne_top (candidateLaw T) univ
  rw [candidateLaw,Measure.map_apply (measurable_sourcePoint T) MeasurableSet.univ,
    preimage_univ] at h
  change ((pastBase.withDensity (sourcePastWeight T)).prod unitSourceLaw) univ ≠ ⊤ at h
  rw [← univ_prod_univ,Measure.prod_prod,
    show unitSourceLaw univ = 1 from measure_univ,mul_one,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at h
  exact h

private theorem sourceKernel_tendsto {m n : ℕ} (T : ℝ≥0) (σ : Fin m → ℝ≥0)
    (τ : Fin n → ℝ≥0) (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ)
    (hΨ : ∀ v, 0 ≤ Ψ v) (q : ℝ × Path) :
    Tendsto (fun δ : ℝ ↦ sourceKernel T σ τ Ψ δ q) (𝓝[>] 0)
      (𝓝 (limitKernel T σ τ Ψ q)) := by
  by_cases hp : (taggedPast q).1 < T
  · have hpR : ((taggedPast q).1 : ℝ) < (T : ℝ) := hp
    have hr : 0 < remainingTime T ((taggedPast q).1 : ℝ) :=
      Real.toNNReal_pos.mpr (sub_pos.mpr hpR)
    have hw : sourcePastWeight T q = ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ENNReal.ofReal (1/Real.sqrt (remainingTime T ((taggedPast q).1 : ℝ) : ℝ)) := by
      change ENNReal.ofReal (Real.sqrt (2/Real.pi))*(if (taggedPast q).1 < T then
        ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-((taggedPast q).1 : ℝ))) else 0) = _
      rw [if_pos hp,remainingTime,Real.coe_toNNReal _ (sub_pos.mpr hpR).le]
    rw [limitKernel,hw]
    have ht := actual_survival_cylinder_tendsto _ hr τ (futureTest σ τ Ψ q) (fun v ↦ hΨ _)
    apply ht.congr
    intro δ
    rw [sourceKernel,if_pos hp,normalizedSurvivalLaw,lintegral_smul_measure,smul_eq_mul,
      div_eq_mul_inv,mul_comm]
    rfl
  · have hw : sourcePastWeight T q = 0 := by
      change ENNReal.ofReal entranceCoefficient*(if (taggedPast q).1 < T then _ else 0) = 0
      rw [if_neg hp,mul_zero]
    simp only [sourceKernel,if_neg hp,limitKernel,hw,zero_mul]
    exact tendsto_const_nhds

private theorem lintegral_limitKernel {m n : ℕ} (T : ℝ≥0) (hT : 0 < T)
    (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ) :
    (∫⁻ q, limitKernel T σ τ Ψ q ∂pastBase) =
      ∫⁻ z, ENNReal.ofReal ((splitTest σ τ Ψ) z) ∂candidateLaw T := by
  let := isFiniteMeasure_withDensity (weight_ne_top T hT)
  have hF := (splitTest σ τ Ψ).continuous.measurable.ennreal_ofReal
  have hi := (hF.comp (measurable_sourcePoint T)).lintegral_prod_right' (ν := unitSourceLaw)
  change _ = ∫⁻ z, ENNReal.ofReal ((splitTest σ τ Ψ) z)
    ∂((pastBase.withDensity (sourcePastWeight T)).prod unitSourceLaw).map (sourcePoint T)
  rw [lintegral_map hF (measurable_sourcePoint T)]
  change _ = ∫⁻ z, ((fun z ↦ ENNReal.ofReal ((splitTest σ τ Ψ) z)) ∘ sourcePoint T) z
    ∂(pastBase.withDensity (sourcePastWeight T)).prod unitSourceLaw
  rw [lintegral_prod _ (hF.comp (measurable_sourcePoint T)).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_sourcePastWeight T) hi]
  rfl

private def majorant {m n : ℕ} (T : ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ) (q : ℝ × Path) : ℝ≥0∞ :=
  (ENNReal.ofReal (‖Ψ‖*BrownianKilledSurvivalMoment.survivalCoefficient)*
    (ENNReal.ofReal entranceCoefficient)⁻¹)*sourcePastWeight T q

private theorem majorant_ne_top {m n : ℕ} (T : ℝ≥0) (hT : 0 < T)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ) :
    (∫⁻ q, majorant T Ψ q ∂pastBase) ≠ ⊤ := by
  change (∫⁻ q, (ENNReal.ofReal (‖Ψ‖*BrownianKilledSurvivalMoment.survivalCoefficient)*
    (ENNReal.ofReal entranceCoefficient)⁻¹)*sourcePastWeight T q ∂pastBase) ≠ ⊤
  rw [lintegral_const_mul _ (measurable_sourcePastWeight T)]
  have hc : ENNReal.ofReal entranceCoefficient ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity))
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr hc)) (weight_ne_top T hT)

private theorem sourceKernel_le_majorant {m n : ℕ} (T : ℝ≥0)
    (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ)
    (δ : ℝ) (hδ : 0 < δ) (q : ℝ × Path) : sourceKernel T σ τ Ψ δ q ≤ majorant T Ψ q := by
  by_cases hp : (taggedPast q).1 < T
  · have hpR : ((taggedPast q).1 : ℝ) < (T : ℝ) := hp
    have hr : 0 < remainingTime T ((taggedPast q).1 : ℝ) :=
      Real.toNNReal_pos.mpr (sub_pos.mpr hpR)
    have hC : 0 ≤ BrownianKilledSurvivalMoment.survivalCoefficient :=
      (zero_le_one : (0 : ℝ) ≤ 1).trans BrownianKilledSurvivalMoment.survivalCoefficient_ge_one
    have hc : ENNReal.ofReal entranceCoefficient ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity))
    have hw : sourcePastWeight T q = ENNReal.ofReal entranceCoefficient*
        ENNReal.ofReal (1/Real.sqrt (remainingTime T ((taggedPast q).1 : ℝ) : ℝ)) := by
      change ENNReal.ofReal entranceCoefficient*(if (taggedPast q).1 < T then
        ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-((taggedPast q).1 : ℝ))) else 0) = _
      rw [if_pos hp,remainingTime,Real.coe_toNNReal _ (sub_pos.mpr hpR).le]
    have htest (g : Path) : ENNReal.ofReal ((splitTest σ τ Ψ) (taggedPast q,-q.1,g)) ≤
        ENNReal.ofReal ‖Ψ‖ := ENNReal.ofReal_le_ofReal
      ((le_abs_self _).trans (Ψ.norm_coe_le_norm _))
    rw [sourceKernel,if_pos hp]
    calc
      _ ≤ ENNReal.ofReal ‖Ψ‖*(pathLaw (survival (-δ)
          (remainingTime T ((taggedPast q).1 : ℝ)))/ENNReal.ofReal δ) :=
        normalized_survival_test_bound δ _ ‖Ψ‖ _ htest
      _ ≤ ENNReal.ofReal ‖Ψ‖*ENNReal.ofReal
          (BrownianKilledSurvivalMoment.survivalCoefficient/
            Real.sqrt (remainingTime T ((taggedPast q).1 : ℝ) : ℝ)) :=
        mul_le_mul' le_rfl (normalized_survival_path_mass_bound δ hδ _ hr)
      _ = ENNReal.ofReal (‖Ψ‖*BrownianKilledSurvivalMoment.survivalCoefficient)*
          ENNReal.ofReal (1/Real.sqrt (remainingTime T ((taggedPast q).1 : ℝ) : ℝ)) := by
        rw [div_eq_mul_one_div,ENNReal.ofReal_mul hC,
          ENNReal.ofReal_mul (norm_nonneg _),mul_assoc]
      _ = majorant T Ψ q := by
        rw [majorant,hw]
        have he := ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top
        calc
          _ = ENNReal.ofReal (‖Ψ‖*BrownianKilledSurvivalMoment.survivalCoefficient)*
              ((ENNReal.ofReal entranceCoefficient)⁻¹*ENNReal.ofReal entranceCoefficient)*
                ENNReal.ofReal (1/Real.sqrt (remainingTime T ((taggedPast q).1 : ℝ) : ℝ)) := by
            rw [he,mul_one]
          _ = _ := by ac_rfl
  · simp only [sourceKernel,if_neg hp]
    exact zero_le

private theorem integrated_source_cylinder_tendsto {m n : ℕ} (T : ℝ≥0) (hT : 0 < T)
    (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ) (hΨ : ∀ v, 0 ≤ Ψ v) :
    Tendsto (fun δ : ℝ ↦ ∫⁻ q, sourceKernel T σ τ Ψ δ q ∂pastBase) (𝓝[>] 0)
      (𝓝 (∫⁻ z, ENNReal.ofReal ((splitTest σ τ Ψ) z) ∂candidateLaw T)) := by
  have hb : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ q ∂pastBase,
      sourceKernel T σ τ Ψ δ q ≤ majorant T Ψ q := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact Eventually.of_forall (sourceKernel_le_majorant T σ τ Ψ δ hδ)
  have ht := tendsto_lintegral_filter_of_dominated_convergence (μ := pastBase) (majorant T Ψ)
    (Eventually.of_forall (measurable_sourceKernel T σ τ Ψ))
    hb
    (majorant_ne_top T hT Ψ) (Eventually.of_forall (sourceKernel_tendsto T σ τ Ψ hΨ))
  rw [lintegral_limitKernel T hT σ τ Ψ] at ht
  exact ht

private def pastKernel {m n : ℕ} (T : ℝ≥0) (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ)
    (δ a : ℝ) (p : ℝ≥0 × Path) : ℝ≥0∞ :=
  ∫⁻ g in survival (-δ) (remainingTime T (p.1 : ℝ)),
    ENNReal.ofReal ((splitTest σ τ Ψ) (p,-a,g)) ∂pathLaw

private theorem measurable_pastKernel {m n : ℕ} (T : ℝ≥0) (σ : Fin m → ℝ≥0)
    (τ : Fin n → ℝ≥0) (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ)
    (δ a : ℝ) : Measurable (pastKernel T σ τ Ψ δ a) := by
  have hm : Measurable (fun q : (ℝ≥0 × Path) × Path ↦
      ENNReal.ofReal ((splitTest σ τ Ψ) (q.1,-a,q.2))) :=
    ((splitTest σ τ Ψ).continuous.measurable.comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).ennreal_ofReal
  have hi := (hm.indicator
    (BrownianFirstPassageMinimumWindowPastFutureLaw.measurableSet_futureSurvival δ T)).lintegral_prod_right'
      (ν := pathLaw)
  convert hi using 1
  funext p
  rw [pastKernel,← lintegral_indicator (measurableSet_survival (-δ) (remainingTime T (p.1 : ℝ)))]
  rfl

private def rawSource {m n : ℕ} (T : ℝ≥0) (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ)
    (δ : ℝ) (q : ℝ × Path) : ℝ≥0∞ :=
  if (taggedPast q).1 < T then pastKernel T σ τ Ψ δ q.1 (taggedPast q) else 0

private theorem measurable_rawSource {m n : ℕ} (T : ℝ≥0) (σ : Fin m → ℝ≥0)
    (τ : Fin n → ℝ≥0) (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ)
    (δ : ℝ) (hδ : 0 < δ) : Measurable (rawSource T σ τ Ψ δ) := by
  have he : rawSource T σ τ Ψ δ = fun q ↦ sourceKernel T σ τ Ψ δ q*ENNReal.ofReal δ := by
    funext q
    by_cases hp : (taggedPast q).1 < T
    · simp only [rawSource,sourceKernel,if_pos hp,pastKernel]
      exact (ENNReal.div_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hδ)
        ENNReal.ofReal_ne_top).symm
    · simp only [rawSource,sourceKernel,if_neg hp,zero_mul]
  rw [he]
  exact (measurable_sourceKernel T σ τ Ψ δ).mul_const _

private theorem integrated_source_eq_product {m n : ℕ} (T : ℝ≥0)
    (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    (∫⁻ q, sourceKernel T σ τ Ψ δ q ∂pastBase) =
      (∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        ∫⁻ g in survival (-δ) (remainingTime T (p.1 : ℝ)),
          ENNReal.ofReal ((splitTest σ τ Ψ) (p,-a,g)) ∂pathLaw
        ∂BrownianFirstPassageMinimumWindowPastFutureLaw.passagePastLaw (-a))/ENNReal.ofReal δ := by
  have hr := measurable_rawSource T σ τ Ψ δ hδ
  have he : sourceKernel T σ τ Ψ δ = fun q ↦ rawSource T σ τ Ψ δ q*(ENNReal.ofReal δ)⁻¹ := by
    funext q
    by_cases hp : (taggedPast q).1 < T
    · simp only [sourceKernel,rawSource,pastKernel,if_pos hp,div_eq_mul_inv]
    · simp only [sourceKernel,rawSource,pastKernel,if_neg hp,zero_mul]
  rw [he,lintegral_mul_const _ hr,← div_eq_mul_inv]
  congr 1
  rw [pastBase,lintegral_prod _ hr.aemeasurable]
  apply lintegral_congr
  intro a
  have hS : MeasurableSet {p : ℝ≥0 × Path | p.1 < T} := measurable_fst measurableSet_Iio
  change _ = ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T}, pastKernel T σ τ Ψ δ a p
    ∂BrownianFirstPassageMinimumWindowPastFutureLaw.passagePastLaw (-a)
  rw [← lintegral_indicator hS,
    BrownianFirstPassageMinimumWindowPastFutureLaw.passagePastLaw,
    lintegral_map ((measurable_pastKernel T σ τ Ψ δ a).indicator hS) (measurable_passagePast (-a))]
  rfl

theorem actual_finite_cylinder_test (T : ℝ≥0) (hT : 0 < T)
    {m n : ℕ} (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ) (hΨ : ∀ v, 0 ≤ Ψ v) :
    (∫⁻ z, ENNReal.ofReal (Ψ ((z.1.1,fun i ↦ z.1.2 (σ i)),z.2.1,fun j ↦ z.2.2 (τ j)))
      ∂pathLaw.map (minimumPoint T)) =
      ∫⁻ z, ENNReal.ofReal (Ψ ((z.1.1,fun i ↦ z.1.2 (σ i)),z.2.1,fun j ↦ z.2.2 (τ j)))
        ∂candidateLaw T := by
  have hF := (splitTest σ τ Ψ).continuous.measurable.ennreal_ofReal
  change (∫⁻ z, ENNReal.ofReal ((splitTest σ τ Ψ) z) ∂pathLaw.map (minimumPoint T)) = _
  rw [lintegral_map hF (measurable_minimumPoint T)]
  have ha := BrownianMinimumSplitWindowNonnegativeLimit.actual_split_past_future_product_limit
    T hT (splitTest σ τ Ψ) (fun z ↦ hΨ _)
  have hc := integrated_source_cylinder_tendsto T hT σ τ Ψ hΨ
  have ha' := ha.congr' (show ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ((∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        ∫⁻ g in survival (-δ) (remainingTime T (p.1 : ℝ)),
          ENNReal.ofReal ((splitTest σ τ Ψ) (p,-a,g)) ∂pathLaw
        ∂BrownianFirstPassageMinimumWindowPastFutureLaw.passagePastLaw (-a))/ENNReal.ofReal δ) =
          ∫⁻ q, sourceKernel T σ τ Ψ δ q ∂pastBase from by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (integrated_source_eq_product T σ τ Ψ δ hδ).symm)
  exact tendsto_nhds_unique ha' hc

theorem actual_finite_cylinder_nnreal_test (T : ℝ≥0) (hT : 0 < T)
    {m n : ℕ} (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ≥0) :
    (∫⁻ z, (Ψ ((z.1.1,fun i ↦ z.1.2 (σ i)),z.2.1,fun j ↦ z.2.2 (τ j)) : ℝ≥0∞)
      ∂pathLaw.map (minimumPoint T)) =
      ∫⁻ z, (Ψ ((z.1.1,fun i ↦ z.1.2 (σ i)),z.2.1,fun j ↦ z.2.2 (τ j)) : ℝ≥0∞)
        ∂candidateLaw T := by
  let G : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ :=
    ⟨⟨fun v ↦ (Ψ v : ℝ),NNReal.continuous_coe.comp Ψ.continuous⟩,Ψ.map_bounded'⟩
  have h := actual_finite_cylinder_test T hT σ τ G (fun v ↦ (Ψ v).coe_nonneg)
  simpa only [G,BoundedContinuousFunction.coe_mk,ENNReal.ofReal_coe_nnreal] using h

end PerronWright.BrownianMinimumSplitCylinderLimit
