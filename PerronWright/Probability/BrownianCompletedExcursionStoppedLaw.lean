import PerronWright.Probability.BrownianCompletedExcursionCandidate
import PerronWright.Probability.BrownianCompletedExcursionPrefixReturnLaw
import PerronWright.Probability.BrownianCompletedExcursionStoppedObservations
import PerronWright.Probability.ContinuousPathPositiveReturnMeasurable
import PerronWright.Probability.BrownianStoppedTimeOrderedSampling
import PerronWright.Probability.BrownianCompletedExcursionObservationTimes
import PerronWright.Probability.BrownianCompletedExcursionMixedReturnLaw

/-! # Identification of the actual completed stopped path and lifetime

Finite ordered stopped observations will be compared on the literal
lifetime strata. The supplied entrance path measure is a constructed law;
no conditional excursion-shape identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BigOperators BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedExcursionStoppedLaw

open BrownianPathLaw BrownianPathDilationLaw BrownianPathIndependentIncrements
open BrownianMinimumFutureEntranceSource BrownianMinimumFutureFirstReturn
open BrownianMinimumFutureReturnPathGeometry BrownianCompletedExcursionCandidate
open BrownianCompletedExcursionStoppedObservations BrownianStoppedTimePathSampling
open BrownianCompletedExcursionObservationTimes BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianCompletedExcursionPrefixReturnLaw BrownianCompletedExcursionMixedReturnLaw
open BrownianEntranceKilledChainConcatenation
open ContinuousPathPositiveReturnMeasurable

private theorem ae_actual_tag_gt_one :
    ∀ᵐ g : Path ∂unitSourceLaw, 1 < (returnTaggedPast g).1 := by
  filter_upwards [ae_unitSourceLaw_firstReturn_gt_one,ae_unitSourceLaw_firstReturn_finite] with g hg hf
  change 1 < (firstReturnZero g).toNNReal
  rw [← ENNReal.coe_lt_coe,ENNReal.coe_toNNReal hf,ENNReal.coe_one]
  exact hg

private theorem dilation_initial_zero (T : ℝ≥0) (e : Path) (he : e 0 = 0) :
    brownianDilation T e 0 = 0 := by
  change Real.sqrt (T : ℝ)*e ((0 : ℝ≥0)/T) = 0
  rw [zero_div,he,mul_zero]

private theorem dilation_stopped_zero (T : ℝ≥0) (hT : 0 < T) (e : Path)
    (he : ∀ t, (1 : ℝ≥0) ≤ t → e t = 0) :
    ∀ t, T ≤ t → brownianDilation T e t = 0 := by
  intro t ht
  change Real.sqrt (T : ℝ)*e (t/T) = 0
  rw [he (t/T) ((one_le_div₀ hT).mpr ht),mul_zero]

private theorem stopped_sample_zeroFill (N : ℕ) (times : Fin N → ℝ≥0) (ζ : ℝ≥0)
    (k : Fin (N+1)) (hζ : ζ ∈ lifetimeStratum N times k)
    (g : Path) (hg : ∀ t, ζ ≤ t → g t = 0) :
    (fun i : Fin N ↦ g (times i)) =
      zeroFill N k (fun j : Fin k.val ↦ g (times ⟨j.val,by have h := k.isLt; omega⟩)) := by
  funext i
  by_cases hi : i.val < k.val
  · simp only [zeroFill,dif_pos hi]
  · simp only [zeroFill,dif_neg hi]
    exact hg (times i) (le_of_not_gt (fun h ↦ hi ((hζ i).mp h)))

private def stratumTest (N : ℕ) (times : Fin N → ℝ≥0) (k : Fin (N+1))
    (Φ : ℝ≥0 × (Fin N → ℝ) → ℝ≥0∞) (q : ℝ≥0 × (Fin k.val → ℝ)) : ℝ≥0∞ :=
  if q.1 ∈ lifetimeStratum N times k then Φ (q.1,zeroFill N k q.2) else 0

private theorem measurable_stratumTest (N : ℕ) (times : Fin N → ℝ≥0) (k : Fin (N+1))
    (Φ : ℝ≥0 × (Fin N → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) : Measurable (stratumTest N times k Φ) := by
  have hs : MeasurableSet {q : ℝ≥0 × (Fin k.val → ℝ) | q.1 ∈ lifetimeStratum N times k} :=
    measurable_fst (measurableSet_lifetimeStratum N times k)
  exact (hΦ.comp (measurable_fst.prodMk ((continuous_zeroFill N k).measurable.comp measurable_snd))).ite hs measurable_const

private theorem source_stratum_zeroFill (N : ℕ) (times : Fin N → ℝ≥0) (k : Fin (N+1))
    (Φ : ℝ≥0 × (Fin N → ℝ) → ℝ≥0∞) :
    (∫⁻ g : Path, if (returnTaggedPast g).1 ∈ lifetimeStratum N times k then
      Φ (sample times (returnTaggedPast g)) else 0 ∂unitSourceLaw) =
      ∫⁻ g : Path, stratumTest N times k Φ ((returnTaggedPast g).1,
        fun i : Fin k.val ↦ g (times ⟨i.val,by have h := k.isLt; omega⟩)) ∂unitSourceLaw := by
  apply lintegral_congr_ae
  filter_upwards [ae_returnTaggedPast_tuple_zeroFill N times] with g hg
  by_cases hs : (returnTaggedPast g).1 ∈ lifetimeStratum N times k
  · simp only [if_pos hs,stratumTest,sample,hg k hs]
  · simp only [if_neg hs,stratumTest]

private theorem candidate_stratum_zeroFill (N : ℕ) (times : Fin N → ℝ≥0) (k : Fin (N+1))
    (Φ : ℝ≥0 × (Fin N → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ q : ℝ≥0 × Path, if q.1 ∈ lifetimeStratum N times k then Φ (sample times q) else 0 ∂candidateLaw) =
      ∫⁻ ζ : ℝ, BrownianMinimumFutureReturnDensity.returnDensity ζ *
        (∫⁻ e : Path, stratumTest N times k Φ (Real.toNNReal ζ,
          fun i : Fin k.val ↦ brownianDilation (Real.toNNReal ζ) e (times ⟨i.val,by have h := k.isLt; omega⟩))
            ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
  have hs : MeasurableSet {q : ℝ≥0 × Path | q.1 ∈ lifetimeStratum N times k} :=
    measurable_fst (measurableSet_lifetimeStratum N times k)
  have htest : Measurable (fun q : ℝ≥0 × Path ↦
      if q.1 ∈ lifetimeStratum N times k then Φ (sample times q) else 0) :=
    (hΦ.comp (continuous_sample times).measurable).ite hs measurable_const
  rw [lintegral_candidateLaw _ htest]
  apply lintegral_congr
  intro ζ
  by_cases hζ : 1 < ζ
  · congr 1
    apply lintegral_congr_ae
    filter_upwards [BrownianEntranceContinuousRealization.ae_pathLaw_stopped_zero 1 zero_lt_one] with e he
    have hp : 0 < Real.toNNReal ζ := Real.toNNReal_pos.mpr (lt_trans (by norm_num) hζ)
    have hz := dilation_stopped_zero (Real.toNNReal ζ) hp e he
    by_cases hmem : Real.toNNReal ζ ∈ lifetimeStratum N times k
    · rw [if_pos hmem]
      simp only [stratumTest,if_pos hmem,sample]
      rw [stopped_sample_zeroFill N times (Real.toNNReal ζ) k hmem _ hz]
    · simp only [stratumTest,if_neg hmem]
  · have hd : BrownianMinimumFutureReturnDensity.returnDensity ζ = 0 := by
      simp only [BrownianMinimumFutureReturnDensity.returnDensity,
        indicator_of_notMem (show ζ ∉ Ioi (1 : ℝ) from hζ),ENNReal.ofReal_zero]
    simp only [hd,zero_mul]

private theorem small_stratum_empty (N : ℕ) (times : Fin N → ℝ≥0) (k : Fin (N+1))
    (i : Fin N) (hone : times i = 1) (hsmall : k.val ≤ i.val)
    (ζ : ℝ≥0) (hζ : 1 < ζ) : ζ ∉ lifetimeStratum N times k := by
  intro hmem
  have hi : i.val < k.val := (hmem i).mp (hone ▸ hζ)
  omega

private theorem small_stratum_equal (N : ℕ) (times : Fin N → ℝ≥0) (k : Fin (N+1))
    (i : Fin N) (hone : times i = 1) (hsmall : k.val ≤ i.val)
    (Φ : ℝ≥0 × (Fin N → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ g : Path, if (returnTaggedPast g).1 ∈ lifetimeStratum N times k then
      Φ (sample times (returnTaggedPast g)) else 0 ∂unitSourceLaw) =
      ∫⁻ q : ℝ≥0 × Path, if q.1 ∈ lifetimeStratum N times k then Φ (sample times q) else 0 ∂candidateLaw := by
  have hsource : (∫⁻ g : Path, if (returnTaggedPast g).1 ∈ lifetimeStratum N times k then
      Φ (sample times (returnTaggedPast g)) else 0 ∂unitSourceLaw) = 0 := by
    calc
      _ = ∫⁻ g : Path, (0 : ℝ≥0∞) ∂unitSourceLaw := by
        apply lintegral_congr_ae
        filter_upwards [ae_actual_tag_gt_one] with g hg
        exact if_neg (small_stratum_empty N times k i hone hsmall _ hg)
      _ = 0 := lintegral_zero
  rw [hsource,candidate_stratum_zeroFill N times k Φ hΦ]
  symm
  rw [← lintegral_zero (μ := (volume : Measure ℝ))]
  apply lintegral_congr
  intro ζ
  by_cases hζ : 1 < ζ
  · have hp : 1 < Real.toNNReal ζ := by
      exact_mod_cast (show (1 : ℝ) < (Real.toNNReal ζ : ℝ) by
        rw [Real.coe_toNNReal _ (lt_trans (by norm_num) hζ).le]; exact hζ)
    have hempty := small_stratum_empty N times k i hone hsmall _ hp
    simp only [stratumTest,if_neg hempty,lintegral_zero,mul_zero]
  · have hd : BrownianMinimumFutureReturnDensity.returnDensity ζ = 0 := by
      simp only [BrownianMinimumFutureReturnDensity.returnDensity,
        indicator_of_notMem (show ζ ∉ Ioi (1 : ℝ) from hζ),ENNReal.ofReal_zero]
    simp only [hd,zero_mul]

private theorem measurable_cons_zero (n : ℕ) :
    Measurable (fun v : Fin n → ℝ ↦ (Fin.cons 0 v : Fin (n+1) → ℝ)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [Fin.cons_zero]
    exact measurable_const
  · simpa only [Fin.cons_succ] using (measurable_pi_apply j : Measurable (fun v : Fin n → ℝ ↦ v j))

private theorem prefix_stratum_equal (N k : ℕ) (times : Fin N → ℝ≥0)
    (hk : k+2 ≤ N) (ht : StrictMono times) (hzero : times ⟨0,by omega⟩ = 0)
    (hone : times ⟨k+1,by omega⟩ = 1)
    (Φ : ℝ≥0 × (Fin N → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ g : Path, if (returnTaggedPast g).1 ∈ lifetimeStratum N times ⟨k+2,by omega⟩ then
      Φ (sample times (returnTaggedPast g)) else 0 ∂unitSourceLaw) =
      ∫⁻ q : ℝ≥0 × Path, if q.1 ∈ lifetimeStratum N times ⟨k+2,by omega⟩ then
        Φ (sample times q) else 0 ∂candidateLaw := by
  let L : Fin (N+1) := ⟨k+2,by omega⟩
  let pre := prefixTimes N k times hk
  let H : FreeVector (k+1) × ℝ → ℝ≥0∞ := fun q ↦
    stratumTest N times L Φ (Real.toNNReal q.2,Fin.cons 0 q.1)
  have hmap : Measurable (fun q : FreeVector (k+1) × ℝ ↦
      (Real.toNNReal q.2,(Fin.cons 0 q.1 : Fin (k+2) → ℝ))) :=
    measurable_snd.real_toNNReal.prodMk ((measurable_cons_zero (k+1)).comp measurable_fst)
  have hH : Measurable H := by
    simpa only [H,Function.comp_def] using (measurable_stratumTest N times L Φ hΦ).comp hmap
  have hrec (g : Path) (hg : g 0 = 0) :
      (fun i : Fin (k+2) ↦ g (times ⟨i.val,by omega⟩)) =
        Fin.cons 0 (fun i : Fin (k+1) ↦ g (pre i.succ)) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.cons_zero,Fin.val_zero,hzero,hg]
    · rfl
  rw [source_stratum_zeroFill N times L Φ,candidate_stratum_zeroFill N times L Φ hΦ]
  calc
    _ = ∫⁻ g : Path, H ((fun i : Fin (k+1) ↦ g (pre i.succ)),(firstReturnZero g).toReal) ∂unitSourceLaw := by
      apply lintegral_congr_ae
      filter_upwards [ae_unitSourceLaw_initial_zero] with g hg
      dsimp only [H]
      rw [ENNReal.toNNReal_toReal_eq,hrec g hg]
      rfl
    _ = ∫⁻ ζ : ℝ, BrownianMinimumFutureReturnDensity.returnDensity ζ *
        (∫⁻ e : Path, H ((fun i : Fin (k+1) ↦ brownianDilation (Real.toNNReal ζ) e (pre i.succ)),ζ)
          ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) :=
      actual_prefix_return_shape_lintegral k pre (prefixTimes_strictMono N k times hk ht)
        (prefixTimes_zero N k times hk hzero) (prefixTimes_last N k times hk hone) H hH
    _ = _ := by
      apply lintegral_congr
      intro ζ
      congr 1
      apply lintegral_congr_ae
      filter_upwards [BrownianEntranceContinuousRealization.ae_pathLaw_initial_zero 1 zero_lt_one] with e he
      dsimp only [H]
      rw [hrec (brownianDilation (Real.toNNReal ζ) e) (dilation_initial_zero _ e he)]

private theorem mixed_stratum_equal (N k n : ℕ) (times : Fin N → ℝ≥0)
    (hkn : k+n+3 ≤ N) (ht : StrictMono times) (hzero : times ⟨0,by omega⟩ = 0)
    (hone : times ⟨k+1,by omega⟩ = 1)
    (Φ : ℝ≥0 × (Fin N → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ g : Path, if (returnTaggedPast g).1 ∈ lifetimeStratum N times ⟨k+(n+1)+1+1,by omega⟩ then
      Φ (sample times (returnTaggedPast g)) else 0 ∂unitSourceLaw) =
      ∫⁻ q : ℝ≥0 × Path, if q.1 ∈ lifetimeStratum N times ⟨k+(n+1)+1+1,by omega⟩ then
        Φ (sample times q) else 0 ∂candidateLaw := by
  let L : Fin (N+1) := ⟨k+(n+1)+1+1,by omega⟩
  let pre := prefixTimes N k times (by omega)
  let post := postTimes N k n times hkn
  let b : ℝ≥0 := 1+post (Fin.last (n+1))
  let G : FreeVector (k+1) × (FreeVector (n+1) × ℝ) → ℝ≥0∞ := fun q ↦
    stratumTest N times L Φ (Real.toNNReal q.2.2,Fin.cons 0 (concatenatedHeights k (n+1) q.1 q.2.1))
  have hcat : Measurable (fun q : FreeVector (k+1) × (FreeVector (n+1) × ℝ) ↦
      (Fin.cons 0 (concatenatedHeights k (n+1) q.1 q.2.1) : Fin L.val → ℝ)) := by
    have hp : Measurable (fun q : FreeVector (k+1) × (FreeVector (n+1) × ℝ) ↦ (q.1,q.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    simpa only [Function.comp_def] using (measurable_cons_zero (k+(n+1)+1)).comp
      ((continuous_concatenatedHeights k (n+1)).measurable.comp hp)
  have hmap : Measurable (fun q : FreeVector (k+1) × (FreeVector (n+1) × ℝ) ↦
      (Real.toNNReal q.2.2,(Fin.cons 0 (concatenatedHeights k (n+1) q.1 q.2.1) : Fin L.val → ℝ))) :=
    (measurable_snd.comp measurable_snd).real_toNNReal.prodMk hcat
  have hG : Measurable G := by
    simpa only [G,Function.comp_def] using (measurable_stratumTest N times L Φ hΦ).comp hmap
  have hb : b = times ⟨L.val-1,by dsimp [L]; omega⟩ := by
    have h := postTimes_absolute N k n times hkn ht.monotone hone (Fin.last (n+1))
    have hi : (⟨k+1+(Fin.last (n+1)).val,by omega⟩ : Fin N) =
        ⟨L.val-1,by dsimp [L]; omega⟩ := Fin.ext (by dsimp [L]; omega)
    rw [hi] at h
    exact h
  have hB (ζ : ℝ≥0) (hζ : ζ ∈ lifetimeStratum N times L) : b < ζ := by
    rw [hb]
    exact (hζ ⟨L.val-1,by dsimp [L]; omega⟩).mpr (by dsimp [L]; omega)
  have hrec (g : Path) (hg : g 0 = 0) :=
    active_tuple_reconstruction N k n times hkn ht.monotone hzero hone g hg
  let E : Set Path := {g | (b : ℝ≥0∞) < firstReturnZero g}
  have hE : MeasurableSet E := measurableSet_lt measurable_const measurable_firstReturnZero
  have hout (g : Path) (hg : g ∉ E) :
      G ((fun i : Fin (k+1) ↦ g (pre i.succ)),
        ((fun i : Fin (n+1) ↦ g (1+post i.succ)),(firstReturnZero g).toReal)) = 0 := by
    dsimp only [G,stratumTest]
    rw [ENNReal.toNNReal_toReal_eq]
    apply if_neg
    intro hmem
    have hlt := hB (firstReturnZero g).toNNReal hmem
    exact hg ((ENNReal.coe_lt_coe.mpr hlt).trans_le ENNReal.coe_toNNReal_le_self)
  rw [source_stratum_zeroFill N times L Φ,candidate_stratum_zeroFill N times L Φ hΦ]
  calc
    _ = ∫⁻ g : Path, G ((fun i : Fin (k+1) ↦ g (pre i.succ)),
        ((fun i : Fin (n+1) ↦ g (1+post i.succ)),(firstReturnZero g).toReal)) ∂unitSourceLaw := by
      apply lintegral_congr_ae
      filter_upwards [ae_unitSourceLaw_initial_zero] with g hg
      dsimp only [G]
      rw [ENNReal.toNNReal_toReal_eq,hrec g hg]
      rfl
    _ = ∫⁻ g in E, G ((fun i : Fin (k+1) ↦ g (pre i.succ)),
        ((fun i : Fin (n+1) ↦ g (1+post i.succ)),(firstReturnZero g).toReal)) ∂unitSourceLaw := by
      rw [← lintegral_indicator hE]
      apply lintegral_congr
      intro g
      by_cases hg : g ∈ E
      · rw [indicator_of_mem hg]
      · rw [indicator_of_notMem hg,hout g hg]
    _ = ∫⁻ ζ in Ioi (b : ℝ), BrownianMinimumFutureReturnDensity.returnDensity ζ *
        (∫⁻ e : Path, G ((fun i : Fin (k+1) ↦ brownianDilation (Real.toNNReal ζ) e (pre i.succ)),
          ((fun i : Fin (n+1) ↦ brownianDilation (Real.toNNReal ζ) e (1+post i.succ)),ζ))
            ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
      simpa only [b,NNReal.coe_add,NNReal.coe_one,E] using actual_mixed_return_shape_lintegral k n pre
        (prefixTimes_strictMono N k times (by omega) ht)
        (prefixTimes_zero N k times (by omega) hzero) (prefixTimes_last N k times (by omega) hone)
        post (postTimes_strictMono N k n times hkn ht hone) (postTimes_zero N k n times hkn hone) G hG
    _ = ∫⁻ ζ : ℝ, BrownianMinimumFutureReturnDensity.returnDensity ζ *
        (∫⁻ e : Path, G ((fun i : Fin (k+1) ↦ brownianDilation (Real.toNNReal ζ) e (pre i.succ)),
          ((fun i : Fin (n+1) ↦ brownianDilation (Real.toNNReal ζ) e (1+post i.succ)),ζ))
            ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro ζ
      by_cases hζ : ζ ∈ Ioi (b : ℝ)
      · rw [indicator_of_mem hζ]
      · rw [indicator_of_notMem hζ]
        have hempty : Real.toNNReal ζ ∉ lifetimeStratum N times L := by
          intro hmem
          exact hζ (Real.lt_toNNReal_iff_coe_lt.mp (hB _ hmem))
        simp only [G,stratumTest,if_neg hempty,lintegral_zero,mul_zero]
    _ = _ := by
      apply lintegral_congr
      intro ζ
      congr 1
      apply lintegral_congr_ae
      filter_upwards [BrownianEntranceContinuousRealization.ae_pathLaw_initial_zero 1 zero_lt_one] with e he
      dsimp only [G]
      rw [hrec (brownianDilation (Real.toNNReal ζ) e) (dilation_initial_zero _ e he)]

theorem actual_returnTaggedPast_law : unitSourceLaw.map returnTaggedPast = candidateLaw := by
  let := candidateLaw_isProbability
  let : IsProbabilityMeasure (unitSourceLaw.map returnTaggedPast) :=
    Measure.isProbabilityMeasure_map measurable_returnTaggedPast.aemeasurable
  apply BrownianStoppedTimeOrderedSampling.ext_of_ordered_sample_tests
  intro N times ht h0 h1 Ψ
  let Φ : ℝ≥0 × (Fin N → ℝ) → ℝ≥0∞ := fun q ↦ (Ψ q : ℝ≥0∞)
  have hΦ : Measurable Φ := ENNReal.continuous_coe.measurable.comp Ψ.continuous.measurable
  let F : ℝ≥0 × Path → ℝ≥0∞ := fun q ↦ Φ (sample times q)
  have hF : Measurable F := by
    simpa only [F,Function.comp_def] using hΦ.comp (continuous_sample times).measurable
  have hs (l : Fin (N+1)) : MeasurableSet {q : ℝ≥0 × Path | q.1 ∈ lifetimeStratum N times l} :=
    measurable_fst (measurableSet_lifetimeStratum N times l)
  have hm (l : Fin (N+1)) : Measurable (({q : ℝ≥0 × Path | q.1 ∈ lifetimeStratum N times l}).indicator F) :=
    hF.indicator (hs l)
  have ha := lintegral_eq_sum_lifetime_strata N times ht.monotone (unitSourceLaw.map returnTaggedPast) F hF
  have hb := lintegral_eq_sum_lifetime_strata N times ht.monotone candidateLaw F hF
  simp_rw [← lintegral_indicator (hs _)] at ha hb
  rw [lintegral_map hF measurable_returnTaggedPast] at ha
  simp_rw [lintegral_map (hm _) measurable_returnTaggedPast] at ha
  change (∫⁻ q, F q ∂unitSourceLaw.map returnTaggedPast) = ∫⁻ q, F q ∂candidateLaw
  rw [lintegral_map hF measurable_returnTaggedPast,ha,hb]
  apply Finset.sum_congr rfl
  intro l _
  simp only [indicator_apply,Set.mem_ofPred_eq,F]
  obtain ⟨i0,hi0⟩ := h0
  obtain ⟨i1,hi1⟩ := h1
  have hN : 0 < N := Nat.zero_lt_of_lt i0.isLt
  let : NeZero N := ⟨ne_of_gt hN⟩
  have hzero : times 0 = 0 := le_antisymm ((ht.monotone (Fin.zero_le i0)).trans_eq hi0) bot_le
  have hi1pos : 0 < i1.val := by
    by_contra hn
    have he : i1 = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    rw [he,hzero] at hi1
    norm_num at hi1
  let k := i1.val-1
  have hk : k+2 ≤ N := by dsimp [k]; have h := i1.isLt; omega
  have hone : times ⟨k+1,by omega⟩ = 1 := by
    have he : (⟨k+1,by omega⟩ : Fin N) = i1 := Fin.ext (by dsimp [k]; omega)
    rw [he]
    exact hi1
  by_cases hsmall : l.val ≤ i1.val
  · exact small_stratum_equal N times l i1 hi1 hsmall Φ hΦ
  · by_cases hbase : l.val = i1.val+1
    · have he : l = ⟨k+2,by omega⟩ := Fin.ext (by dsimp [k]; omega)
      rw [he]
      exact prefix_stratum_equal N k times hk ht hzero hone Φ hΦ
    · let n := l.val-i1.val-2
      have hkn : k+n+3 ≤ N := by dsimp [k,n]; have h := l.isLt; omega
      have he : l = ⟨k+(n+1)+1+1,by omega⟩ := Fin.ext (by dsimp [k,n]; omega)
      rw [he]
      exact mixed_stratum_equal N k n times hkn ht hzero hone Φ hΦ

theorem actual_returnTaggedPast_lintegral (Ψ : ℝ≥0 × Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ g : Path, Ψ (returnTaggedPast g) ∂unitSourceLaw) =
      ∫⁻ ζ : ℝ, BrownianMinimumFutureReturnDensity.returnDensity ζ *
        (∫⁻ e : Path, Ψ (Real.toNNReal ζ,brownianDilation (Real.toNNReal ζ) e)
          ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
  rw [← lintegral_map hΨ measurable_returnTaggedPast,actual_returnTaggedPast_law]
  exact lintegral_candidateLaw Ψ hΨ

end PerronWright.BrownianCompletedExcursionStoppedLaw
