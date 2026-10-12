import PerronWright.Probability.BrownianParabolicPassageDriverFutureLaw
import PerronWright.Probability.ContinuousPathPositiveReturnMeasurable

/-! # Physical complete return after a strictly positive prefix

The actual parabolic continuation is stopped at the negative of the real
prefix endpoint. This proves the complete-return stopped-driver/fresh-noise
formula at its own physical return. In particular, a parabolic continuation
is not assigned the zero-drift entrance source's return time.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianParabolicPositivePrefixReturnLaw

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open ContinuousPathFirstPassage BrownianFirstPassagePastFibers
open BrownianFirstPassageUncappedLaw
open BrownianMinimumFutureFirstReturn BrownianMinimumFutureReturnPathGeometry
open ContinuousPathPositiveReturnMeasurable
open BrownianParabolicFirstPassageStrongMarkovFull BrownianParabolicFirstPassageStoppedTiltFull
open BrownianParabolicFirstPassageFinite BrownianParabolicPassageDriverFutureLaw

private theorem return_eq_post_prefix_passage (r : ℝ≥0) (hr : 0 < r) (g : Path)
    (hg : ∀ t : ℝ≥0, 0 < t → t ≤ r → 0 < g t) :
    firstReturnZero g = (r : ℝ≥0∞)+firstPassage (-g r) (futurePath r g) := by
  apply le_antisymm
  · by_cases hfin : firstPassage (-g r) (futurePath r g) = ⊤
    · rw [hfin,add_top]
      exact le_top
    · let τ := (firstPassage (-g r) (futurePath r g)).toNNReal
      have hh := firstPassage_attained (-g r) (futurePath r g) hfin
      have hhit : g (r+τ) ≤ 0 := by
        rw [futurePath_eval] at hh
        change g (r+τ)-g r ≤ -g r at hh
        linarith
      have hpos : 0 < r+τ := add_pos_of_pos_of_nonneg hr bot_le
      have hle : firstReturnZero g ≤ ((r+τ : ℝ≥0) : ℝ≥0∞) :=
        sInf_le ⟨r+τ,⟨hpos,hhit⟩,rfl⟩
      simpa only [ENNReal.coe_add,τ,ENNReal.coe_toNNReal hfin] using hle
  · apply le_sInf
    rintro x ⟨t,⟨ht0,hgt⟩,rfl⟩
    have hrt : r < t := lt_of_not_ge (fun ht ↦ (not_le_of_gt (hg t ht0 ht)) hgt)
    have hh : firstPassage (-g r) (futurePath r g) ≤ ((t-r : ℝ≥0) : ℝ≥0∞) := by
      apply (firstPassage_le_iff (-g r) (futurePath r g) (t-r)).mpr
      refine ⟨t-r,le_rfl,?_⟩
      rw [futurePath_eval,add_tsub_cancel_of_le hrt.le]
      linarith
    calc
      _ ≤ (r : ℝ≥0∞)+((t-r : ℝ≥0) : ℝ≥0∞) := add_le_add le_rfl hh
      _ = (t : ℝ≥0∞) := by rw [← ENNReal.coe_add,add_tsub_cancel_of_le hrt.le]

private theorem past_splice (r : ℝ≥0) (p h : Path) (hzero : h 0 = 0) :
    pastPath r (splicePath r (p,h)) = pastPath r p := by
  apply ContinuousMap.ext
  intro t
  change p (min (min t r) r)+h (min t r-r) = p (min t r)
  rw [min_assoc,min_self,tsub_eq_zero_of_le (min_le_right t r),hzero,add_zero]

private theorem future_splice (r : ℝ≥0) (p h : Path) (hzero : h 0 = 0) :
    futurePath r (splicePath r (p,h)) = h := by
  apply ContinuousMap.ext
  intro t
  change (p (min (r+t) r)+h (r+t-r))-(p (min r r)+h (r-r)) = h t
  rw [min_eq_right (le_add_of_nonneg_right bot_le),add_tsub_cancel_left,min_self,
    tsub_self,hzero,add_zero]
  ring

private theorem splice_return_reconstruction (r : ℝ≥0) (hr : 0 < r) (p h : Path)
    (hp : ∀ t : ℝ≥0, 0 < t → t ≤ r → 0 < p t) (hzero : h 0 = 0)
    (hfin : firstPassage (-p r) h ≠ ⊤) :
    returnTaggedPast (splicePath r (p,h)) =
        (r+(firstPassage (-p r) h).toNNReal,
          splicePath r (pastPath r p,pastPath (firstPassage (-p r) h).toNNReal h)) ∧
      returnFuturePath (splicePath r (p,h)) = futurePath (firstPassage (-p r) h).toNNReal h := by
  have hprefix : ∀ t : ℝ≥0, 0 < t → t ≤ r → 0 < splicePath r (p,h) t := by
    intro t ht htr
    change 0 < p (min t r)+h (t-r)
    rw [min_eq_left htr,tsub_eq_zero_of_le htr,hzero,add_zero]
    exact hp t ht htr
  have hreturn := return_eq_post_prefix_passage r hr (splicePath r (p,h)) hprefix
  have heval : splicePath r (p,h) r = p r := by
    rw [splicePath_eval,min_self,tsub_self,hzero,add_zero]
  rw [heval,future_splice r p h hzero] at hreturn
  have ht : (firstReturnZero (splicePath r (p,h))).toNNReal =
      r+(firstPassage (-p r) h).toNNReal := by
    rw [hreturn,ENNReal.toNNReal_add ENNReal.coe_ne_top hfin,ENNReal.toNNReal_coe]
  constructor
  · rw [returnTaggedPast,ht,pastPath_add_splice,past_splice r p h hzero,future_splice r p h hzero]
  · rw [returnFuturePath,ht,futurePath_add,future_splice r p h hzero]

theorem actual_positive_prefix_parabolic_return_lintegral (r : ℝ≥0) (hr : 0 < r)
    (p : Path) (hp : ∀ t : ℝ≥0, 0 < t → t ≤ r → 0 < p t) (lambda : ℝ)
    {Ψ : (ℝ≥0 × Path) × Path → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ h : Path, Ψ (returnTaggedPast (splicePath r (p,driftPath lambda h)),
      returnFuturePath (splicePath r (p,driftPath lambda h))) ∂pathLaw) =
      ∫⁻ q : ℝ≥0 × Path, ∫⁻ k : Path,
        Ψ ((r+q.1,splicePath r (pastPath r p,q.2)),driftPath (lambda-(q.1 : ℝ)) k)
          ∂pathLaw ∂pathLaw.map (actualDriverPassagePast lambda (-p r)) := by
  let Φ : (ℝ≥0 × Path) × Path → ℝ≥0∞ := fun z ↦
    Ψ ((r+z.1.1,splicePath r (pastPath r p,z.1.2)),z.2)
  have hΦ : Measurable Φ := hΨ.comp
    (((measurable_const.add measurable_fst.fst).prodMk
      ((measurable_splicePath r).comp (measurable_const.prodMk measurable_fst.snd))).prodMk measurable_snd)
  have he := actual_driver_passage_future_lintegral lambda (-p r) hΦ
  calc
    _ = ∫⁻ h : Path, Φ (actualDriverPassagePast lambda (-p r) h,
        futurePath (parabolicPassageTime lambda (-p r) h) (driftPath lambda h)) ∂pathLaw := by
      apply lintegral_congr_ae
      filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero,
        ae_parabolicFirstPassage_ne_top lambda (-p r)] with h hzero hfin
      have hd0 : driftPath lambda h 0 = 0 := by
        change h 0+lambda*(0 : ℝ)-(0 : ℝ)^2/2 = 0
        simp only [hzero,mul_zero,zero_pow (by decide : 2 ≠ 0),zero_div,add_zero,sub_zero]
      obtain ⟨hgp,hgf⟩ := splice_return_reconstruction r hr p (driftPath lambda h) hp hd0 hfin
      rw [hgp,hgf]
      rfl
    _ = _ := he

theorem actual_positive_prefix_brownian_return_lintegral (r : ℝ≥0) (hr : 0 < r)
    (p : Path) (hp : ∀ t : ℝ≥0, 0 < t → t ≤ r → 0 < p t)
    {Ψ : (ℝ≥0 × Path) × Path → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ h : Path, Ψ (returnTaggedPast (splicePath r (p,h)),
      returnFuturePath (splicePath r (p,h))) ∂pathLaw) =
      ∫⁻ q : ℝ≥0 × Path, ∫⁻ k : Path,
        Ψ ((r+q.1,splicePath r (pastPath r p,q.2)),k) ∂pathLaw
          ∂pathLaw.map (BrownianFirstPassageUncappedLaw.passagePast (-p r)) := by
  let Φ : (ℝ≥0 × Path) × Path → ℝ≥0∞ := fun z ↦
    Ψ ((r+z.1.1,splicePath r (pastPath r p,z.1.2)),z.2)
  have hΦ : Measurable Φ := hΨ.comp
    (((measurable_const.add measurable_fst.fst).prodMk
      ((measurable_splicePath r).comp (measurable_const.prodMk measurable_fst.snd))).prodMk measurable_snd)
  have hnegative : -p r < 0 := neg_neg_of_pos (hp r hr le_rfl)
  let : IsProbabilityMeasure (pathLaw.map (BrownianFirstPassageUncappedLaw.passagePast (-p r))) :=
    Measure.isProbabilityMeasure_map (measurable_passagePast (-p r)).aemeasurable
  have he : (∫⁻ h : Path, Φ (BrownianFirstPassageUncappedLaw.passagePast (-p r) h,
      BrownianFirstPassageUncappedLaw.passageFuture (-p r) h) ∂pathLaw) =
      ∫⁻ q : ℝ≥0 × Path, ∫⁻ k : Path, Φ (q,k) ∂pathLaw
        ∂pathLaw.map (BrownianFirstPassageUncappedLaw.passagePast (-p r)) := by
    rw [← lintegral_map hΦ ((measurable_passagePast (-p r)).prodMk (measurable_passageFuture (-p r))),
      BrownianFirstPassageStrongMarkovFull.passage_jointLaw (-p r) hnegative]
    exact lintegral_prod _ hΦ.aemeasurable
  calc
    _ = ∫⁻ h : Path, Φ (BrownianFirstPassageUncappedLaw.passagePast (-p r) h,
        BrownianFirstPassageUncappedLaw.passageFuture (-p r) h) ∂pathLaw := by
      apply lintegral_congr_ae
      filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero,
        BrownianFirstPassageZeroDrift.ae_firstPassage_ne_top (-p r) hnegative] with h hzero hfin
      obtain ⟨hgp,hgf⟩ := splice_return_reconstruction r hr p h hp hzero hfin
      rw [hgp,hgf]
      rfl
    _ = _ := he

end PerronWright.BrownianParabolicPositivePrefixReturnLaw
