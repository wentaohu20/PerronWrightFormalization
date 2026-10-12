import PerronWright.Probability.BrownianPathIndependentIncrements
import PerronWright.Probability.ContinuousPathIntervalMinimum

/-! # Actual Brownian minima on separated intervals cannot tie

The stopped left path and the entire right future leave an independent
diffuse Gaussian increment across the gap. Every fixed pair of pieces
has at most one increment producing a tie. This proves the actual null
event, not a minimum uniqueness assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPathSeparatedMinima

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathIntervalMinimum
open ContinuousPathLeastMinimum

theorem endpoint_future_jointLaw (h : ℝ≥0) :
    pathLaw.map (fun f : Path ↦ (f h,futurePath h f)) =
      (gaussianReal 0 h).prod pathLaw := by
  have hm : Measurable (Prod.map (fun f : Path ↦ f h) (id : Path → Path)) :=
    (continuous_eval h).measurable.prodMap measurable_id
  have he := congrArg (Measure.map (Prod.map (fun f : Path ↦ f h) (id : Path → Path)))
    (past_future_jointLaw h)
  rw [Measure.map_map hm ((measurable_pastPath h).prodMk (measurable_futurePath h)),
    ← Measure.map_prod_map (pastLaw h) pathLaw (continuous_eval h).measurable measurable_id,
    Measure.map_id] at he
  have hl : Prod.map (fun f : Path ↦ f h) (id : Path → Path) ∘
      (fun f : Path ↦ (pastPath h f,futurePath h f)) =
      (fun f : Path ↦ (f h,futurePath h f)) := by
    funext f
    simp only [Function.comp_def,Prod.map_apply,id_eq,pastPath_eval,min_self]
  have hr : (pastLaw h).map (fun f : Path ↦ f h) = gaussianReal 0 h := by
    rw [pastLaw,Measure.map_map (continuous_eval h).measurable (measurable_pastPath h)]
    have hh : (fun f : Path ↦ f h) ∘ pastPath h = fun f : Path ↦ f h := by
      funext f
      simp only [Function.comp_def,pastPath_eval,min_self]
    rw [hh]
    exact isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval h |>.map_eq
  rw [hl,hr] at he
  exact he

theorem past_gap_future_jointLaw (a b : ℝ≥0) (hab : a ≤ b) :
    pathLaw.map (fun f : Path ↦ (pastPath a f,f b-f a,futurePath b f)) =
      (pastLaw a).prod ((gaussianReal 0 (b-a)).prod pathLaw) := by
  let R : Path → ℝ × Path := fun g ↦ (g (b-a),futurePath (b-a) g)
  have hR : Measurable R := (continuous_eval (b-a)).measurable.prodMk (measurable_futurePath (b-a))
  have he := congrArg (Measure.map (Prod.map (id : Path → Path) R)) (past_future_jointLaw a)
  rw [Measure.map_map (measurable_id.prodMap hR)
    ((measurable_pastPath a).prodMk (measurable_futurePath a)),
    ← Measure.map_prod_map (pastLaw a) pathLaw measurable_id hR,Measure.map_id,
    endpoint_future_jointLaw] at he
  have hf (f : Path) : futurePath (b-a) (futurePath a f) = futurePath b f := by
    apply ContinuousMap.ext
    intro t
    change (f (a+((b-a)+t))-f a)-(f (a+(b-a))-f a) = f (b+t)-f b
    rw [← add_assoc,add_tsub_cancel_of_le hab]
    ring
  have hl : Prod.map (id : Path → Path) R ∘
      (fun f : Path ↦ (pastPath a f,futurePath a f)) =
      (fun f : Path ↦ (pastPath a f,f b-f a,futurePath b f)) := by
    funext f
    simp only [Function.comp_def,Prod.map_apply,id_eq,R,futurePath_eval,
      add_tsub_cancel_of_le hab,hf]
  rw [hl] at he
  exact he

theorem intervalMinimum_shift_future (b w : ℝ≥0) (hbw : b ≤ w) (f : Path) :
    intervalMinimum b w f = f b+minimumValue (w-b) (futurePath b f) := by
  apply intervalMinimum_eq_of_attains b w hbw
  · intro t ht
    have hm := minimumValue_le (w-b) (futurePath b f) (t-b) (tsub_le_tsub_right ht.2 b)
    rw [futurePath_eval,add_tsub_cancel_of_le ht.1] at hm
    linarith
  · let t := leastMinimizer (w-b) (futurePath b f)
    have ht := leastMinimizer_le_time (w-b) (futurePath b f)
    have he := leastMinimizer_value (w-b) (futurePath b f)
    refine ⟨b+t,⟨le_add_of_nonneg_right zero_le,?_⟩,?_⟩
    · calc
        b+t ≤ b+(w-b) := add_le_add_right ht b
        _ = w := add_tsub_cancel_of_le hbw
    · change f (b+t)-f b = minimumValue (w-b) (futurePath b f) at he
      linarith

theorem ae_separated_interval_minima_ne (l a b w : ℝ≥0)
    (_hla : l ≤ a) (hab : a < b) (hbw : b ≤ w) :
    ∀ᵐ f ∂pathLaw, intervalMinimum l a f ≠ intervalMinimum b w f := by
  let H : Set (Path × ℝ × Path) := {p | intervalMinimum l a p.1 =
    p.1 a+p.2.1+minimumValue (w-b) p.2.2}
  have hH : MeasurableSet H := measurableSet_eq_fun
    ((continuous_intervalMinimum l a).measurable.comp measurable_fst)
    ((((continuous_eval a).measurable.comp measurable_fst).add measurable_snd.fst).add
      ((continuous_minimumValue (w-b)).measurable.comp measurable_snd.snd))
  let G := gaussianReal 0 (b-a)
  let : NullSingletonClass G := nullSingletonClass_gaussianReal
    (ne_of_gt (tsub_pos_iff_lt.mpr hab))
  have hsection (p g : Path) : G {z : ℝ | (p,z,g) ∈ H} = 0 := by
    apply Set.Subsingleton.measure_zero
    intro x hx y hy
    change intervalMinimum l a p = p a+x+minimumValue (w-b) g at hx
    change intervalMinimum l a p = p a+y+minimumValue (w-b) g at hy
    linarith
  have hz : ((pastLaw a).prod (G.prod pathLaw)) H = 0 := by
    rw [Measure.prod_apply hH]
    have hi (p : Path) : (G.prod pathLaw) (Prod.mk p ⁻¹' H) = 0 := by
      have hS : MeasurableSet (Prod.mk p ⁻¹' H) := by
        have hh : Measurable (Prod.mk p : ℝ × Path → Path × ℝ × Path) :=
          measurable_const.prodMk measurable_id
        exact hH.preimage hh
      rw [Measure.prod_apply_symm hS]
      change (∫⁻ g : Path, G {z : ℝ | (p,z,g) ∈ H} ∂pathLaw) = 0
      simp only [hsection,lintegral_zero]
    simp only [hi,lintegral_zero]
  have hm : Measurable (fun f : Path ↦ (pastPath a f,f b-f a,futurePath b f)) :=
    (measurable_pastPath a).prodMk
      (((continuous_eval b).measurable.sub (continuous_eval a).measurable).prodMk
        (measurable_futurePath b))
  have he : {f : Path | intervalMinimum l a f = intervalMinimum b w f} =
      (fun f : Path ↦ (pastPath a f,f b-f a,futurePath b f)) ⁻¹' H := by
    ext f
    have hl : intervalMinimum l a (pastPath a f) = intervalMinimum l a f := by
      unfold intervalMinimum
      congr 1
      apply image_congr
      intro t ht
      simp only [pastPath_eval,min_eq_left ht.2]
    change intervalMinimum l a f = intervalMinimum b w f ↔
      intervalMinimum l a (pastPath a f) =
      pastPath a f a+(f b-f a)+minimumValue (w-b) (futurePath b f)
    rw [hl,pastPath_eval,min_self,intervalMinimum_shift_future b w hbw f]
    ring_nf
  have hzero : pathLaw {f : Path | intervalMinimum l a f = intervalMinimum b w f} = 0 := by
    rw [he,← Measure.map_apply hm hH,past_gap_future_jointLaw a b hab.le]
    exact hz
  simpa only [ae_iff,not_not] using hzero

end PerronWright.BrownianPathSeparatedMinima
