import PerronWright.Probability.BrownianPositiveBridgeFiniteDimensionalSource
import PerronWright.Probability.BrownianPositiveBridgeFiniteDimensionalDensity
import PerronWright.Probability.BrownianKilledSemigroupJointLaw

/-! # An actual positive pinned bridge's interior one-point density

The actual two-segment killed law is compared with the true bridge--endpoint
product. The finite-coordinate lower-cut probability is monotone in the
endpoint, while the killed exit integral is continuous. Thus equality of
densities almost everywhere identifies the bridge at its literal zero
endpoint. No pinned Markov or excursion identity is used as an input.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeFiniteDimensionalOnePoint

open BrownianPathLaw ContinuousPathFirstPassage BrownianKilledSemigroup
open BrownianKilledTransitionKernel BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel
open BrownianKilledSemigroupJointLaw BrownianPositiveBridgeFiniteDimensionalDensity
open BrownianPositiveBridgeFiniteDimensionalSource BrownianBridgeSurvivalPointwise
open BrownianPositiveBridgeConditioning

theorem transitionLaw_shift (a x : ℝ) (t : ℝ≥0) :
    transitionLaw (-a) t x = (law (x+a) t).map (fun y : ℝ ↦ y-a) := by
  rw [law_eq_shift_killed,Measure.map_map (by fun_prop) (measurable_endpointShift (x+a))]
  have he : -(x+a) = -a-x := by ring
  rw [he,transitionLaw]
  congr 1
  funext y
  dsimp only [Function.comp_def]
  ring

theorem transitionLaw_apply_density (a x : ℝ) (t : ℝ≥0) (ht : 0 < t)
    {B : Set ℝ} (hB : MeasurableSet B) :
    transitionLaw (-a) t x B = ∫⁻ z in B, density (x+a) t (z+a) := by
  have hsub : Measurable (fun y : ℝ ↦ y-a) := by fun_prop
  have hd : Measurable (fun z : ℝ ↦ density (x+a) t (z+a)) :=
    (measurable_density (x+a) t).comp (measurable_endpointShift a)
  rw [transitionLaw_shift,Measure.map_apply hsub hB,law_eq_withDensity_all (x+a) t ht,
    withDensity_apply _ (hsub hB)]
  calc
    _ = ∫⁻ y in (fun y : ℝ ↦ y-a) ⁻¹' B, density (x+a) t ((y-a)+a) := by
      apply setLIntegral_congr_fun (hsub hB)
      intro y _
      change density (x+a) t y = density (x+a) t ((y-a)+a)
      rw [sub_add_cancel]
    _ = ∫⁻ z in B, density (x+a) t (z+a) ∂volume.map (fun y : ℝ ↦ y-a) :=
      (setLIntegral_map hB hd hsub).symm
    _ = _ := by
      change (∫⁻ z in B, density (x+a) t (z+a) ∂volume.map (fun y : ℝ ↦ y+(-a))) = _
      rw [map_add_right_eq_self]

def headLaw (a : ℝ) (s : ℝ≥0) (c : ℝ) : Measure ℝ := (law a s).restrict (Ioi c)

instance headLaw_isFinite (a : ℝ) (s : ℝ≥0) (c : ℝ) : IsFiniteMeasure (headLaw a s c) := by
  unfold headLaw
  infer_instance

def exitIntegral (a : ℝ) (s t : ℝ≥0) (c z : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, density x t (z+a) ∂headLaw a s c

def exitRatio (a : ℝ) (s t : ℝ≥0) (c z : ℝ) : ℝ≥0∞ :=
  exitIntegral a s t c z/gaussianPDF 0 (s+t) z

theorem continuous_exitIntegral (a : ℝ) (s t : ℝ≥0) (ht : 0 < t) (c : ℝ) :
    Continuous (exitIntegral a s t c) := continuous_last_kernel_integral (headLaw a s c) t ht a

theorem continuous_exitRatio (a : ℝ) (s t : ℝ≥0) (ht : 0 < t) (c : ℝ) :
    Continuous (exitRatio a s t c) :=
  continuous_exit_ratio (headLaw a s c) t (s+t) ht
    (ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))) a

theorem endpointLaw_eq_exitIntegral_density (a : ℝ) (s t : ℝ≥0) (ht : 0 < t) (c : ℝ) :
    endpointLaw a (s+t) (fun _ : Fin 1 ↦ s) (fun _ ↦ c) =
      volume.withDensity (exitIntegral a s t c) := by
  ext B hB
  have hsT : s ≤ s+t := le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ t)
  have he : (fun f : Path ↦ f (s+t)) ⁻¹' B ∩
      (survival (-a) (s+t) ∩ {f | ∀ _ : Fin 1, c < f (min s (s+t))+a}) =
      {f : Path | f ∈ survival (-a) (s+t) ∧ f s ∈ Ioi (c-a) ∧ f (s+t) ∈ B} := by
    ext f
    simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,min_eq_left hsT,
      Fin.forall_fin_one,mem_Ioi]
    constructor
    · rintro ⟨hB,hSurv,hCut⟩
      exact ⟨hSurv,by linarith,hB⟩
    · rintro ⟨hSurv,hCut,hB⟩
      exact ⟨hB,hSurv,by linarith⟩
  rw [endpointLaw,Measure.map_apply (continuous_eval (s+t)).measurable hB,
    Measure.restrict_apply ((continuous_eval (s+t)).measurable hB),he,
    two_endpoint_rectangle_probability (-a) s t measurableSet_Ioi hB,
    withDensity_apply _ hB]
  have hm : Measurable (fun x : ℝ ↦ ∫⁻ z in B, density x t (z+a)) := by
    apply Measurable.lintegral_prod_right
    exact (BrownianPositiveKilledKernel.measurable_joint_density t).comp
      (measurable_fst.prodMk (measurable_snd.add_const a))
  have hm₂ : Measurable (fun p : ℝ × ℝ ↦ density p.1 t (p.2+a)) :=
    (BrownianPositiveKilledKernel.measurable_joint_density t).comp
      (measurable_fst.prodMk (measurable_snd.add_const a))
  calc
    _ = ∫⁻ u in Ioi (c-a), (∫⁻ z in B, density (u+a) t (z+a) ∂volume) ∂killedEndpointLaw (-a) s := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro u _
      exact transitionLaw_apply_density a u t ht hB
    _ = ∫⁻ x in Ioi c, (∫⁻ z in B, density x t (z+a) ∂volume) ∂law a s := by
      have hpre : (fun u : ℝ ↦ u+a) ⁻¹' Ioi c = Ioi (c-a) := by
        ext u
        simp only [mem_preimage,mem_Ioi]
        constructor <;> intro hu <;> linarith
      rw [law_eq_shift_killed,setLIntegral_map measurableSet_Ioi hm (measurable_endpointShift a),hpre]
    _ = ∫⁻ z in B, ∫⁻ x, density x t (z+a) ∂headLaw a s c := by
      exact lintegral_lintegral_swap (μ := headLaw a s c) (ν := volume.restrict B)
        hm₂.aemeasurable

theorem probability_eq_exitRatio (a : ℝ) (s t : ℝ≥0) (ht : 0 < t) (c z : ℝ) :
    probability a (s+t) (fun _ : Fin 1 ↦ s) (fun _ ↦ c) z = exitRatio a s t c z := by
  have hT : 0 < s+t := ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))
  let p := probability a (s+t) (fun _ : Fin 1 ↦ s) (fun _ ↦ c)
  have hp : Measurable p := measurable_probability a (s+t) (fun _ : Fin 1 ↦ s) (fun _ ↦ c)
  have hd := (endpointLaw_eq_bridge_density a (s+t) hT (fun _ : Fin 1 ↦ s) (fun _ ↦ c)).symm.trans
    (endpointLaw_eq_exitIntegral_density a s t ht c)
  rw [gaussianReal_of_var_ne_zero 0 (ne_of_gt hT),← withDensity_mul volume
    (measurable_gaussianPDF 0 (s+t)) hp] at hd
  have hae : (fun z ↦ gaussianPDF 0 (s+t) z*p z) =ᵐ[volume] exitIntegral a s t c :=
    (withDensity_eq_iff_of_sigmaFinite ((measurable_gaussianPDF 0 (s+t)).mul hp).aemeasurable
      (continuous_exitIntegral a s t ht c).measurable.aemeasurable).mp hd
  have hratio : p =ᵐ[volume] exitRatio a s t c := by
    filter_upwards [hae] with w hw
    have hpos : gaussianPDF 0 (s+t) w ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr
      (gaussianPDFReal_pos 0 (s+t) w (ne_of_gt hT))
    have hfin : gaussianPDF 0 (s+t) w ≠ ∞ := ENNReal.ofReal_ne_top
    unfold exitRatio
    rw [← hw,mul_comm,_root_.ENNReal.mul_div_cancel_right hpos hfin]
  exact congrFun (monotone_eq_of_ae_eq volume (monotone_probability a (s+t)
    (fun _ : Fin 1 ↦ s) (fun _ ↦ c)) (continuous_exitRatio a s t ht c) hratio) z

theorem positiveBridgeLaw_onePoint_tail (a : ℝ) (ha : 0 < a) (s t : ℝ≥0)
    (ht : 0 < t) (c : ℝ) :
    positiveBridgeLaw a (s+t) {g | c < g s} =
      (ENNReal.ofReal (1-Real.exp (-2*a^2/(s+t : ℝ≥0))))⁻¹ *
        (∫⁻ x in Ioi c, density x t a ∂law a s)/gaussianPDF 0 (s+t) 0 := by
  have hT : 0 < s+t := ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))
  have he : lowerCuts (fun _ : Fin 1 ↦ s) (fun _ ↦ c) = {g : Path | c < g s} := by
    ext g
    simp only [lowerCuts,mem_ofPred_eq,Fin.forall_fin_one]
  rw [← he,positiveBridgeLaw_lowerCuts a ha (s+t) hT,
    probability_eq_exitRatio a s t ht c 0]
  simp only [exitRatio,exitIntegral,headLaw,zero_add,mul_div_assoc]

end PerronWright.BrownianPositiveBridgeFiniteDimensionalOnePoint
