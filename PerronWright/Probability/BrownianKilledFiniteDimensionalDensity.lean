import PerronWright.Probability.BrownianKilledFiniteDimensionalDensityCoordinates

/-! # Actual killed Brownian finite-dimensional Gaussian product density

The free endpoint vector is a literal map of the constructed Brownian
path law restricted to whole-interval survival. Its genuine killed chain
law and the proved Gaussian-difference kernel identify its density under
finite product Lebesgue measure. No Markov or density identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledFiniteDimensionalDensity

open BrownianPathLaw BrownianKilledSemigroup ContinuousPathFirstPassage
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalLaw
open BrownianKilledFiniteDimensionalOrderedTimes BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

def freeTupleLaw (a : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) : Measure (FreeVector n) :=
  (actualTupleLaw 0 a gaps n).map (dropInitial n)

instance freeTupleLaw_isFinite (a : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    IsFiniteMeasure (freeTupleLaw a gaps n) := by unfold freeTupleLaw; infer_instance

theorem freeTupleLaw_eq_chain_map (a : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    freeTupleLaw a gaps n = (chainLaw 0 a gaps n).map (dropInitial n) := by
  rw [freeTupleLaw,actualTupleLaw_eq_chainLaw]

theorem freeTupleLaw_eq_source (a : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    freeTupleLaw a gaps n = (pathLaw.restrict (survival (-a) (sampleTime gaps n))).map
      (fun f : Path ↦ fun i : Fin n ↦ a+f (sampleTime gaps (i.val+1))) := by
  rw [freeTupleLaw,actualTupleLaw,zero_sub,Measure.map_map (continuous_dropInitial n).measurable
    (continuous_endpointTuple n a gaps).measurable]
  rfl

theorem chainLaw_initial_ae (a : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    ∀ᵐ v ∂chainLaw 0 a gaps n, v 0 = a := by
  rw [← actualTupleLaw_eq_chainLaw,actualTupleLaw]
  apply (ae_map_iff (continuous_endpointTuple n a gaps).measurable.aemeasurable
    (isClosed_eq (continuous_apply 0) continuous_const).measurableSet).mpr
  filter_upwards [ae_restrict_of_ae isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero]
    with f hf
  change a+f (sampleTime gaps 0) = a
  rw [sampleTime_zero,hf,add_zero]

theorem lintegral_transition_density (t : ℝ≥0) (ht : 0 < t) (z : ℝ)
    {Ψ : ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ y, Ψ y ∂transitionLaw 0 t z) = ∫⁻ y, density z t y*Ψ y := by
  rw [← killedKernel_apply,killedKernel_zero_eq_density t ht z,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_density z t) hΨ]
  rfl

/-- Arbitrary coupled free-coordinate test, with the actual killed chain
identified as the literal Gaussian-difference product under Lebesgue measure. -/
theorem lintegral_chain_free_density (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n, 0 < gaps j) {Φ : FreeVector n → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ v, Φ (dropInitial n v) ∂chainLaw 0 a gaps n) =
      ∫⁻ v, jointDensity n a gaps v*Φ v := by
  induction n with
  | zero =>
    rw [chainLaw_zero,if_pos ha,lintegral_dirac,Measure.volume_pi_eq_dirac]
    simp only [jointDensity_zero,one_mul,lintegral_dirac]
    exact congrArg Φ (Subsingleton.elim _ _)
  | succ n ih =>
    have hn : 0 < gaps n := hgaps n (Nat.lt_succ_self n)
    have hprev : ∀ j < n, 0 < gaps j := fun j hj ↦ hgaps j (hj.trans (Nat.lt_succ_self n))
    have hΨ : Measurable (fun v : EndpointVector (n+1) ↦ Φ (dropInitial (n+1) v)) :=
      hΦ.comp (continuous_dropInitial (n+1)).measurable
    rw [lintegral_chainLaw_succ 0 a gaps n hΨ]
    simp only [dropInitial_append]
    let J : FreeVector n × ℝ → ℝ≥0∞ :=
      fun p ↦ density (lastState n a p.1) (gaps n) p.2*Φ (freeAppend n p)
    have hD : Measurable (fun p : FreeVector n × ℝ ↦ density (lastState n a p.1) (gaps n) p.2) := by
      have hp : Measurable (fun p : FreeVector n × ℝ ↦ (lastState n a p.1,p.2)) :=
        (((continuous_lastState n a).comp continuous_fst).measurable).prodMk measurable_snd
      have hm := measurable_joint_density (gaps n)
      simpa only [Function.comp_def] using hm.comp hp
    have hP : Measurable (fun p : FreeVector n × ℝ ↦ Φ (freeAppend n p)) :=
      hΦ.comp (continuous_freeAppend n).measurable
    have hJ : Measurable J := hD.mul hP
    let H : FreeVector n → ℝ≥0∞ := fun v ↦ ∫⁻ y, J (v,y)
    have hH : Measurable H := hJ.lintegral_prod_right'
    have hpart (v : FreeVector n) : Measurable (fun y : ℝ ↦ J (v,y)) :=
      hJ.comp (measurable_const.prodMk measurable_id)
    calc
      _ = ∫⁻ v, H (dropInitial n v) ∂chainLaw 0 a gaps n := by
        apply lintegral_congr_ae
        filter_upwards [chainLaw_initial_ae a gaps n] with v hv
        rw [← lastState_dropInitial n a v hv]
        have hf : Measurable (fun y : ℝ ↦ Φ (freeAppend n (dropInitial n v,y))) :=
          hΦ.comp ((continuous_freeAppend n).comp (continuous_const.prodMk continuous_id)).measurable
        rw [lintegral_transition_density (gaps n) hn _ hf]
      _ = ∫⁻ v, jointDensity n a gaps v*H v := ih hprev hH
      _ = ∫⁻ v, jointDensity (n+1) a gaps v*Φ v := by
        have hF : Measurable (fun v : FreeVector (n+1) ↦ jointDensity (n+1) a gaps v*Φ v) :=
          (measurable_jointDensity (n+1) a gaps).mul hΦ
        rw [lintegral_volume_freeAppend n hF]
        apply lintegral_congr
        intro v
        simp_rw [jointDensity_append,mul_assoc]
        exact (lintegral_const_mul (jointDensity n a gaps v) (hpart v)).symm

theorem freeTupleLaw_eq_withDensity (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n, 0 < gaps j) :
    freeTupleLaw a gaps n = volume.withDensity (jointDensity n a gaps) := by
  ext B hB
  rw [← lintegral_indicator_one hB,← lintegral_indicator_one hB,
    freeTupleLaw_eq_chain_map,lintegral_map (measurable_one.indicator hB)
      (continuous_dropInitial n).measurable,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_jointDensity n a gaps)
      (measurable_one.indicator hB)]
  exact lintegral_chain_free_density n a ha gaps hgaps (measurable_one.indicator hB)

theorem freeTupleLaw_eq_zero_of_nonpos (a : ℝ) (ha : a ≤ 0) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    freeTupleLaw a gaps n = 0 := by
  have hz : pathLaw (survival (-a) (sampleTime gaps n)) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
    intro hs
    have he := (mem_survival_iff (-a) (sampleTime gaps n) f).mp hs 0 zero_le
    rw [hf] at he
    linarith
  rw [freeTupleLaw_eq_source,Measure.restrict_eq_zero.mpr hz,Measure.map_zero]

theorem jointDensity_eq_zero_of_nonpos_initial (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : a ≤ 0)
    (gaps : ℕ → ℝ≥0) (hgaps : ∀ j < n, 0 < gaps j) : jointDensity n a gaps = 0 := by
  funext v
  unfold jointDensity
  let i : Fin n := ⟨0,hn⟩
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hi : i.castSucc = (0 : Fin (n+1)) := rfl
  rw [hi]
  change density a (gaps 0) (v i) = 0
  exact congrFun (density_eq_zero_of_nonpos a ha (gaps 0) (hgaps 0 hn)) (v i)

/-- All real initial states are included. Nonpositive initial states
give the actual zero killed law and the actual zero Gaussian product. -/
theorem freeTupleLaw_eq_withDensity_all (n : ℕ) (hn : 0 < n) (a : ℝ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n, 0 < gaps j) :
    freeTupleLaw a gaps n = volume.withDensity (jointDensity n a gaps) := by
  rcases lt_or_ge 0 a with ha | ha
  · exact freeTupleLaw_eq_withDensity n a ha gaps hgaps
  · rw [freeTupleLaw_eq_zero_of_nonpos a ha gaps n,
      jointDensity_eq_zero_of_nonpos_initial n hn a ha gaps hgaps,withDensity_zero]

theorem actual_free_endpoints_density (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n, 0 < gaps j) :
    (pathLaw.restrict (survival (-a) (sampleTime gaps n))).map
        (fun f : Path ↦ fun i : Fin n ↦ a+f (sampleTime gaps (i.val+1))) =
      volume.withDensity (jointDensity n a gaps) := by
  rw [← freeTupleLaw_eq_source]
  exact freeTupleLaw_eq_withDensity n a ha gaps hgaps

theorem lintegral_actual_free_density (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n, 0 < gaps j) {Φ : FreeVector n → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f in survival (-a) (sampleTime gaps n),
        Φ (fun i : Fin n ↦ a+f (sampleTime gaps (i.val+1))) ∂pathLaw) =
      ∫⁻ v, jointDensity n a gaps v*Φ v := by
  have hm : Measurable (fun f : Path ↦ fun i : Fin n ↦ a+f (sampleTime gaps (i.val+1))) :=
    measurable_pi_lambda _ (fun _ ↦ measurable_const.add (continuous_eval _).measurable)
  rw [← lintegral_map hΦ hm,actual_free_endpoints_density n a ha gaps hgaps,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_jointDensity n a gaps) hΦ]
  rfl

end PerronWright.BrownianKilledFiniteDimensionalDensity
