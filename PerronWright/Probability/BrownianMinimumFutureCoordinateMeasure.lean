import PerronWright.Probability.BrownianMinimumFutureCoordinateDensity
import PerronWright.Probability.BrownianEntranceProductGeometry
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! # Actual original minimum-coordinate law under a time cutoff

The genuine supported continuous-test density determines the actual
weighted Brownian law. Equality of finite measures then extends the
formula to all nonnegative Borel tests, in particular Borel endpoint
weights needed for literal endpoint pinning. The cutoff is a concrete
bounded continuous function, not a supplied stochastic interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumFutureCoordinateMeasure

open BrownianPathLaw ContinuousPathLeastMinimum BrownianMinimumFutureCoordinates
open BrownianMinimumFutureCoordinateDensity BrownianKilledFreeEntranceTests
open BrownianKilledFreeEntranceGeometry BrownianEntranceProductGeometry
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalOrderedTimes

def originalTriple (n : ℕ) (times : Fin (n+1) → ℝ≥0) (f : Path) :
    ℝ≥0 × ℝ × FreeVector (n+1) :=
  (leastMinimizer (times (Fin.last n)) f,minimumValue (times (Fin.last n)) f,
    fun i ↦ f (times i)-minimumValue (times (Fin.last n)) f)

theorem measurable_originalTriple (n : ℕ) (times : Fin (n+1) → ℝ≥0) :
    Measurable (originalTriple n times) :=
  (measurable_leastMinimizer _).prodMk ((continuous_minimumValue _).measurable.prodMk
    (measurable_pi_lambda _ (fun i ↦ (continuous_eval (times i)).measurable.sub
      (continuous_minimumValue _).measurable)))

def actualLaw (n : ℕ) (times : Fin (n+1) → ℝ≥0) (κ : ℝ≥0 →ᵇ ℝ) :
    Measure (ℝ≥0 × ℝ × FreeVector (n+1)) :=
  (pathLaw.withDensity (fun f ↦ ENNReal.ofReal (κ (leastMinimizer (times (Fin.last n)) f)))).map
    (originalTriple n times)

instance actualLaw_isFinite (n : ℕ) (times : Fin (n+1) → ℝ≥0) (κ : ℝ≥0 →ᵇ ℝ) :
    IsFiniteMeasure (actualLaw n times κ) := by
  have hfin : (∫⁻ f, ENNReal.ofReal (κ (leastMinimizer (times (Fin.last n)) f)) ∂pathLaw) ≠ ∞ := by
    apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ‖κ‖))
    calc
      _ ≤ ∫⁻ _f : Path, ENNReal.ofReal ‖κ‖ ∂pathLaw := lintegral_mono (fun f ↦
        ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (κ.norm_coe_le_norm _)))
      _ = _ := by simp only [lintegral_const,measure_univ,mul_one]
  let := isFiniteMeasure_withDensity hfin
  unfold actualLaw
  infer_instance

def referenceMeasure (n : ℕ) (times : Fin (n+1) → ℝ≥0) :
    Measure (ℝ × ℝ × FreeVector (n+1)) :=
  (volume.restrict (Ioo (0 : ℝ) (times (Fin.last n) : ℝ))).prod
    ((volume.restrict (Ioi (0 : ℝ))).prod volume)

def residualGaps (n : ℕ) (times : Fin (n+1) → ℝ≥0) (s : ℝ) : ℕ → ℝ≥0 :=
  orderedGaps (n+1) (residualSchedule n times (Real.toNNReal s))

theorem measurable_residualGaps (n : ℕ) (times : Fin (n+1) → ℝ≥0) :
    Measurable (residualGaps n times) := by
  apply measurable_pi_lambda
  intro j
  unfold residualGaps orderedGaps finiteTimeExtension
  have hm (i : Fin (n+2)) : Measurable (fun s : ℝ ↦ residualSchedule n times (Real.toNNReal s) i) := by
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · simp only [residualSchedule_zero]
      exact measurable_const
    · simp only [residualSchedule_succ]
      exact measurable_const.sub measurable_id.real_toNNReal
  exact (hm _).sub (hm _)

def jointDensity (n : ℕ) (times : Fin (n+1) → ℝ≥0) (κ : ℝ≥0 →ᵇ ℝ)
    (p : ℝ × ℝ × FreeVector (n+1)) : ℝ≥0∞ :=
  BrownianFirstPassageDensityGeometry.density p.2.1 p.1*
    entranceJoint n (residualGaps n times p.1) p.2.2*ENNReal.ofReal (κ (Real.toNNReal p.1))

theorem measurable_jointDensity (n : ℕ) (times : Fin (n+1) → ℝ≥0) (κ : ℝ≥0 →ᵇ ℝ) :
    Measurable (jointDensity n times κ) := by
  have hg : Measurable (fun p : ℝ × ℝ × FreeVector (n+1) ↦
      (residualGaps n times p.1,p.2.2)) :=
    ((measurable_residualGaps n times).comp measurable_fst).prodMk measurable_snd.snd
  have he : Measurable (fun q : (ℕ → ℝ≥0) × FreeVector (n+1) ↦ entranceJoint n q.1 q.2) :=
    (measurable_joint_entranceNN.comp
      (by fun_prop : Measurable (fun q : (ℕ → ℝ≥0) × FreeVector (n+1) ↦ (q.1 0,q.2 0)))).mul
      (measurable_joint_internalDensity n)
  exact ((BrownianHeatResolvent.measurable_joint_passageDensity.comp
    (measurable_snd.fst.prodMk measurable_fst)).mul (he.comp hg)).mul
    (κ.continuous.measurable.comp measurable_fst.real_toNNReal).ennreal_ofReal

def encode (n : ℕ) (p : ℝ × ℝ × FreeVector (n+1)) : ℝ≥0 × ℝ × FreeVector (n+1) :=
  (Real.toNNReal p.1,-p.2.1,p.2.2)

theorem measurable_encode (n : ℕ) : Measurable (encode n) :=
  measurable_fst.real_toNNReal.prodMk (measurable_snd.fst.neg.prodMk measurable_snd.snd)

def candidateLaw (n : ℕ) (times : Fin (n+1) → ℝ≥0) (κ : ℝ≥0 →ᵇ ℝ) :
    Measure (ℝ≥0 × ℝ × FreeVector (n+1)) :=
  ((referenceMeasure n times).withDensity (jointDensity n times κ)).map (encode n)

theorem lintegral_candidateLaw (n : ℕ) (times : Fin (n+1) → ℝ≥0) (κ : ℝ≥0 →ᵇ ℝ)
    (Ψ : (ℝ≥0 × ℝ × FreeVector (n+1)) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ q, Ψ q ∂candidateLaw n times κ) =
      ∫⁻ s in Ioo 0 (times (Fin.last n) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          ∫⁻ v, entranceJoint n (residualGaps n times s) v*
            ENNReal.ofReal (κ (Real.toNNReal s))*Ψ (Real.toNNReal s,-a,v) := by
  have hm := (measurable_jointDensity n times κ).mul (hΨ.comp (measurable_encode n))
  rw [candidateLaw,lintegral_map hΨ (measurable_encode n)]
  change (∫⁻ p, (Ψ ∘ encode n) p ∂(referenceMeasure n times).withDensity (jointDensity n times κ)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_jointDensity n times κ)
    (hΨ.comp (measurable_encode n)),referenceMeasure,lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro s
  trans ∫⁻ a in Ioi (0 : ℝ), ∫⁻ v : FreeVector (n+1),
    (jointDensity n times κ*(Ψ ∘ encode n)) (s,a,v)
  · exact lintegral_prod _ (hm.comp
      (measurable_const.prodMk measurable_id : Measurable (fun p : ℝ × FreeVector (n+1) ↦ (s,p)))).aemeasurable
  apply lintegral_congr
  intro a
  simp only [jointDensity,encode,Pi.mul_apply,Function.comp_apply,mul_assoc]
  exact lintegral_const_mul _ ((measurable_entranceJoint n _).mul (measurable_const.mul
    (hΨ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))))

theorem actualLaw_eq_candidateLaw (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hstrict : StrictMono times) (hT : 0 < times (Fin.last n)) (κ : ℝ≥0 →ᵇ ℝ)
    (hκ : ∀ t, 0 ≤ κ t) (hcut : ∀ t, times 0 ≤ t → κ t = 0) :
    actualLaw n times κ = candidateLaw n times κ := by
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  let F : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ :=
    ⟨⟨fun p ↦ (f p : ℝ),NNReal.continuous_coe.comp f.continuous⟩,f.map_bounded'⟩
  let Φ := (κ.compContinuous ⟨Prod.fst,continuous_fst⟩)*F
  have hΦ : ∀ p, 0 ≤ Φ p := fun p ↦ mul_nonneg (hκ p.1) (f p).coe_nonneg
  have hc : ∀ t : ℝ≥0, times 0 ≤ t → ∀ a v, Φ (t,a,v) = 0 := by
    intro t ht a v
    change κ t*(f (t,a,v) : ℝ) = 0
    rw [hcut t ht,zero_mul]
  have he := actual_minimum_original_coordinate_density n times hstrict hT Φ hΦ hc
  have hd : Measurable (fun g : Path ↦ ENNReal.ofReal (κ (leastMinimizer (times (Fin.last n)) g))) :=
    (κ.continuous.measurable.comp (measurable_leastMinimizer _)).ennreal_ofReal
  rw [actualLaw,lintegral_map f.continuous.measurable.coe_nnreal_ennreal (measurable_originalTriple n times)]
  change (∫⁻ g, ((fun q ↦ (f q : ℝ≥0∞)) ∘ originalTriple n times) g
    ∂pathLaw.withDensity (fun g ↦ ENNReal.ofReal (κ (leastMinimizer (times (Fin.last n)) g)))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hd
    (f.continuous.measurable.coe_nnreal_ennreal.comp (measurable_originalTriple n times)),
    lintegral_candidateLaw n times κ _ f.continuous.measurable.coe_nnreal_ennreal]
  have he' : (∫⁻ g, ENNReal.ofReal (κ (leastMinimizer (times (Fin.last n)) g))*
      (f (originalTriple n times g) : ℝ≥0∞) ∂pathLaw) =
      ∫⁻ s in Ioo 0 (times (Fin.last n) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          ∫⁻ v, ENNReal.ofReal (κ (Real.toNNReal s))*(f (Real.toNNReal s,-a,v) : ℝ≥0∞)
            ∂freeEntranceLaw n (residualGaps n times s) := by
    simpa only [Φ,F,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
      BoundedContinuousFunction.coe_mk,ContinuousMap.coe_mk,ENNReal.ofReal_mul (hκ _),
      ENNReal.ofReal_coe_nnreal,originalTriple,residualGaps] using he
  simp only [Pi.mul_apply,Function.comp_apply]
  rw [he']
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro a
  congr 1
  rw [freeEntranceLaw]
  have hm : Measurable (fun v : FreeVector (n+1) ↦ ENNReal.ofReal (κ (Real.toNNReal s))*
      (f (Real.toNNReal s,-a,v) : ℝ≥0∞)) := by
    exact measurable_const.mul (f.continuous.measurable.coe_nnreal_ennreal.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_entranceJoint n _) hm]
  simp only [Pi.mul_apply]
  apply lintegral_congr
  intro v
  exact (mul_assoc _ _ _).symm

theorem actual_weighted_borel_density (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hstrict : StrictMono times) (hT : 0 < times (Fin.last n)) (κ : ℝ≥0 →ᵇ ℝ)
    (hκ : ∀ t, 0 ≤ κ t) (hcut : ∀ t, times 0 ≤ t → κ t = 0)
    (Ψ : (ℝ≥0 × ℝ × FreeVector (n+1)) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ g, ENNReal.ofReal (κ (leastMinimizer (times (Fin.last n)) g))*
      Ψ (originalTriple n times g) ∂pathLaw) =
      ∫⁻ s in Ioo 0 (times (Fin.last n) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          ∫⁻ v, entranceJoint n (residualGaps n times s) v*
            ENNReal.ofReal (κ (Real.toNNReal s))*Ψ (Real.toNNReal s,-a,v) := by
  have hd : Measurable (fun g : Path ↦ ENNReal.ofReal (κ (leastMinimizer (times (Fin.last n)) g))) :=
    (κ.continuous.measurable.comp (measurable_leastMinimizer _)).ennreal_ofReal
  change (∫⁻ g, ((fun g ↦ ENNReal.ofReal (κ (leastMinimizer (times (Fin.last n)) g)))*
    (Ψ ∘ originalTriple n times)) g ∂pathLaw) = _
  rw [← lintegral_withDensity_eq_lintegral_mul _ hd (hΨ.comp (measurable_originalTriple n times))]
  simp only [Function.comp_apply]
  rw [← lintegral_map hΨ (measurable_originalTriple n times)]
  change (∫⁻ p, Ψ p ∂actualLaw n times κ) = _
  rw [actualLaw_eq_candidateLaw n times hstrict hT κ hκ hcut,lintegral_candidateLaw n times κ Ψ hΨ]

end PerronWright.BrownianMinimumFutureCoordinateMeasure
