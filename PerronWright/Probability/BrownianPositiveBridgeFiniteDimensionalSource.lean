import PerronWright.Probability.BrownianPositiveBridgeConditioning
import PerronWright.Probability.BrownianBridgeSurvivalPointwise

/-! # Genuine finite coordinate constraints of a positive-endpoint bridge

The endpoint-relative density below is the probability of a literal
constraint under the actual pinned Brownian bridge. It is obtained from
the proved whole-path bridge/endpoint product, not from a conditional
Markov or excursion premise. Coordinate lower cuts make this density
monotone in the endpoint, including arbitrary finite collections of times.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeFiniteDimensionalSource

open BrownianPathLaw BrownianFirstPassageBridgeLaw ContinuousPathFirstPassage
open BrownianBridgeSurvivalPointwise BrownianPositiveBridgeConditioning

def lowerCuts {ι : Type*} (times : ι → ℝ≥0) (cuts : ι → ℝ) : Set Path :=
  {g | ∀ i, cuts i < g (times i)}

theorem measurableSet_lowerCuts {ι : Type*} [Countable ι]
    (times : ι → ℝ≥0) (cuts : ι → ℝ) : MeasurableSet (lowerCuts times cuts) := by
  have he : lowerCuts times cuts = ⋂ i, {g : Path | cuts i < g (times i)} := by
    ext g
    simp only [lowerCuts,mem_ofPred_eq,mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun i ↦ (isOpen_lt continuous_const (continuous_eval (times i))).measurableSet)

def constraint {ι : Type*} (a : ℝ) (T : ℝ≥0)
    (times : ι → ℝ≥0) (cuts : ι → ℝ) (z : ℝ) : Set Path :=
  bridgeConstraint (-a) T z ∩
    {g | ∀ i, cuts i < g (times i)+(min (times i) T : ℝ≥0)/(T : ℝ)*z+a}

theorem measurableSet_joint_constraint {ι : Type*} [Countable ι]
    (a : ℝ) (T : ℝ≥0) (times : ι → ℝ≥0) (cuts : ι → ℝ) :
    MeasurableSet {p : Path × ℝ | p.1 ∈ constraint a T times cuts p.2} := by
  have he : {p : Path × ℝ | p.1 ∈ constraint a T times cuts p.2} =
      {p : Path × ℝ | reconstruct T p ∈ survival (-a) T} ∩
        ⋂ i, {p : Path × ℝ | cuts i < p.1 (times i)+(min (times i) T : ℝ≥0)/(T : ℝ)*p.2+a} := by
    ext p
    simp only [constraint,bridgeConstraint,mem_inter_iff,mem_ofPred_eq,mem_iInter]
  rw [he]
  exact ((measurable_reconstruct T) (measurableSet_survival (-a) T)).inter
    (MeasurableSet.iInter (fun i ↦ (isOpen_lt continuous_const
      (((continuous_eval (times i)).comp continuous_fst).add
        (continuous_const.mul continuous_snd) |>.add continuous_const)).measurableSet))

theorem measurableSet_constraint {ι : Type*} [Countable ι]
    (a : ℝ) (T : ℝ≥0) (times : ι → ℝ≥0) (cuts : ι → ℝ) (z : ℝ) :
    MeasurableSet (constraint a T times cuts z) :=
  (measurable_id.prodMk measurable_const) (measurableSet_joint_constraint a T times cuts)

def probability {ι : Type*} (a : ℝ) (T : ℝ≥0)
    (times : ι → ℝ≥0) (cuts : ι → ℝ) (z : ℝ) : ℝ≥0∞ :=
  pinnedLaw T (constraint a T times cuts z)

theorem measurable_probability {ι : Type*} [Countable ι]
    (a : ℝ) (T : ℝ≥0) (times : ι → ℝ≥0) (cuts : ι → ℝ) :
    Measurable (probability a T times cuts) :=
  measurable_measure_prodMk_right (measurableSet_joint_constraint a T times cuts)

theorem constraint_subset_of_le {ι : Type*} (a : ℝ) (T : ℝ≥0)
    (times : ι → ℝ≥0) (cuts : ι → ℝ) {z z' : ℝ} (hz : z ≤ z') :
    constraint a T times cuts z ⊆ constraint a T times cuts z' := by
  rintro g ⟨hg,hcuts⟩
  refine ⟨bridgeConstraint_subset_of_le (-a) T hz hg,?_⟩
  intro i
  have hm := mul_le_mul_of_nonneg_left hz (div_nonneg (min (times i) T).coe_nonneg T.coe_nonneg)
  have hi := hcuts i
  linarith

theorem monotone_probability {ι : Type*} (a : ℝ) (T : ℝ≥0)
    (times : ι → ℝ≥0) (cuts : ι → ℝ) : Monotone (probability a T times cuts) := by
  intro z z' hz
  exact measure_mono (constraint_subset_of_le a T times cuts hz)

/-- The actual Brownian survival-and-coordinate-restricted endpoint law. -/
def endpointLaw {ι : Type*} (a : ℝ) (T : ℝ≥0)
    (times : ι → ℝ≥0) (cuts : ι → ℝ) : Measure ℝ :=
  (pathLaw.restrict (survival (-a) T ∩
    {f | ∀ i, cuts i < f (min (times i) T)+a})).map (fun f : Path ↦ f T)

theorem endpointLaw_eq_bridge_density {ι : Type*} [Countable ι]
    (a : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (times : ι → ℝ≥0) (cuts : ι → ℝ) :
    endpointLaw a T times cuts = (gaussianReal 0 T).withDensity (probability a T times cuts) := by
  ext B hB
  have hm : Measurable (fun f : Path ↦ (BrownianBridgeAreaTiltPathLaw.stoppedBridgePath T f,f T)) :=
    (BrownianBridgeAreaTiltPathLaw.measurable_stoppedBridgePath T).prodMk (continuous_eval T).measurable
  let A : Set (Path × ℝ) := {p | p.1 ∈ constraint a T times cuts p.2 ∧ p.2 ∈ B}
  have hA : MeasurableSet A := (measurableSet_joint_constraint a T times cuts).inter (measurable_snd hB)
  have he : (fun f : Path ↦ (BrownianBridgeAreaTiltPathLaw.stoppedBridgePath T f,f T)) ⁻¹' A =
      (fun f : Path ↦ f T) ⁻¹' B ∩ (survival (-a) T ∩
        {f | ∀ i, cuts i < f (min (times i) T)+a}) := by
    ext f
    simp only [A,mem_preimage,mem_ofPred_eq,constraint,bridgeConstraint,mem_inter_iff,
      reconstruct_bridge_endpoint,stopped_mem_survival_iff]
    have hi : (∀ i, cuts i < BrownianBridgeAreaTiltPathLaw.stoppedBridgePath T f (times i)+
        (min (times i) T : ℝ≥0)/(T : ℝ)*f T+a) ↔
        ∀ i, cuts i < f (min (times i) T)+a := by
      apply forall_congr'
      intro i
      change (cuts i < BrownianPinnedBridge.bridge T (min (times i) T) f+
        (min (times i) T : ℝ≥0)/(T : ℝ)*f T+a) ↔ _
      unfold BrownianPinnedBridge.bridge
      ring_nf
    rw [hi]
    tauto
  rw [endpointLaw,Measure.map_apply (continuous_eval T).measurable hB,
    Measure.restrict_apply ((continuous_eval T).measurable hB),← he,
    ← Measure.map_apply hm hA,bridge_endpoint_jointLaw T hT,Measure.prod_apply_symm hA,
    withDensity_apply _ hB,← lintegral_indicator hB]
  apply lintegral_congr
  intro z
  have hzset : (fun g : Path ↦ (g,z)) ⁻¹' A =
      if z ∈ B then constraint a T times cuts z else ∅ := by
    ext g
    by_cases hz : z ∈ B <;> simp [A,hz]
  rw [hzset]
  by_cases hz : z ∈ B
  · simp only [if_pos hz,indicator_of_mem hz,probability]
  · simp only [if_neg hz,measure_empty,indicator_of_notMem hz]

theorem positiveBridgeLaw_lowerCuts {ι : Type*} [Countable ι]
    (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T)
    (times : ι → ℝ≥0) (cuts : ι → ℝ) :
    positiveBridgeLaw a T (lowerCuts times cuts) =
      (ENNReal.ofReal (1-Real.exp (-2*a^2/(T : ℝ))))⁻¹ * probability a T times cuts 0 := by
  rw [positiveBridgeLaw,Measure.map_apply (measurable_translate a) (measurableSet_lowerCuts times cuts),
    conditionedLaw,ProbabilityTheory.cond,Measure.smul_apply,
    Measure.restrict_apply ((measurable_translate a) (measurableSet_lowerCuts times cuts)),
    BrownianBridgeSurvivalLaw.bridgeConstraint_probability_zero_endpoint a ha T hT]
  congr 1
  congr 1
  ext g
  simp only [constraint,lowerCuts,mem_inter_iff,mem_ofPred_eq,mem_preimage,
    translate_eval,mul_zero,add_zero]
  exact and_comm

end PerronWright.BrownianPositiveBridgeFiniteDimensionalSource
