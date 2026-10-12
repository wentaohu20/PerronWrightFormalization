import PerronWright.Probability.BrownianKilledFiniteDimensionalCoordinates

/-! # Actual arbitrary finite surviving Brownian endpoint laws

Every finite ordered tuple is sampled from the actual continuous path
law with its literal whole-interval survival gate. Deterministic past and
future independence proves the one-step joint law, and induction identifies
the entire tuple law with the iterated genuine killed transition chain.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledFiniteDimensionalLaw

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathReflection
open ContinuousPathFirstPassage BrownianKilledSemigroup
open BrownianKilledFiniteDimensionalCoordinates

def actualTupleLaw (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) : Measure (EndpointVector n) :=
  (pathLaw.restrict (survival (level-x) (sampleTime gaps n))).map (endpointTuple n x gaps)

instance actualTupleLaw_isFinite (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    IsFiniteMeasure (actualTupleLaw level x gaps n) := by
  unfold actualTupleLaw
  infer_instance

theorem actualTupleLaw_apply (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ)
    {D : Set (EndpointVector n)} (hD : MeasurableSet D) :
    actualTupleLaw level x gaps n D =
      pathLaw {f : Path | f ∈ survival (level-x) (sampleTime gaps n) ∧ endpointTuple n x gaps f ∈ D} := by
  rw [actualTupleLaw,Measure.map_apply (continuous_endpointTuple n x gaps).measurable hD,
    Measure.restrict_apply ((continuous_endpointTuple n x gaps).measurable hD)]
  congr 1
  ext f
  simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq]
  exact and_comm

theorem lintegral_headTuple_past (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ)
    {F : EndpointVector n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p in survival (level-x) (sampleTime gaps n), F (endpointTuple n x gaps p)
        ∂pastLaw (sampleTime gaps n)) = ∫⁻ v, F v ∂actualTupleLaw level x gaps n := by
  rw [actualTupleLaw,lintegral_map hF (continuous_endpointTuple n x gaps).measurable]
  have hI : Measurable ((survival (level-x) (sampleTime gaps n)).indicator
      (fun p : Path ↦ F (endpointTuple n x gaps p))) :=
    (hF.comp (continuous_endpointTuple n x gaps).measurable).indicator (measurableSet_survival _ _)
  rw [← lintegral_indicator (measurableSet_survival _ _),
    ← lintegral_indicator (measurableSet_survival _ _),pastLaw,
    lintegral_map hI (measurable_pastPath _)]
  apply lintegral_congr
  intro f
  by_cases hf : f ∈ survival (level-x) (sampleTime gaps n)
  · have hp := (past_survival_iff (level-x) (sampleTime gaps n) f).mpr hf
    simp only [indicator_of_mem hf,indicator_of_mem hp,endpointTuple_past]
  · have hp : pastPath (sampleTime gaps n) f ∉ survival (level-x) (sampleTime gaps n) :=
      (past_survival_iff (level-x) (sampleTime gaps n) f).not.mpr hf
    simp only [indicator_of_notMem hf,indicator_of_notMem hp]

def actualNextPairLaw (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    Measure (EndpointVector n × ℝ) :=
  (pathLaw.restrict (survival (level-x) (sampleTime gaps (n+1)))).map
    (fun f : Path ↦ (endpointTuple n x gaps f,x+f (sampleTime gaps (n+1))))

instance actualNextPairLaw_isFinite (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    IsFiniteMeasure (actualNextPairLaw level x gaps n) := by
  unfold actualNextPairLaw
  infer_instance

theorem actualNextPairLaw_apply (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ)
    {D : Set (EndpointVector n × ℝ)} (hD : MeasurableSet D) :
    actualNextPairLaw level x gaps n D =
      pathLaw {f : Path | f ∈ survival (level-x) (sampleTime gaps (n+1)) ∧
        (endpointTuple n x gaps f,x+f (sampleTime gaps (n+1))) ∈ D} := by
  have hm : Measurable (fun f : Path ↦ (endpointTuple n x gaps f,x+f (sampleTime gaps (n+1)))) :=
    (continuous_endpointTuple n x gaps).measurable.prodMk
      (measurable_const.add (continuous_eval _).measurable)
  rw [actualNextPairLaw,Measure.map_apply hm hD,Measure.restrict_apply (hm hD)]
  congr 1
  ext f
  simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq]
  exact and_comm

def tupleSegmentEvent (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ)
    (D : Set (EndpointVector n × ℝ)) : Set (Path × Path) :=
  {p | p.1 ∈ survival (level-x) (sampleTime gaps n) ∧
    p.2 ∈ survival (level-(x+p.1 (sampleTime gaps n))) (gaps n) ∧
    (endpointTuple n x gaps p.1,x+p.1 (sampleTime gaps n)+p.2 (gaps n)) ∈ D}

theorem measurableSet_tupleSegmentEvent (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ)
    {D : Set (EndpointVector n × ℝ)} (hD : MeasurableSet D) :
    MeasurableSet (tupleSegmentEvent level x gaps n D) := by
  have hv : Continuous (fun p : Path × Path ↦ x+p.1 (sampleTime gaps n)) :=
    continuous_const.add ((continuous_eval _).comp continuous_fst)
  have hy : Continuous (fun p : Path × Path ↦ p.2 (gaps n)) :=
    (continuous_eval _).comp continuous_snd
  exact (measurable_fst (measurableSet_survival _ _)).inter
    (((isOpen_lt (continuous_const.sub hv)
      ((continuous_minimum_at _).comp continuous_snd)).measurableSet).inter
      ((((continuous_endpointTuple n x gaps).comp continuous_fst).prodMk
        (hv.add hy)).measurable hD))

theorem tupleSegmentEvent_preimage (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ)
    (D : Set (EndpointVector n × ℝ)) :
    (fun f : Path ↦ (pastPath (sampleTime gaps n) f,futurePath (sampleTime gaps n) f)) ⁻¹'
        tupleSegmentEvent level x gaps n D =
      {f : Path | f ∈ survival (level-x) (sampleTime gaps (n+1)) ∧
        (endpointTuple n x gaps f,x+f (sampleTime gaps (n+1))) ∈ D} := by
  ext f
  have hl : level-x-f (sampleTime gaps n) = level-(x+f (sampleTime gaps n)) := by ring
  simp only [mem_preimage,tupleSegmentEvent,mem_ofPred_eq,pastPath_eval,min_self,
    past_survival_iff,endpointTuple_past,sampleTime_succ,survival_add_iff,hl,endpoint_add,add_assoc]
  exact and_assoc.symm

/-- The actual whole-history next-endpoint law. All deterministic head
coordinates are retained, rather than replaced by a two-point marginal. -/
theorem actualNextPairLaw_eq_compProd (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    actualNextPairLaw level x gaps n =
      (actualTupleLaw level x gaps n) ⊗ₘ endpointKernel n level (gaps n) := by
  ext D hD
  have hm : Measurable (fun v : EndpointVector n ↦
      endpointKernel n level (gaps n) v ((fun y : ℝ ↦ (v,y)) ⁻¹' D)) :=
    (endpointKernel n level (gaps n)).measurable_kernel_prodMk_left hD
  rw [Measure.compProd_apply hD,← lintegral_headTuple_past level x gaps n hm]
  let A := tupleSegmentEvent level x gaps n D
  have hA : MeasurableSet A := measurableSet_tupleSegmentEvent level x gaps n hD
  have hj : Measurable (fun f : Path ↦
      (pastPath (sampleTime gaps n) f,futurePath (sampleTime gaps n) f)) :=
    (measurable_pastPath _).prodMk (measurable_futurePath _)
  have he : actualNextPairLaw level x gaps n D = ((pastLaw (sampleTime gaps n)).prod pathLaw) A := by
    rw [← past_future_jointLaw (sampleTime gaps n),Measure.map_apply hj hA,
      tupleSegmentEvent_preimage,actualNextPairLaw_apply level x gaps n hD]
  rw [he,Measure.prod_apply hA,← lintegral_indicator (measurableSet_survival _ _)]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ survival (level-x) (sampleTime gaps n)
  · have hxD : MeasurableSet ((fun y : ℝ ↦ (endpointTuple n x gaps p,y)) ⁻¹' D) :=
      (measurable_const.prodMk measurable_id) hD
    rw [indicator_of_mem hp,endpointKernel_apply,endpointTuple_last,
      transitionLaw_apply level (gaps n) (x+p (sampleTime gaps n)) hxD]
    congr 1
    ext g
    simp only [A,tupleSegmentEvent,tailEvent,mem_preimage,mem_ofPred_eq,hp,true_and]
  · have he : (fun g : Path ↦ (p,g)) ⁻¹' A = ∅ := by
      ext g
      simp only [A,tupleSegmentEvent,mem_preimage,mem_ofPred_eq,hp,false_and,mem_empty_iff_false]
    rw [he,measure_empty,indicator_of_notMem hp]

theorem actualTupleLaw_succ (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    actualTupleLaw level x gaps (n+1) =
      ((actualTupleLaw level x gaps n) ⊗ₘ endpointKernel n level (gaps n)).map (appendEndpoint n) := by
  have hm : Measurable (fun f : Path ↦
      (endpointTuple n x gaps f,x+f (sampleTime gaps (n+1)))) :=
    (continuous_endpointTuple n x gaps).measurable.prodMk
      (measurable_const.add (continuous_eval _).measurable)
  rw [← actualNextPairLaw_eq_compProd,actualNextPairLaw,
    Measure.map_map (continuous_appendEndpoint n).measurable hm,actualTupleLaw]
  congr 1
  exact funext (endpointTuple_succ n x gaps)

theorem actualTupleLaw_zero (level x : ℝ) (gaps : ℕ → ℝ≥0) :
    actualTupleLaw level x gaps 0 = if level < x then Measure.dirac (fun _ ↦ x) else 0 := by
  ext D hD
  rw [actualTupleLaw_apply level x gaps 0 hD]
  have he : {f : Path | f ∈ survival (level-x) (sampleTime gaps 0) ∧ endpointTuple 0 x gaps f ∈ D}
      =ᵐ[pathLaw] (if level < x ∧ (fun _ : Fin 1 ↦ x) ∈ D
        then (univ : Set Path) else (∅ : Set Path)) := by
    filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
    have hv : endpointTuple 0 x gaps f = fun _ ↦ x := by
      funext i
      have hi : i.val = 0 := by omega
      simp only [endpointTuple,hi,sampleTime_zero,hf,add_zero]
    have hs : f ∈ survival (level-x) (sampleTime gaps 0) ↔ level < x := by
      change level-x < runningMinimum f (sampleTime gaps 0) ↔ level < x
      rw [sampleTime_zero,runningMinimum_zero,hf]
      constructor <;> intro h <;> linarith
    apply propext
    change (f ∈ survival (level-x) (sampleTime gaps 0) ∧ endpointTuple 0 x gaps f ∈ D) ↔
      f ∈ (if level < x ∧ (fun _ : Fin 1 ↦ x) ∈ D then (univ : Set Path) else ∅)
    simp only [hs,hv]
    split_ifs <;> simp_all
  rw [measure_congr he]
  by_cases hx : level < x <;> by_cases hc : (fun _ : Fin 1 ↦ x) ∈ D <;>
    simp [hx,hc,Measure.dirac_apply' _ hD]

/-- Genuine arbitrary finite-dimensional surviving endpoint chain,
including the initial point and all ordered nonnegative time gaps. -/
theorem actualTupleLaw_eq_chainLaw (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    actualTupleLaw level x gaps n = chainLaw level x gaps n := by
  induction n with
  | zero => exact actualTupleLaw_zero level x gaps
  | succ n ih => rw [actualTupleLaw_succ,ih,chainLaw_succ]

theorem lintegral_actualTuple_eq_chain (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ)
    {Φ : EndpointVector n → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f in survival (level-x) (sampleTime gaps n), Φ (endpointTuple n x gaps f) ∂pathLaw) =
      ∫⁻ v, Φ v ∂chainLaw level x gaps n := by
  rw [← actualTupleLaw_eq_chainLaw,actualTupleLaw,
    lintegral_map hΦ (continuous_endpointTuple n x gaps).measurable]

theorem lintegral_actualTuple_succ_kernel (level x : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ)
    {Φ : EndpointVector (n+1) → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f in survival (level-x) (sampleTime gaps (n+1)),
        Φ (endpointTuple (n+1) x gaps f) ∂pathLaw) =
      ∫⁻ v, ∫⁻ y, Φ (appendEndpoint n (v,y)) ∂transitionLaw level (gaps n) (v (Fin.last n))
        ∂chainLaw level x gaps n := by
  rw [lintegral_actualTuple_eq_chain level x gaps (n+1) hΦ]
  exact lintegral_chainLaw_succ level x gaps n hΦ

/-- Every nondecreasing deterministic-time source tuple starting at time
zero has the genuine ordered-gap killed chain law. Times may coincide. -/
theorem ordered_endpoint_law (level x : ℝ) (times : ℕ → ℝ≥0)
    (hmono : Monotone times) (hzero : times 0 = 0) (n : ℕ) :
    (pathLaw.restrict (survival (level-x) (times n))).map
        (fun f : Path ↦ fun i : Fin (n+1) ↦ x+f (times i.val)) =
      chainLaw level x (fun j ↦ times (j+1)-times j) n := by
  have ht : sampleTime (fun j ↦ times (j+1)-times j) = times :=
    funext (sampleTime_ordered times hmono hzero)
  have h := actualTupleLaw_eq_chainLaw level x (fun j ↦ times (j+1)-times j) n
  unfold actualTupleLaw endpointTuple at h
  rw [ht] at h
  exact h

end PerronWright.BrownianKilledFiniteDimensionalLaw
