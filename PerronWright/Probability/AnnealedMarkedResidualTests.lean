import PerronWright.Probability.AnnealedMarkedResidualConcentration

/-!
# Continuous joint marks under the literal residual weighting

No mark-concentration interface is assumed: each connected component,
its actual pi marginal, and the actual normalized residual density are
used.  Weak continuous joint tests are measurably sampled through the
finite type coordinates, without identifying weak and Giry Borel spaces.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedMarkedResidualTests

open AnnealedMarkedResidualLaw AnnealedMarkedResidualConcentration
  AnnealedProfileFunctionalObservable AnnealedProfileFunctionalExpectation
  AnnealedTupleResidualCounting EmpiricalMarkConcentration ProfileFiniteCollection
  ProfileSquareMoment BoundedConcentrationTransfer

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

theorem jointContinuousTest_measurable {q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i)
    (G : (Fin q → ProbabilityMeasure S) → ℝ) (hG : Continuous G) :
    Measurable (fun p : StateFamily (S := S) k ↦ G (componentMarks hk p)) := by
  have hc : Continuous (fun x : (i : Fin q) → Fin (k i) → S ↦
      G (fun i ↦ typesMark (hk i) (x i))) := hG.comp
    (continuous_pi (fun i ↦ (typesMark_continuous (hk i)).comp (continuous_apply i)))
  have hx : Measurable (fun p : StateFamily (S := S) k ↦ fun i ↦ (p i).1) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i).fst
  exact hc.measurable.comp hx

def jointContinuousTestBound {q : ℕ} (G : (Fin q → ProbabilityMeasure S) → ℝ)
    (hG : Continuous G) : ℝ :=
  ‖BoundedContinuousFunction.mkOfCompact
    (⟨G,hG⟩ : C((Fin q → ProbabilityMeasure S),ℝ))‖

theorem jointContinuousTest_abs_le {q : ℕ} (G : (Fin q → ProbabilityMeasure S) → ℝ)
    (hG : Continuous G) (ν : Fin q → ProbabilityMeasure S) :
    |G ν| ≤ jointContinuousTestBound G hG :=
  BoundedContinuousFunction.norm_coe_le_norm
    (BoundedContinuousFunction.mkOfCompact (⟨G,hG⟩ : C((Fin q → ProbabilityMeasure S),ℝ))) ν

theorem jointContinuousTest_integrable {q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i)
    (μ : Measure (StateFamily (S := S) k)) [IsFiniteMeasure μ]
    (G : (Fin q → ProbabilityMeasure S) → ℝ) (hG : Continuous G) :
    Integrable (fun p ↦ G (componentMarks hk p)) μ :=
  (integrable_const (jointContinuousTestBound G hG)).mono'
    (jointContinuousTest_measurable hk G hG).aestronglyMeasurable
    (Eventually.of_forall (fun _ ↦ jointContinuousTest_abs_le G hG _))

theorem normalizedResidual_jointContinuousTest_integrable {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ) (hn : 0 < n)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hweight : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n)) (k i) (r i))
    (G : (Fin q → ProbabilityMeasure S) → ℝ) (hG : Continuous G) :
    Integrable (fun p ↦ normalizedResidualObservable M hM lambda hk f s₀ p * G (componentMarks hk p))
      (productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hweight) :=
  (normalizedResidualObservable_integrable_alltime M hM lambda hn hk f s₀ hweight).mul_bdd
    (jointContinuousTest_measurable hk G hG).aestronglyMeasurable
    (Eventually.of_forall (fun _ ↦ jointContinuousTest_abs_le G hG _))

section Critical

variable (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hQP : M.QP)
  (R q : ℕ) (hq : 0 < q) (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C) (lambda : ℝ)
  (N : ℕ → ℕ) (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
  (f : ∀ n, Placements (N n) (k n)) (s₀ : S)
  (hweight : ∀ n i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda (N n)))
    (k n i) (r n i))
  (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
  (hkTop : ∀ i, Tendsto (fun n ↦ k n i) atTop atTop)
  (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
  (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i:ℝ) *
    ‖M.scalarField (CriticalScaling.time lambda (N n))‖ ≤ L)
  (hsize : ∀ᶠ n in atTop, (∑ i,(k n i:ℝ)) ≤ C*(N n:ℝ)^(2/3:ℝ))
  {s : ℝ} (hs : Tendsto (fun n ↦ (∑ i,k n i:ℕ)/(N n:ℝ)^(2/3:ℝ)) atTop (𝓝 s))

include hQP hq hL hC hN hNt hkTop hr hg hsize hs in
theorem weightedLaw_jointContinuousTest_l1_tendsto_zero
    (G : (Fin q → ProbabilityMeasure S) → ℝ) (hG : Continuous G) :
    Tendsto (fun n ↦ ∫ p, |G (componentMarks (hk n) p)-G (perronMarks M hM q)|
      ∂(weightedLaw M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)).toMeasure) atTop (𝓝 0) := by
  let B := jointContinuousTestBound G hG + |G (perronMarks M hM q)|
  have hbound (n : ℕ) (p : StateFamily (S := S) (k n)) :
      |G (componentMarks (hk n) p)-G (perronMarks M hM q)| ≤ B :=
    (abs_sub _ _).trans (by linarith only [jointContinuousTest_abs_le G hG (componentMarks (hk n) p)])
  apply integral_abs_tendsto_zero
    (fun n ↦ (weightedLaw M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)).toMeasure)
    (fun n p ↦ G (componentMarks (hk n) p)-G (perronMarks M hM q))
    (fun n ↦ (jointContinuousTest_measurable (hk n) G hG).sub measurable_const)
    B (by dsimp [B,jointContinuousTestBound]; positivity) hbound
  intro ε hε
  let U := {ν : Fin q → ProbabilityMeasure S | |G ν-G (perronMarks M hM q)| < ε}
  have hU : U ∈ 𝓝 (perronMarks M hM q) := by
    apply (isOpen_lt ((hG.sub continuous_const).abs) continuous_const).mem_nhds
    change |G (perronMarks M hM q)-G (perronMarks M hM q)| < ε
    simpa only [sub_self,abs_zero] using hε
  have ht := weightedLaw_outside_joint_weak_nhds_tendsto_zero M hM hQP R q hq L C hL hC lambda
    N k r hk f s₀ hweight hN hNt hkTop hr hg hsize hs U hU
  simpa only [U,Set.mem_ofPred_eq,not_lt] using ht

include hQP hq hL hC hN hNt hkTop hr hg hsize hs in
theorem weightedLaw_jointContinuousTest_integral_tendsto
    (G : (Fin q → ProbabilityMeasure S) → ℝ) (hG : Continuous G) :
    Tendsto (fun n ↦ ∫ p, G (componentMarks (hk n) p)
      ∂(weightedLaw M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)).toMeasure)
        atTop (𝓝 (G (perronMarks M hM q))) := by
  have hl := weightedLaw_jointContinuousTest_l1_tendsto_zero M hM hQP R q hq L C hL hC lambda
    N k r hk f s₀ hweight hN hNt hkTop hr hg hsize hs G hG
  have he (n : ℕ) :
      |(∫ p, G (componentMarks (hk n) p)
          ∂(weightedLaw M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)).toMeasure)-G (perronMarks M hM q)| ≤
        ∫ p, |G (componentMarks (hk n) p)-G (perronMarks M hM q)|
          ∂(weightedLaw M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)).toMeasure := by
    have hh := abs_integral_le_integral_abs (μ := (weightedLaw M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)).toMeasure)
      (f := fun p ↦ G (componentMarks (hk n) p)-G (perronMarks M hM q))
    rw [integral_sub (jointContinuousTest_integrable (hk n) _ G hG) (integrable_const _),integral_const] at hh
    simpa only [probReal_univ,smul_eq_mul,one_mul] using hh
  have hh := squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) (Eventually.of_forall he) hl
  rw [← tendsto_sub_nhds_zero_iff,tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using hh

include hQP hq hL hC hN hNt hkTop hr hg hsize hs in
/-- Actual normalized-residual weighted integrals of the component joint
mark deviation vanish.  Integrability follows from the genuine residual. -/
theorem weightedResidual_jointContinuousTest_l1_tendsto_zero
    (G : (Fin q → ProbabilityMeasure S) → ℝ) (hG : Continuous G) :
    Tendsto (fun n ↦ ∫ p, normalizedResidualObservable M hM lambda (hk n) (f n) s₀ p *
      |G (componentMarks (hk n) p)-G (perronMarks M hM q)|
      ∂productLaw M (k n) (r n) (fun _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) (hweight n))
        atTop (𝓝 0) := by
  let μ n := productLaw M (k n) (r n) (fun _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) (hweight n)
  let Z n := ∫ p, normalizedResidualObservable M hM lambda (hk n) (f n) s₀ p ∂μ n
  let A n := ∫ p, |G (componentMarks (hk n) p)-G (perronMarks M hM q)|
    ∂(weightedLaw M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)).toMeasure
  have hz : Tendsto Z atTop (𝓝 1) := (normalizedResidualObservable_l1_and_mean_tendsto
    M hM hQP R q hq L C hL hC lambda N k r hk f s₀ hweight hN hNt
    (totalSize_tendsto_of_components q hq k hkTop) hr hg hsize hs).2
  have ha : Tendsto A atTop (𝓝 0) := weightedLaw_jointContinuousTest_l1_tendsto_zero
    M hM hQP R q hq L C hL hC lambda N k r hk f s₀ hweight hN hNt hkTop hr hg hsize hs G hG
  have he (n : ℕ) : Z n*A n = ∫ p, normalizedResidualObservable M hM lambda (hk n) (f n) s₀ p *
      |G (componentMarks (hk n) p)-G (perronMarks M hM q)| ∂μ n := by
    dsimp only [A]
    rw [weightedLaw_integral]
    exact mul_div_cancel₀ _ (residualExpectation_pos M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)).ne'
  simpa only [Pi.mul_apply,one_mul,he] using hz.mul ha

include hQP hq hL hC hN hNt hkTop hr hg hsize hs in
/-- Terminal actual marked expectation: the residual-weighted joint test
has the Perron product point evaluation, with its literal normalizer. -/
theorem weightedResidual_jointContinuousTest_integral_tendsto
    (G : (Fin q → ProbabilityMeasure S) → ℝ) (hG : Continuous G) :
    Tendsto (fun n ↦ ∫ p, normalizedResidualObservable M hM lambda (hk n) (f n) s₀ p *
      G (componentMarks (hk n) p)
      ∂productLaw M (k n) (r n) (fun _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) (hweight n))
        atTop (𝓝 (G (perronMarks M hM q))) := by
  let μ n := productLaw M (k n) (r n) (fun _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) (hweight n)
  let Z n := ∫ p, normalizedResidualObservable M hM lambda (hk n) (f n) s₀ p ∂μ n
  let A n := ∫ p, G (componentMarks (hk n) p)
    ∂(weightedLaw M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)).toMeasure
  have hz : Tendsto Z atTop (𝓝 1) := (normalizedResidualObservable_l1_and_mean_tendsto
    M hM hQP R q hq L C hL hC lambda N k r hk f s₀ hweight hN hNt
    (totalSize_tendsto_of_components q hq k hkTop) hr hg hsize hs).2
  have ha : Tendsto A atTop (𝓝 (G (perronMarks M hM q))) := weightedLaw_jointContinuousTest_integral_tendsto
    M hM hQP R q hq L C hL hC lambda N k r hk f s₀ hweight hN hNt hkTop hr hg hsize hs G hG
  have he (n : ℕ) : Z n*A n = ∫ p, normalizedResidualObservable M hM lambda (hk n) (f n) s₀ p *
      G (componentMarks (hk n) p) ∂μ n := by
    dsimp only [A]
    rw [weightedLaw_integral]
    exact mul_div_cancel₀ _ (residualExpectation_pos M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)).ne'
  simpa only [Pi.mul_apply,one_mul,he] using hz.mul ha

end Critical

end PerronWright.AnnealedMarkedResidualTests
