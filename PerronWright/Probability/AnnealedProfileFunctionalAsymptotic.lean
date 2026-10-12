import PerronWright.Probability.AnnealedProfileFunctionalExpectation

/-!
# Genuine annealed residual asymptotic with literal finite-population selection

The residual is the paper's actual falling-selection ratio times its
actual connected-product-law expectation.  Its limit follows from the
proved normalized observable expectation and the proved selection
correction, not a residual-asymptotic interface.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedProfileFunctionalAsymptotic

open AnnealedProfileFunctionalExpectation AnnealedProfileFunctionalObservable
  AnnealedTupleResidualCounting AnnealedTupleResidualConnectedLawCoordinates
  ProfileFiniteCollection CriticalResidualScaling

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

/-- The literal annealed residual in the exact component factorial formula. -/
def annealedResidual {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (lambda : ℝ) (hk : ∀ i, 0 < k i)
    (f : Placements n k) (s₀ : S)
    (hweight : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n)) (k i) (r i)) : ℝ :=
  ((n.descFactorial (∑ i,k i):ℝ)/(n:ℝ)^(∑ i,k i)) *
    ∫ p, residualObservable M (CriticalScaling.time lambda n) hk f s₀ p
      ∂productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hweight

/-- Terminal normalized literal expectation with the deterministic
exponential explicitly outside the genuine product-law integral. -/
theorem normalized_residual_expectation_tendsto_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hQP : M.QP)
    (R q : ℕ) (hq : 0 < q) (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C) (lambda : ℝ)
    (N : ℕ → ℕ) (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (f : ∀ n, Placements (N n) (k n)) (s₀ : S)
    (hweight : ∀ n i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda (N n)))
      (k n i) (r n i))
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (hKTop : Tendsto (fun n ↦ ∑ i,(k n i:ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i:ℝ) *
      ‖M.scalarField (CriticalScaling.time lambda (N n))‖ ≤ L)
    (hsize : ∀ᶠ n in atTop, (∑ i,(k n i:ℝ)) ≤ C*(N n:ℝ)^(2/3:ℝ))
    {s : ℝ} (hs : Tendsto (fun n ↦ (∑ i,k n i:ℕ)/(N n:ℝ)^(2/3:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n ↦
      Real.exp (-(∑ i,(k n i:ℝ))^2/(2*(N n:ℝ)) -
        (∑ i,(k n i:ℝ))^3/(6*(N n:ℝ)^2) - perronExponent M hM lambda (N n) (∑ i,k n i)) *
      ∫ p, residualObservable M (CriticalScaling.time lambda (N n)) (hk n) (f n) s₀ p
        ∂productLaw M (k n) (r n) (fun _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) (hweight n))
      atTop (𝓝 1) := by
  have hh := (normalizedResidualObservable_l1_and_mean_tendsto M hM hQP R q hq L C hL hC lambda
    N k r hk f s₀ hweight hN hNt hKTop hr hg hsize hs).2
  simpa only [normalizedResidualObservable,integral_const_mul,neg_div] using hh

/-- The genuine selected-component annealed residual, after its actual
Perron thermal/cubic normalization, tends to one. -/
theorem annealedResidual_perron_normalization_tendsto_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hQP : M.QP)
    (R q : ℕ) (hq : 0 < q) (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C) (lambda : ℝ)
    (N : ℕ → ℕ) (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (f : ∀ n, Placements (N n) (k n)) (s₀ : S)
    (hweight : ∀ n i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda (N n)))
      (k n i) (r n i))
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (hKTop : Tendsto (fun n ↦ ∑ i,(k n i:ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i:ℝ) *
      ‖M.scalarField (CriticalScaling.time lambda (N n))‖ ≤ L)
    (hsize : ∀ᶠ n in atTop, (∑ i,(k n i:ℝ)) ≤ C*(N n:ℝ)^(2/3:ℝ))
    {s : ℝ} (hs : Tendsto (fun n ↦ (∑ i,k n i:ℕ)/(N n:ℝ)^(2/3:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n ↦ Real.exp (-perronExponent M hM lambda (N n) (∑ i,k n i)) *
      annealedResidual M lambda (hk n) (f n) s₀ (hweight n)) atTop (𝓝 1) := by
  let K n : ℕ := ∑ i,k n i
  have hsizeK : ∀ᶠ n in atTop, (K n:ℝ) ≤ C*(N n:ℝ)^(2/3:ℝ) := by
    simpa only [K,Nat.cast_sum] using hsize
  have hselection := FinitePopulationLog.selection_leading_correction_tendsto_one N K hN hNt hC hsizeK
  have hres := normalized_residual_expectation_tendsto_one M hM hQP R q hq L C hL hC lambda
    N k r hk f s₀ hweight hN hNt hKTop hr hg hsize hs
  have hh := hselection.mul hres
  simp only [mul_one] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  dsimp only [K,annealedResidual]
  rw [Nat.cast_sum]
  let a : ℝ := (∑ i,(k n i:ℝ))^2/(2*(N n:ℝ))
  let b : ℝ := (∑ i,(k n i:ℝ))^3/(6*(N n:ℝ)^2)
  let P := perronExponent M hM lambda (N n) (∑ i,k n i)
  have he : Real.exp (a+b) * Real.exp (-a-b-P) = Real.exp (-P) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [neg_div]
  change (_ * Real.exp (a+b)) * (Real.exp (-a-b-P) * _) = _
  calc
    _ = ((((N n).descFactorial (∑ i,k n i):ℝ)/(N n:ℝ)^(∑ i,k n i)) *
      (∫ p, residualObservable M (CriticalScaling.time lambda (N n)) (hk n) (f n) s₀ p
        ∂productLaw M (k n) (r n) (fun _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) (hweight n))) *
      (Real.exp (a+b)*Real.exp (-a-b-P)) := by ring
    _ = _ := by rw [he]; ring

/-- The paper's explicit compact-model annealed residual limit for the
literal finite-size expectation and the literal falling-selection ratio. -/
theorem annealedResidual_tendsto
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hQP : M.QP)
    (R q : ℕ) (hq : 0 < q) (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C) (lambda : ℝ)
    (N : ℕ → ℕ) (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (f : ∀ n, Placements (N n) (k n)) (s₀ : S)
    (hweight : ∀ n i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda (N n)))
      (k n i) (r n i))
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (hKTop : Tendsto (fun n ↦ ∑ i,(k n i:ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i:ℝ) *
      ‖M.scalarField (CriticalScaling.time lambda (N n))‖ ≤ L)
    (hsize : ∀ᶠ n in atTop, (∑ i,(k n i:ℝ)) ≤ C*(N n:ℝ)^(2/3:ℝ))
    {s : ℝ} (hs : Tendsto (fun n ↦ (∑ i,k n i:ℕ)/(N n:ℝ)^(2/3:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n ↦ annealedResidual M lambda (hk n) (f n) s₀ (hweight n)) atTop
      (𝓝 (Real.exp (lambda*M.alpha hM*s^2/2-M.beta hM*s^3/6))) := by
  have hn := annealedResidual_perron_normalization_tendsto_one M hM hQP R q hq L C hL hC lambda
    N k r hk f s₀ hweight hN hNt hKTop hr hg hsize hs
  have hp := perron_residual_exponent_tendsto N (fun n ↦ ∑ i,k n i) hN hNt lambda
    (M.alpha hM) (M.beta hM) hs
  change Tendsto (fun n ↦ perronExponent M hM lambda (N n) (∑ i,k n i)) atTop _ at hp
  have hh := hn.mul (Real.continuous_exp.tendsto _ |>.comp hp)
  simp only [one_mul] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  dsimp only [Function.comp_apply]
  rw [mul_assoc,mul_comm (annealedResidual M lambda (hk n) (f n) s₀ (hweight n)),← mul_assoc,
    ← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]

end PerronWright.AnnealedProfileFunctionalAsymptotic
