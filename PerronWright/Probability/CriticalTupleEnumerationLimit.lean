import PerronWright.Probability.CriticalTuplePrefactor

/-! # Literal tuple enumeration contribution to the factorial density -/

open Filter Topology
open scoped BigOperators Real Topology

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.CriticalTupleEnumerationLimit

theorem density_factorization {q : ℕ} (alpha beta lambda : ℝ)
    (s : Fin q → ℝ) (r : Fin q → ℕ) :
    Real.exp (lambda*alpha*(∑ i,s i)^2/2-beta*(∑ i,s i)^3/6) *
      (∏ i, FactorialDensity.sizeFactor beta (s i) (r i) *
        Real.exp (-(alpha^2/(2*beta))*(lambda^2*s i))) =
      FactorialDensity.density alpha beta lambda s r := by
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  have hsum : (∑ i, -(alpha^2/(2*beta))*(lambda^2*s i)) =
      -(alpha^2/(2*beta))*lambda^2*(∑ i,s i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hexp : lambda*alpha*(∑ i,s i)^2/2-beta*(∑ i,s i)^3/6 +
      (∑ i, -(alpha^2/(2*beta))*(lambda^2*s i)) =
      -FactorialDensity.criticalExponent alpha beta lambda (∑ i,s i) := by
    rw [hsum]
    unfold FactorialDensity.criticalExponent
    ring
  unfold FactorialDensity.density
  rw [← hexp, Real.exp_add]
  ring

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Actual critical connected weights and actual integer factorials,
with all floor errors and critical-time conversion already proved. -/
theorem tuple_enumeration_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) {q : ℕ} (r : Fin q → ℕ)
    (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (x : ℕ → Fin q → ℝ) (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hxa : ∀ m i, a ≤ x m i) (hxb : ∀ m i, x m i ≤ b)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i)
    (hxs : ∀ i, Tendsto (fun m ↦ x m i) atTop (𝓝 (s i))) :
    Tendsto (fun m ↦ ∏ i, (N m : ℝ)^(5/3-(r i : ℝ)) *
      (M.connectedWeight (CriticalScaling.time lambda (N m))
        (CriticalScaling.size (x m i) (N m)) (r i) /
        ((CriticalScaling.size (x m i) (N m)).factorial : ℝ)))
      atTop (𝓝 (∏ i, FactorialDensity.sizeFactor (M.beta hM) (s i) (r i) *
        Real.exp (-CriticalWindowRadiusConversion.criticalQuadraticRate M hM*(lambda^2*s i)))) := by
  exact tendsto_finsetProd Finset.univ (fun i _ ↦
    CriticalLocalSizeFactor.single_component_enumeration_tendsto M hM (r i)
      N hN hNt (fun m ↦ x m i) lambda a b ha hb
      (fun m ↦ hxa m i) (fun m ↦ hxb m i) (hs i) (hxs i))

end PerronWright.CriticalTupleEnumerationLimit
