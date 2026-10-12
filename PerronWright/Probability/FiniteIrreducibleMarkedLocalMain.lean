import PerronWright.Probability.FiniteIrreducibleMarkedFactorialFormula
import PerronWright.Probability.FiniteIrreducibleMarkedResidualTransfer
import PerronWright.Probability.FiniteIrreducibleNumericalFactorialAssembly

/-! # Genuine deterministic finite marked local factorial density

The source is the actual ordered distinct component sum, evaluated under
the graph law conditional on a literal fixed type assignment. Arbitrary
O(1)-rounded type counts are allowed. Coupled continuous empirical mark
tests have the canonical Perron mark evaluation in the leading density.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology Real
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleMarkedLocalMain

open FiniteIrreducibleMarkedFactorialFormula FiniteIrreducibleMarkedResidualTransfer
open FiniteIrreducibleNativeMarkConcentration FiniteIrreducibleCriticalPrefactorScaling
open FiniteIrreducibleNumericalFactorialAssembly FiniteIrreducibleFactorialDensityFloor
open FiniteIrreducibleCriticalTuplePrefactor (enumerationPrefactor)
open FiniteIrreduciblePerronCountExpansion (mainExponent)
open FiniteIrreducibleResidualNormalization (normalizedResidual)
open FiniteIrreducibleDeterministicResidualWeights (residual)
open FiniteIrreducibleDeterministicConnectedLawFormula (connectedProductLaw)
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)
open AnnealedMarkedFactorialCounting (markedCount)
open AnnealedMarkedResidualConcentration (componentMarks)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def scaledMarkedFactorialExpectation (M : FiniteIrreducibleModel S) (lambda : ℝ)
    (n : ℕ) {q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) : ℝ :=
  (n : ℝ) ^ (2 * (q : ℝ) / 3) *
    (∫ G, markedCount x G k r Ψ
      ∂FiniteIrreducibleTypedGraphLaw.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) x)

theorem scaledMarkedFactorialExpectation_eq_numericalFactor_mul_integral
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (lambda : ℝ)
    {n q : ℕ} (hn : 0 < n) (ht : 0 < CriticalScaling.time lambda n)
    (x : Fin n → S) (c : S → ℕ) (hc : ∀ a, fiberCount x a = c a)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k i) (r i))
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    scaledMarkedFactorialExpectation M lambda n x k r Ψ =
      numericalFactor M hM n k r (CriticalScaling.time lambda n) *
        (∫ p, normalizedResidual M hM lambda n c p * Ψ (componentMarks hk p)
          ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) := by
  let E := mainExponent M hM (n : ℝ) (∑ i, (k i : ℝ)) (CriticalScaling.time lambda n)
  have hcancel : Real.exp E *
      (∫ p, normalizedResidual M hM lambda n c p * Ψ (componentMarks hk p)
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) =
      (∫ p, residual M (CriticalScaling.time lambda n) n c p * Ψ (componentMarks hk p)
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) := by
    have he : (fun p ↦ normalizedResidual M hM lambda n c p * Ψ (componentMarks hk p)) =
        (fun p ↦ (residual M (CriticalScaling.time lambda n) n c p * Ψ (componentMarks hk p)) *
          Real.exp (-E)) := by funext p; unfold normalizedResidual; dsimp only [E]; ring
    rw [he, integral_mul_const, Real.exp_neg]
    field_simp
  have hexact := marked_factorial_expectation_connectedLaw_residual_formula M
    (CriticalScaling.time lambda n) ht hn x c hc k r hk pos Ψ
  unfold scaledMarkedFactorialExpectation
  rw [hexact]
  change ((n : ℝ) ^ (2 * (q : ℝ) / 3) *
    (enumerationPrefactor M n k r (CriticalScaling.time lambda n) * _)) = _
  unfold numericalFactor
  rw [Nat.cast_sum]
  change _ = ((n : ℝ) ^ (2 * (q : ℝ) / 3) * enumerationPrefactor M n k r (CriticalScaling.time lambda n) *
    Real.exp E) * _
  rw [← hcancel]
  ring

private theorem marked_product_error (A u d v : ℝ) :
    |A * u - d * v| ≤ |A| * |u - v| + |A - d| * |v| := by
  have he : A * u - d * v = A * (u - v) + (A - d) * v := by ring
  rw [he]
  exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])

/-- Full integer-window marked local-main for the genuine fixed-assignment
graph law. The Perron value is proved by actual profile concentration and
actual residual averaging, not supplied as a marked theorem interface. -/
theorem eventually_uniform_marked_factorial_density
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → S, (∀ s, fiberCount x s = c n s) →
      ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      |scaledMarkedFactorialExpectation M lambda n x k r Ψ -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (k i)) r * Ψ (perronMarks M hM q)| < ε := by
  obtain ⟨C, hC, hbound⟩ := FactorialDensity.exists_density_window_bound
    (b := b) (M.beta_pos hM) ha R
  let B := C ^ q * Real.exp (-M.beta hM * (a * q) ^ 3 / 24)
  have hB : 0 < B := mul_pos (pow_pos hC _) (Real.exp_pos _)
  let v := Ψ (perronMarks M hM q)
  let δ := min 1 (ε / (2 * (|v| + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  let η := ε / (2 * (B + 1))
  have hη : 0 < η := by dsimp only [η]; positivity
  filter_upwards [eventually_uniform_numericalFactor_actual_time M hM q R lambda a b ha hb hδ,
    eventually_uniform_weighted_joint_mark_test M hM R q hq lambda a b ha hb c D hD hround Ψ hΨ hη,
    eventually_ge_atTop (1 : ℕ),
    (CriticalScaling.time_tendsto lambda).eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hnum hmark hn1 ht
  intro x hc k r hka hkb hr
  have hn : 0 < n := by omega
  obtain ⟨hk, pos, hw⟩ := hmark k r hka hkb hr
  have herr := hnum k r hka hkb hr
  have hd := FactorialDensity.density_pos (M.alpha hM) lambda (M.beta_pos hM)
    (fun i ↦ normalizedSize n (k i)) r (fun i ↦ ha.trans_le (hka i))
  have hdB := hbound q (M.alpha hM) lambda (fun i ↦ normalizedSize n (k i)) r
    (fun i ↦ ⟨hka i, hkb i⟩) hr
  have hnumB : |numericalFactor M hM n k r (CriticalScaling.time lambda n)| ≤ B + 1 := by
    have hh := abs_add_le
      (numericalFactor M hM n k r (CriticalScaling.time lambda n) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda (fun i ↦ normalizedSize n (k i)) r)
      (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda (fun i ↦ normalizedSize n (k i)) r)
    rw [sub_add_cancel, abs_of_pos hd] at hh
    exact hh.trans (by have := herr.trans_le (min_le_left (1 : ℝ) _); linarith)
  have he1 : |numericalFactor M hM n k r (CriticalScaling.time lambda n)| *
      |(∫ p, normalizedResidual M hM lambda n (c n) p * Ψ (componentMarks hk p)
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) - v| ≤ ε / 2 := by
    calc
      _ ≤ (B + 1) * η := mul_le_mul hnumB hw (abs_nonneg _) (by linarith)
      _ = ε / 2 := by dsimp only [η]; field_simp
  have he2 : |numericalFactor M hM n k r (CriticalScaling.time lambda n) -
      FactorialDensity.density (M.alpha hM) (M.beta hM) lambda (fun i ↦ normalizedSize n (k i)) r| * |v| < ε / 2 := by
    have hh := herr.trans_le (min_le_right (1 : ℝ) _)
    have hpos : 0 < ε / (2 * (|v| + 1)) := by positivity
    calc
      _ ≤ |numericalFactor M hM n k r (CriticalScaling.time lambda n) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda (fun i ↦ normalizedSize n (k i)) r| * (|v| + 1) := by
        gcongr; linarith
      _ < (ε / (2 * (|v| + 1))) * (|v| + 1) :=
        mul_lt_mul_of_pos_right hh (by positivity)
      _ = ε / 2 := by field_simp
  rw [scaledMarkedFactorialExpectation_eq_numericalFactor_mul_integral M hM lambda hn ht x (c n) hc k r hk pos Ψ]
  exact (marked_product_error _ _ _ _).trans_lt (by linarith [he1, he2])

/-- Literal floor-size marked local-main, uniform on the paper size window. -/
theorem eventually_uniform_floor_marked_factorial_density
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → S, (∀ s, fiberCount x s = c n s) →
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |scaledMarkedFactorialExpectation M lambda n x (fun i ↦ CriticalScaling.size (y i) n) r Ψ -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r * Ψ (perronMarks M hM q)| < ε := by
  let v := Ψ (perronMarks M hM q)
  let δ := ε / (2 * (|v| + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  filter_upwards [eventually_uniform_marked_factorial_density M hM q R hq lambda (a / 2) b
      (by linarith) hb c D hD hround Ψ hΨ (show 0 < ε / 2 by positivity),
    eventually_uniform_floor_density (M.alpha hM) (M.beta hM) lambda q R a b ha hδ,
    eventually_floor_normalized_box q a b ha] with n hn hd hbox
  intro x hc y r hya hyb hr
  have hw := hbox y hya hyb
  have he1 := hn x hc (fun i ↦ CriticalScaling.size (y i) n) r hw.1 hw.2 hr
  have he2 := hd y r hya hyb hr
  have he2' : |(FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
        (fun i ↦ normalizedSize n (CriticalScaling.size (y i) n)) r -
      FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r) * v| < ε / 2 := by
    rw [abs_mul]
    calc
      _ ≤ |FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (CriticalScaling.size (y i) n)) r -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| * (|v| + 1) := by gcongr; linarith
      _ < δ * (|v| + 1) := mul_lt_mul_of_pos_right he2 (by positivity)
      _ = ε / 2 := by dsimp only [δ]; field_simp
  have hh := abs_sub_le (scaledMarkedFactorialExpectation M lambda n x (fun i ↦ CriticalScaling.size (y i) n) r Ψ)
    (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
      (fun i ↦ normalizedSize n (CriticalScaling.size (y i) n)) r * v)
    (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r * v)
  have hsub : FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
      (fun i ↦ normalizedSize n (CriticalScaling.size (y i) n)) r * v -
      FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r * v =
      (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
        (fun i ↦ normalizedSize n (CriticalScaling.size (y i) n)) r -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r) * v := by ring
  rw [hsub] at hh
  exact hh.trans_lt (by linarith [he1, he2'])

end PerronWright.FiniteIrreducibleMarkedLocalMain
