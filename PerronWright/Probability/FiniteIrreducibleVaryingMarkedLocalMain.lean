import PerronWright.Probability.FiniteIrreducibleMarkedLocalMain
import PerronWright.Probability.FiniteIrreducibleVaryingMarkedTransfer
import PerronWright.Probability.FiniteIrreducibleVaryingNumericalFactor
import PerronWright.Probability.FiniteIrreducibleVaryingDensity

/-! # Actual marked local factorial density with varying critical parameter -/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology Real
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleVaryingMarkedLocalMain

open FiniteIrreducibleMarkedLocalMain FiniteIrreducibleMarkedFactorialFormula
open FiniteIrreducibleNativeMarkConcentration FiniteIrreducibleCriticalPrefactorScaling
open FiniteIrreducibleNumericalFactorialAssembly FiniteIrreducibleFactorialDensityFloor
open FiniteIrreducibleResidualNormalization (normalizedResidual)
open FiniteIrreducibleDeterministicConnectedLawFormula (connectedProductLaw)
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)
open AnnealedMarkedResidualConcentration (componentMarks)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

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
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda)) (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → S, (∀ s, fiberCount x s = c n s) →
      ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      |scaledMarkedFactorialExpectation M (ell n) n x k r Ψ -
        FactorialDensity.density (M.alpha hM) (M.beta hM) (ell n)
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
  filter_upwards [FiniteIrreducibleVaryingNumericalFactor.eventually_uniform_numericalFactor_actual_time M hM q R ell lambda a b hl ha hb hδ,
    FiniteIrreducibleVaryingMarkedTransfer.eventually_uniform_weighted_joint_mark_test M hM R q hq ell lambda a b hl ha hb c D hD hround Ψ hΨ hη,
    eventually_ge_atTop (1 : ℕ),
    (FiniteIrreducibleVaryingCriticalTime.time_tendsto ell lambda hl).eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hnum hmark hn1 ht
  intro x hc k r hka hkb hr
  have hn : 0 < n := by omega
  obtain ⟨hk, pos, hw⟩ := hmark k r hka hkb hr
  have herr := hnum k r hka hkb hr
  have hd := FactorialDensity.density_pos (M.alpha hM) (ell n) (M.beta_pos hM)
    (fun i ↦ normalizedSize n (k i)) r (fun i ↦ ha.trans_le (hka i))
  have hdB := hbound q (M.alpha hM) (ell n) (fun i ↦ normalizedSize n (k i)) r
    (fun i ↦ ⟨hka i, hkb i⟩) hr
  have hnumB : |numericalFactor M hM n k r (CriticalScaling.time (ell n) n)| ≤ B + 1 := by
    have hh := abs_add_le
      (numericalFactor M hM n k r (CriticalScaling.time (ell n) n) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) (ell n) (fun i ↦ normalizedSize n (k i)) r)
      (FactorialDensity.density (M.alpha hM) (M.beta hM) (ell n) (fun i ↦ normalizedSize n (k i)) r)
    rw [sub_add_cancel, abs_of_pos hd] at hh
    exact hh.trans (by have := herr.trans_le (min_le_left (1 : ℝ) _); linarith)
  have he1 : |numericalFactor M hM n k r (CriticalScaling.time (ell n) n)| *
      |(∫ p, normalizedResidual M hM (ell n) n (c n) p * Ψ (componentMarks hk p)
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time (ell n) n)) k r pos) - v| ≤ ε / 2 := by
    calc
      _ ≤ (B + 1) * η := mul_le_mul hnumB hw (abs_nonneg _) (by linarith)
      _ = ε / 2 := by dsimp only [η]; field_simp
  have he2 : |numericalFactor M hM n k r (CriticalScaling.time (ell n) n) -
      FactorialDensity.density (M.alpha hM) (M.beta hM) (ell n) (fun i ↦ normalizedSize n (k i)) r| * |v| < ε / 2 := by
    have hh := herr.trans_le (min_le_right (1 : ℝ) _)
    have hpos : 0 < ε / (2 * (|v| + 1)) := by positivity
    calc
      _ ≤ |numericalFactor M hM n k r (CriticalScaling.time (ell n) n) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) (ell n) (fun i ↦ normalizedSize n (k i)) r| * (|v| + 1) := by
        gcongr; linarith
      _ < (ε / (2 * (|v| + 1))) * (|v| + 1) :=
        mul_lt_mul_of_pos_right hh (by positivity)
      _ = ε / 2 := by field_simp
  rw [scaledMarkedFactorialExpectation_eq_numericalFactor_mul_integral M hM (ell n) hn ht x (c n) hc k r hk pos Ψ]
  exact (marked_product_error _ _ _ _).trans_lt (by linarith [he1, he2])



/-- The actual varying-parameter graph expectation converges uniformly to
the density at the limiting parameter, including coupled continuous marks. -/
theorem eventually_uniform_marked_factorial_density_limit_parameter
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (hq : 0 < q)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda))
    (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → S, (∀ s, fiberCount x s = c n s) →
      ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      |scaledMarkedFactorialExpectation M (ell n) n x k r Ψ -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (k i)) r * Ψ (perronMarks M hM q)| < ε := by
  let v := Ψ (perronMarks M hM q)
  let δ := ε / (2 * (|v| + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  filter_upwards [eventually_uniform_marked_factorial_density M hM q R hq ell lambda a b hl ha hb
    c D hD hround Ψ hΨ (show 0 < ε / 2 by positivity),
    FiniteIrreducibleVaryingDensity.eventually_uniform_parameter_density
      (M.alpha hM) (M.beta hM) ell lambda hl q R a b ha hδ]
    with n hactual hd
  intro x hc k r hka hkb hr
  have he1 := hactual x hc k r hka hkb hr
  have he2 := hd (fun i ↦ normalizedSize n (k i)) r hka hkb hr
  have he2' : |FactorialDensity.density (M.alpha hM) (M.beta hM) (ell n)
      (fun i ↦ normalizedSize n (k i)) r * v -
      FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
      (fun i ↦ normalizedSize n (k i)) r * v| < ε / 2 := by
    rw [← sub_mul, abs_mul]
    calc
      _ ≤ |FactorialDensity.density (M.alpha hM) (M.beta hM) (ell n)
          (fun i ↦ normalizedSize n (k i)) r -
          FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (k i)) r| * (|v| + 1) := by gcongr; linarith
      _ < δ * (|v| + 1) := mul_lt_mul_of_pos_right he2 (by positivity)
      _ = ε / 2 := by dsimp only [δ]; field_simp
  exact (abs_sub_le _ _ _).trans_lt (by linarith [he1, he2'])

/-- Literal floor-size marked local-main, uniform on the paper size window. -/
theorem eventually_uniform_floor_marked_factorial_density
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (hq : 0 < q)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda)) (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → S, (∀ s, fiberCount x s = c n s) →
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |scaledMarkedFactorialExpectation M (ell n) n x (fun i ↦ CriticalScaling.size (y i) n) r Ψ -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r * Ψ (perronMarks M hM q)| < ε := by
  let v := Ψ (perronMarks M hM q)
  let δ := ε / (2 * (|v| + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  filter_upwards [eventually_uniform_marked_factorial_density_limit_parameter M hM q R hq ell lambda (a / 2) b hl
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
  have hh := abs_sub_le (scaledMarkedFactorialExpectation M (ell n) n x (fun i ↦ CriticalScaling.size (y i) n) r Ψ)
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

end PerronWright.FiniteIrreducibleVaryingMarkedLocalMain
