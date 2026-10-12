import PerronWright.Probability.FiniteIrreducibleLocalMainIdentity
import PerronWright.Probability.FiniteIrreducibleRawResidualUniform

/-! # Uniform deterministic finite factorial expectation density

This is the actual fixed-assignment graph probability theorem. Literal
finite counts satisfy an eventual bounded O(1) error from n μ. The true
normalized residual averaging and genuine finite Perron--Wright numeric
assembly are combined; neither is assumed as a theorem interface. The
matrix can be bipartite, and no B2 or primitive hypothesis is present.
-/

open MeasureTheory Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleLocalMainUniform

open FiniteIrreducibleLocalMainIdentity
open FiniteIrreducibleCriticalPrefactorScaling
open FiniteIrreducibleNumericalFactorialAssembly
open FiniteIrreducibleFactorialDensityFloor
open FiniteIrreducibleRawResidualUniform
open FiniteIrreducibleRawResidualTerminal (integral_normalizedResidual)
open FiniteIrreducibleResidualNormalization (normalizedResidual)
open FiniteIrreducibleDeterministicConnectedLawFormula (connectedProductLaw)
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

private theorem product_error (A u d : ℝ) :
    |A*u-d| ≤ |A| * |u-1| + |A-d| := by
  have he : A*u-d = A*(u-1)+(A-d) := by ring
  rw [he]
  exact (abs_add_le _ _).trans_eq (by rw [abs_mul])

/-- Full integer-window local main theorem for every actual deterministic
assignment realizing arbitrary O(1)-rounded counts. The threshold is
simultaneous in assignments, sizes and all bounded surplus vectors. -/
theorem eventually_uniform_factorial_expectation_density
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ)*M.weight s| ≤ D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → S, (∀ s, fiberCount x s = c n s) →
      ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      |scaledFactorialExpectation M lambda n x k r -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (k i)) r| < ε := by
  obtain ⟨C, hC, hbound⟩ := FactorialDensity.exists_density_window_bound
    (b := b) (M.beta_pos hM) ha R
  let B := C^q * Real.exp (-M.beta hM * (a*q)^3/24)
  have hB : 0 < B := mul_pos (pow_pos hC _) (Real.exp_pos _)
  let δ : ℝ := min 1 (ε/2)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  let η : ℝ := ε/(2*(B+1))
  have hη : 0 < η := div_pos hε (by positivity)
  filter_upwards [eventually_uniform_numericalFactor_actual_time M hM q R lambda a b ha hb hδ,
    eventually_uniform_native_rawResidual_limits M hM R q hq lambda a b ha hb c D hD hround hη,
    eventually_all_sizes_ge a ha 1, eventually_ge_atTop (1 : ℕ),
    (CriticalScaling.time_tendsto lambda).eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hnum hres hsize hn1 ht x hc k r hka hkb hr
  have hn : 0 < n := by omega
  have hk : ∀ i, 0 < k i := fun i ↦ by have := hsize (k i) (hka i); omega
  obtain ⟨pos, _, hmean⟩ := hres k r hka hkb hr
  rw [← integral_normalizedResidual M hM lambda n (c n) k r pos] at hmean
  have hd := FactorialDensity.density_pos (M.alpha hM) lambda (M.beta_pos hM)
    (fun i ↦ normalizedSize n (k i)) r (fun i ↦ ha.trans_le (hka i))
  have hdB := hbound q (M.alpha hM) lambda (fun i ↦ normalizedSize n (k i)) r
    (fun i ↦ ⟨hka i, hkb i⟩) hr
  have herr := hnum k r hka hkb hr
  have hnumB : |numericalFactor M hM n k r (CriticalScaling.time lambda n)| ≤ B+1 := by
    have h := abs_add_le
      (numericalFactor M hM n k r (CriticalScaling.time lambda n) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (k i)) r)
      (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (k i)) r)
    rw [sub_add_cancel, abs_of_pos hd] at h
    exact h.trans (by have hh := herr.trans_le (min_le_left (1 : ℝ) (ε/2)); linarith)
  have hm : |numericalFactor M hM n k r (CriticalScaling.time lambda n)| *
      |(∫ p, normalizedResidual M hM lambda n (c n) p
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos)-1| ≤ ε/2 := by
    calc
      _ ≤ (B+1)*η := mul_le_mul hnumB hmean (abs_nonneg _) (by linarith)
      _ = ε/2 := by dsimp only [η]; field_simp
  rw [scaledFactorialExpectation_eq_numericalFactor_mul_integral M hM lambda hn ht x (c n) hc k r hk pos]
  exact (product_error _ _ _).trans_lt (by
    have hh := herr.trans_le (min_le_right (1 : ℝ) (ε/2))
    linarith)

/-- Paper local-main at literal floor sizes, uniformly over the whole real
size window and every bounded surplus vector, under the actual fixed-type
independent-edge graph law with p_edge = 1-exp(-t κ/n). -/
theorem eventually_uniform_floor_factorial_expectation_density
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ)*M.weight s| ≤ D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → S, (∀ s, fiberCount x s = c n s) →
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |scaledFactorialExpectation M lambda n x (fun i ↦ CriticalScaling.size (y i) n) r -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| < ε := by
  filter_upwards [eventually_uniform_factorial_expectation_density M hM q R hq lambda (a/2) b
      (by linarith) hb c D hD hround (show 0 < ε/2 by linarith),
    eventually_uniform_floor_density (M.alpha hM) (M.beta hM) lambda q R a b ha
      (show 0 < ε/2 by linarith),
    eventually_floor_normalized_box q a b ha] with n hn hd hbox x hc y r hya hyb hr
  have hw := hbox y hya hyb
  have he1 := hn x hc (fun i ↦ CriticalScaling.size (y i) n) r hw.1 hw.2 hr
  have he2 := hd y r hya hyb hr
  calc
    _ ≤ |scaledFactorialExpectation M lambda n x (fun i ↦ CriticalScaling.size (y i) n) r -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (CriticalScaling.size (y i) n)) r| +
        |FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (CriticalScaling.size (y i) n)) r -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| := abs_sub_le _ _ _
    _ < ε/2+ε/2 := add_lt_add he1 he2
    _ = ε := by ring

end PerronWright.FiniteIrreducibleLocalMainUniform
