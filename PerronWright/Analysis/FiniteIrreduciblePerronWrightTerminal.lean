import PerronWright.Analysis.FiniteIrreducibleBoundedSurplusPerronWrightFormula
import PerronWright.Analysis.FiniteIrreduciblePhysicalScalarRadius

/-!
# Full finite irreducible Perron--Wright enumerative terminal

This combines the actual labelled connected tree, unicyclic and total
positive-surplus graph weights, for every fixed finite surplus cutoff.
The literal symmetric nonnegative irreducible mean matrix and its true
spectral criticality suffice; bipartite kernels remain allowed.

This is an enumerative theorem. It does not assert a component process law
or any realization of the Brownian/Aldous limiting process.
-/

open Filter Topology Asymptotics
open scoped Classical Topology Real

noncomputable section

namespace PerronWright.FiniteIrreduciblePerronWrightTerminal

namespace Radius
export PerronWright.FiniteIrreducibleCriticalWindowRadiusConversion
  (realScalarRadius criticalQuadraticRate)
export PerronWright.FiniteIrreduciblePhysicalScalarRadius
  (realScalarRadius_one realScalarRadius_analytic
   exists_physical_scalar_radius_and_cubic_bound)
end Radius

namespace Main
export PerronWright.FiniteIrreduciblePerronWrightFormulaMainTerm
  (wrightConstant wrightConstant_pos wrightConstant_eq_classical
   perronWrightRadiusMainTerm)
export PerronWright.FiniteIrreducibleBoundedSurplusPerronWrightFormula
  (perronWrightGaussianMainTerm
   exists_boundedSurplusPerronWright_radius_relative_bound_uniform_eta
   exists_boundedSurplusPerronWright_gaussian_relative_bound)
end Main

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
/-- Every unified Gaussian main term is genuinely positive at positive size. -/
theorem perronWrightGaussianMainTerm_pos
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {k : ℕ} (hk : 0 < k) (r : ℕ) (t : ℝ) :
    0 < Main.perronWrightGaussianMainTerm M hM k r t := by
  unfold Main.perronWrightGaussianMainTerm
  have hw := Main.wrightConstant_pos r
  have hb := M.beta_pos hM
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-- The actual connected weight is eventually positive simultaneously for
all bounded surpluses in a fixed physical critical window. -/
theorem connectedWeight_pos_eventually_bounded_surplus
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (R : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∀ᶠ k : ℕ in atTop, ∀ r : ℕ, r ≤ R → ∀ t : ℝ,
      Real.sqrt (k : ℝ) * |t - 1| ≤ L →
      0 < M.bjrModel.connectedWeight t k r := by
  obtain ⟨K, _hK, hbound⟩ :=
    Main.exists_boundedSurplusPerronWright_gaussian_relative_bound M hM R L hL
  have hs : Tendsto (fun k : ℕ ↦ (Real.sqrt (k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun k : ℕ ↦ K / Real.sqrt (k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hs
  have hsmall : ∀ᶠ k : ℕ in atTop, K / Real.sqrt (k : ℝ) < 1 :=
    hlim.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hbound, hsmall, eventually_ge_atTop (1 : ℕ)]
    with k hk hks hkone
  intro r hr t ht
  have h := (hk r hr t ht).trans_lt hks
  have hratio : 0 < M.bjrModel.connectedWeight t k r /
      Main.perronWrightGaussianMainTerm M hM k r t := by
    have hlow := neg_abs_le
      (M.bjrModel.connectedWeight t k r /
        Main.perronWrightGaussianMainTerm M hM k r t - 1)
    linarith
  have hp := perronWrightGaussianMainTerm_pos M hM
    (Nat.zero_lt_one.trans_le hkone) r t
  have hmul := mul_pos hratio hp
  simpa only [div_mul_cancel₀ _ hp.ne'] using hmul

/-- Along any bounded-surplus physical critical-window sequence the ratio
of the actual connected weight to the literal unified Gaussian main term
tends to one. Both surplus and scalar intensity may vary with size. -/
theorem tendsto_connectedWeight_div_perronWrightGaussianMainTerm
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (R : ℕ) (L : ℝ) (hL : 0 ≤ L) (r : ℕ → ℕ) (t : ℕ → ℝ)
    (hr : ∀ᶠ k : ℕ in atTop, r k ≤ R)
    (ht : ∀ᶠ k : ℕ in atTop, Real.sqrt (k : ℝ) * |t k - 1| ≤ L) :
    Tendsto (fun k : ℕ ↦ M.bjrModel.connectedWeight (t k) k (r k) /
      Main.perronWrightGaussianMainTerm M hM k (r k) (t k)) atTop (𝓝 1) := by
  obtain ⟨K, _hK, hbound⟩ :=
    Main.exists_boundedSurplusPerronWright_gaussian_relative_bound M hM R L hL
  have herror : (fun k : ℕ ↦ M.bjrModel.connectedWeight (t k) k (r k) /
      Main.perronWrightGaussianMainTerm M hM k (r k) (t k) - 1) =O[atTop]
      (fun k : ℕ ↦ (Real.sqrt (k : ℝ))⁻¹) := by
    apply IsBigO.of_bound K
    filter_upwards [hbound, hr, ht] with k hk hkr hkt
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
      div_eq_mul_inv] using hk (r k) hkr (t k) hkt
  have hscale : Tendsto (fun k : ℕ ↦ (Real.sqrt (k : ℝ))⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  simpa only [zero_add, sub_add_cancel] using
    (herror.trans_tendsto hscale).add_const 1

/-- The complete finite-type enumerative Perron--Wright theorem in one
statement: a real analytic genuine rooted-tree radius, its normalized
quadratic response and cubic error, the common shrinking-window formula
for every finite surplus cutoff, and its uniform critical Gaussian form.
The radius error constants are chosen before the window sequence. -/
theorem finite_perronWright
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    AnalyticAt ℝ (Radius.realScalarRadius M hM) 1 ∧
    Radius.realScalarRadius M hM 1 = 1 ∧
    (∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ t : ℝ, |t - 1| < δ →
      0 < t ∧ 0 < Radius.realScalarRadius M hM t ∧
      (M.fieldFMS (FiniteIrreducibleScalarFieldResponse.scalarField M (t : ℂ))).radius =
        ENNReal.ofReal (Radius.realScalarRadius M hM t) ∧
      |Real.log (Radius.realScalarRadius M hM t) -
        M.alpha hM ^ 2 / (2 * M.beta hM) * (t - 1) ^ 2| ≤ C * |t - 1| ^ 3) ∧
    (∀ R : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (𝓝 0) →
      ∀ᶠ k : ℕ in atTop, ∀ r : ℕ, r ≤ R → ∀ t : ℝ, |t - 1| ≤ eta k →
        |M.bjrModel.connectedWeight t k r /
          Main.perronWrightRadiusMainTerm M hM k r t - 1| ≤
            K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ)))) ∧
    (∀ R : ℕ, ∀ L : ℝ, 0 ≤ L →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop, ∀ r : ℕ, r ≤ R → ∀ t : ℝ,
        Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        |M.bjrModel.connectedWeight t k r /
          Main.perronWrightGaussianMainTerm M hM k r t - 1| ≤
            K / Real.sqrt (k : ℝ)) := by
  refine ⟨Radius.realScalarRadius_analytic M hM,
    Radius.realScalarRadius_one M hM, ?_,
    Main.exists_boundedSurplusPerronWright_radius_relative_bound_uniform_eta M hM,
    Main.exists_boundedSurplusPerronWright_gaussian_relative_bound M hM⟩
  simpa only [Radius.criticalQuadraticRate] using
    Radius.exists_physical_scalar_radius_and_cubic_bound M hM

end PerronWright.FiniteIrreduciblePerronWrightTerminal
