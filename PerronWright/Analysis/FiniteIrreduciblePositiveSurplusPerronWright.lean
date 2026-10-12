import PerronWright.Analysis.FiniteIrreducibleConnectedPerronWrightFormula
import PerronWright.Analysis.FiniteIrreducibleCriticalConnectedWright

/-!
# Physical positive-surplus Perron--Wright theorem for finite irreducible types

The numerator is the original annealed simple connected-graph partition
function. The main term is the literal real Wright expression with the
Gaussian rate alpha^2/(2 beta). All analytic continuation, full EGF matching,
noncubic remainder, transfer and scalar-radius response have been proved
from the finite model, without a primitive or B2 assumption.
-/

open Filter Topology
open scoped Classical Topology Real Nat

noncomputable section

namespace PerronWright.FiniteIrreduciblePositiveSurplusPerronWright

open GraphCore FiniteIrreducibleCriticalConnectedWright

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- The paper's complete real Gaussian main term at positive surplus. -/
def connectedGaussianMain
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell k : ℕ) (t : ℝ) : ℝ :=
  criticalConnectedMain M hM ell k *
    Real.exp (-(M.alpha hM ^ 2 / (2 * M.beta hM)) *
      (k : ℝ) * (t - 1) ^ 2)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem connectedGaussianMain_pos
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell k : ℕ} (hell : 0 < ell) (hk : 0 < k) (t : ℝ) :
    0 < connectedGaussianMain M hM ell k t :=
  mul_pos (criticalConnectedMain_pos M hM hell hk) (Real.exp_pos _)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
/-- The complex scalar transfer main term is exactly the cast of the
paper's real main term, including the explicit Gaussian rate. -/
theorem connectedGaussianMain_ofReal
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell k : ℕ} (hell : 0 < ell) (hk : 0 < k) (t : ℝ) :
    (connectedGaussianMain M hM ell k t : ℂ) =
      FiniteIrreducibleConnectedPerronWrightFormula.scalarConnectedGaussianMainTerm
        M hM ell k t := by
  unfold connectedGaussianMain
    FiniteIrreducibleConnectedPerronWrightFormula.scalarConnectedGaussianMainTerm
    FiniteIrreducibleConnectedPerronWrightFormula.Radius.criticalQuadraticRate
  rw [Complex.ofReal_mul, criticalConnectedMain_ofReal M hM hell hk]

private theorem eventually_criticalWindow_positive
    (L : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∀ t : ℝ,
      Real.sqrt (k : ℝ) * |t - 1| ≤ L → 0 < t := by
  have hsqrt : Tendsto (fun k : ℕ ↦ Real.sqrt (k : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ k : ℕ in atTop,
      L + 1 < Real.sqrt (k : ℝ) :=
    hsqrt.eventually_gt_atTop (L + 1)
  filter_upwards [hevent] with k hk
  intro t ht
  by_contra htpos
  have htle : t ≤ 0 := le_of_not_gt htpos
  have habs : 1 ≤ |t - 1| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hge : Real.sqrt (k : ℝ) ≤
      Real.sqrt (k : ℝ) * |t - 1| := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left habs
      (Real.sqrt_nonneg _)
  linarith

/-- The actual total connected-graph Perron--Wright formula, uniformly on
the physical critical window sqrt(k)|t-1| <= L, for each fixed positive
surplus. Bipartite finite type kernels are included. -/
theorem exists_connectedWeight_gaussian_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop, ∀ t : ℝ,
      Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        |M.bjrModel.connectedWeight t k (ell + 1) /
            connectedGaussianMain M hM ell k t - 1| ≤
          K / Real.sqrt (k : ℝ) := by
  obtain ⟨K, hK, hbound⟩ :=
    FiniteIrreducibleConnectedPerronWrightFormula.exists_scalarConnected_gaussian_relative_bound
      M hM hell L hL
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_criticalWindow_positive L,
    eventually_gt_atTop (0 : ℕ)] with k hk hkpos hkone
  intro t ht
  have h := hk t ht
  rw [FiniteIrreducibleConnectedPerronWrightFormula.scalarConnectedContribution_eq_connectedWeight
    M t (hkpos t ht) ell k,
    ← connectedGaussianMain_ofReal M hM hell hkone] at h
  have hnorm :
      ‖(M.bjrModel.connectedWeight t k (ell + 1) : ℂ) /
          (connectedGaussianMain M hM ell k t : ℂ) - 1‖ =
        |M.bjrModel.connectedWeight t k (ell + 1) /
          connectedGaussianMain M hM ell k t - 1| := by norm_cast
  rw [hnorm] at h
  exact h

/-- Along every sequence in a bounded physical critical window, the actual
connected weight divided by the explicit real main term tends to one. -/
theorem tendsto_connectedWeight_div_gaussianMain
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) (L : ℝ) (hL : 0 ≤ L)
    (t : ℕ → ℝ)
    (ht : ∀ᶠ k : ℕ in atTop,
      Real.sqrt (k : ℝ) * |t k - 1| ≤ L) :
    Tendsto (fun k : ℕ ↦
      M.bjrModel.connectedWeight (t k) k (ell + 1) /
        connectedGaussianMain M hM ell k (t k)) atTop (𝓝 1) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_connectedWeight_gaussian_relative_bound M hM hell L hL
  have herror : (fun k : ℕ ↦
      M.bjrModel.connectedWeight (t k) k (ell + 1) /
        connectedGaussianMain M hM ell k (t k) - 1) =O[atTop]
      (fun k : ℕ ↦ (Real.sqrt (k : ℝ))⁻¹) := by
    apply Asymptotics.IsBigO.of_bound K
    filter_upwards [hbound, ht] with k hk htk
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
      div_eq_mul_inv] using hk (t k) htk
  have hscale : Tendsto (fun k : ℕ ↦ (Real.sqrt (k : ℝ))⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  simpa only [zero_add, sub_add_cancel] using
    (herror.trans_tendsto hscale).add_const 1

/-- One common error constant and index work for all positive surpluses in
a fixed finite range, on the same physical critical window. -/
theorem exists_connectedWeight_gaussian_relative_bound_uniform_surplus
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (R : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ ell : ℕ, 0 < ell → ell ≤ R → ∀ t : ℝ,
        Real.sqrt (k : ℝ) * |t - 1| ≤ L →
          |M.bjrModel.connectedWeight t k (ell + 1) /
              connectedGaussianMain M hM ell k t - 1| ≤
            K / Real.sqrt (k : ℝ) := by
  classical
  have hex : ∀ i : Fin R, ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ, Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        |M.bjrModel.connectedWeight t k (i.val + 1 + 1) /
            connectedGaussianMain M hM (i.val + 1) k t - 1| ≤
          K / Real.sqrt (k : ℝ) := by
    intro i
    exact exists_connectedWeight_gaussian_relative_bound M hM
      (Nat.succ_pos i.val) L hL
  choose K hK hbound using hex
  have hall : ∀ᶠ k : ℕ in atTop, ∀ i : Fin R, ∀ t : ℝ,
      Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        |M.bjrModel.connectedWeight t k (i.val + 1 + 1) /
            connectedGaussianMain M hM (i.val + 1) k t - 1| ≤
          K i / Real.sqrt (k : ℝ) := Filter.eventually_all.mpr hbound
  let C : ℝ := 1 + ∑ i : Fin R, K i
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun i _ ↦ (hK i).le)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hall] with k hk
  intro ell hell hellR t ht
  let i : Fin R := ⟨ell - 1, by omega⟩
  have hi : i.val + 1 = ell := by dsimp only [i]; omega
  have hsum : K i ≤ ∑ j : Fin R, K j :=
    Finset.single_le_sum (fun j _ ↦ (hK j).le) (Finset.mem_univ i)
  have hiC : K i ≤ C := hsum.trans (by dsimp only [C]; linarith)
  have h := hk i t ht
  rw [hi] at h
  exact h.trans (div_le_div_of_nonneg_right hiC (Real.sqrt_nonneg _))

end PerronWright.FiniteIrreduciblePositiveSurplusPerronWright
