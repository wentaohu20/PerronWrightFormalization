import PerronWright.Probability.CountableFixedSupportApproximation
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform approximation of the literal reference densities

Joint continuity in the Perron scales, scalar parameter and positive
size coordinates is proved for the explicit density formula. Compact
boxes and the finite bounded-surplus family give actual reference
approximation uniformly on all coordinates used by the slow diagonal.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableFixedSupportDensityUniform

theorem density_continuousAt_positive_scales {q : ℕ} (r : Fin q → ℕ)
    {z : (ℝ × ℝ) × (ℝ × (Fin q → ℝ))} (hβ : 0 < z.1.2) (hx : ∀ i, 0 < z.2.2 i) :
    ContinuousAt (fun w : (ℝ × ℝ) × (ℝ × (Fin q → ℝ)) ↦
      FactorialDensity.density w.1.1 w.1.2 w.2.1 w.2.2 r) z := by
  unfold FactorialDensity.density
  apply ContinuousAt.mul
  · apply Real.continuous_exp.continuousAt.comp
    unfold FactorialDensity.criticalExponent
    fun_prop (disch := positivity)
  · apply tendsto_finsetProd
    intro i _
    change ContinuousAt (fun w : (ℝ × ℝ) × (ℝ × (Fin q → ℝ)) ↦
      FactorialDensity.sizeFactor w.1.2 (w.2.2 i) (r i)) z
    unfold FactorialDensity.sizeFactor
    fun_prop (disch := first | exact Or.inl hβ.ne' | exact Or.inl (hx i).ne' | positivity)

theorem density_continuousOn_scale_box {q : ℕ} (r : Fin q → ℕ)
    (A B L a b : ℝ) (hB : 0 < B) (ha : 0 < a) :
    ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × (Fin q → ℝ)) ↦
      FactorialDensity.density z.1.1 z.1.2 z.2.1 z.2.2 r)
      ((Set.Icc (A - 1) (A + 1) ×ˢ Set.Icc (B / 2) (2 * B + 1)) ×ˢ
        (Set.Icc (-L) L ×ˢ Set.Icc (fun _ ↦ a) (fun _ ↦ b))) := by
  intro z hz
  exact (density_continuousAt_positive_scales r
    ((div_pos hB (by norm_num)).trans_le hz.1.2.1)
    (fun i ↦ ha.trans_le (hz.2.2.1 i))).continuousWithinAt

end PerronWright.CountableFixedSupportDensityUniform

namespace PerronWright.CountableKernel

theorem fixedSupport_eventually_uniform_reference_density_fixed_surplus
    (M : CountableKernel) (hM : M.IsRegularCritical) {q : ℕ} (r : Fin q → ℕ)
    (a b L : ℝ) (ha : 0 < a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      ∀ y : Fin q → ℝ, (∀ i, a ≤ y i) → (∀ i, y i ≤ b) →
      |FactorialDensity.density
          ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
          ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
          lambda y r - FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| < ε := by
  let A := M.alpha hM
  let B := M.beta hM
  have hB : 0 < B := M.beta_pos hM
  have hc := CountableFixedSupportDensityUniform.density_continuousOn_scale_box
    r A B L a b hB ha
  have hk : IsCompact
      ((Set.Icc (A - 1) (A + 1) ×ˢ Set.Icc (B / 2) (2 * B + 1)) ×ˢ
        (Set.Icc (-L) L ×ˢ Set.Icc (fun _ : Fin q ↦ a) (fun _ ↦ b))) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hk.uniformContinuousOn_of_continuous hc) ε hε
  have hα := M.fixedSupportModel_alpha_tendsto hM hlower hlo
  have hβ := M.fixedSupportModel_beta_tendsto hM hlower hlo
  have hαmem := hα.eventually (Icc_mem_nhds (a := A - 1) (b := A + 1)
    (by dsimp [A]; linarith) (by dsimp [A]; linarith))
  have hβmem := hβ.eventually (Icc_mem_nhds (a := B / 2) (b := 2 * B + 1)
    (by dsimp [B] at *; linarith) (by dsimp [B] at *; linarith))
  have hdist := (hα.prodMk_nhds hβ).eventually (Metric.ball_mem_nhds (A, B) hδ)
  filter_upwards [hαmem, hβmem, hdist] with m ham hbm hdm lambda hl y hya hyb
  rw [← Real.dist_eq]
  exact hclose
    (((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo),
      (M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo)), (lambda, y))
    ⟨⟨ham, hbm⟩, ⟨abs_le.mp hl, hya, hyb⟩⟩
    ((A, B), (lambda, y))
    ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ⟨abs_le.mp hl, hya, hyb⟩⟩
    (by simpa only [dist_prod_same_right] using hdm)

/-- One support threshold controls every bounded surplus vector and
the full compact scalar/positive-size box. -/
theorem fixedSupport_eventually_uniform_reference_density
    (M : CountableKernel) (hM : M.IsRegularCritical) (q R : ℕ)
    (a b L : ℝ) (ha : 0 < a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |FactorialDensity.density
          ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
          ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
          lambda y r - FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| < ε := by
  have hfamily : ∀ rr : Fin q → Fin (R + 1), ∀ᶠ m in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      ∀ y : Fin q → ℝ, (∀ i, a ≤ y i) → (∀ i, y i ≤ b) →
      |FactorialDensity.density
          ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
          ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
          lambda y (fun i ↦ (rr i : ℕ)) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y (fun i ↦ (rr i : ℕ))| < ε :=
    fun rr ↦ M.fixedSupport_eventually_uniform_reference_density_fixed_surplus
      hM (fun i ↦ (rr i : ℕ)) a b L ha hlower hlo hε
  filter_upwards [eventually_all.mpr hfamily] with m hm lambda hl y r hya hyb hr
  exact hm (fun i ↦ ⟨r i, Nat.lt_succ_of_le (hr i)⟩) lambda hl y hya hyb

end PerronWright.CountableKernel
