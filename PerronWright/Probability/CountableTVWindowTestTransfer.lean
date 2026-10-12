import PerronWright.Probability.FinitePointMeasureConstantMarkNeighborhood
import PerronWright.Probability.CountableTVWindowTerminal
import PerronWright.Probability.GraphWindowFactorialLimits
import PerronWright.Probability.BoundedConcentrationTransfer

/-! # Actual countable marked-window bounded-test transfer

The deterministic near-constant-mark estimate uses compact positions,
not compact marks. The stochastic estimate splits at an actual component
number cutoff and an actual weak-Borel bad-mark event. The hypotheses in
these transfer lemmas are discharged by the actual realization terminal
in the subsequent model-only construction.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Real Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableTVWindowTestTransfer

open CountableVariationMarks CountableComponentWindowLaw CountableTVWindowProfile
open ComponentWindowPointMeasures EmpiricalTypeMarks
open FinitePointMeasureCompact FinitePointMeasureFintype FinitePointMeasureMarking
open FinitePointMeasureConstantMarkNeighborhood BoundedConcentrationTransfer
open GraphWindowSource GraphWindowFactorialLimits

def testDifference (M : CountableKernel) (level : ℕ → ℕ)
    (a b : ℝ) (R n : ℕ) (p : VariationMark)
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) (G : SimpleGraph (Fin (n + 1))) : ℝ :=
  F (markedWindowPointMeasure
    (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) G a b R) -
    F (constantMark p (windowPointMeasure a b R 1 G))

theorem testDifference_bound (M : CountableKernel) (level : ℕ → ℕ)
    (a b : ℝ) (R n : ℕ) (p : VariationMark)
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) (G : SimpleGraph (Fin (n + 1))) :
    |testDifference M level a b R n p F G| ≤ 2 * ‖F‖ := by
  have ha := norm_coe_le_norm F (markedWindowPointMeasure
    (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) G a b R)
  have hb := norm_coe_le_norm F (constantMark p (windowPointMeasure a b R 1 G))
  simp only [Real.norm_eq_abs] at ha hb
  exact (abs_sub _ _).trans (by linarith)

theorem sample_mass_probability_le (M : CountableKernel) (level : ℕ → ℕ)
    (lambda a b : ℝ) (R n : ℕ) {lower : ℝ} (hlower : 0 < lower)
    (hlo : ∀ s t, lower ≤ M.kernel s t) (H : ℝ) (hH : 0 < H) :
    (M.empiricalNormalizedGraphLaw level lambda hlower hlo n).real
      {G | H < (Fintype.card (WindowComponent a b R 1 G) : ℝ)} ≤
    (∫ η, (mass η : ℝ) ∂(windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
      a b R n : Measure (PointMeasure (SurplusWindow a b R)))) / H := by
  let μ := M.empiricalNormalizedGraphLaw level lambda hlower hlo n
  let D : SimpleGraph (Fin (n + 1)) → ℝ := fun G ↦ (Fintype.card (WindowComponent a b R 1 G) : ℝ)
  have hI : Integrable D μ := Integrable.of_finite
  have hp (G) : 0 ≤ D G := Nat.cast_nonneg _
  have hh : μ {G | H < D G} ≤ ENNReal.ofReal (∫ G, D G / H ∂μ) :=
    (hI.div_const H).measure_le_integral
      (Eventually.of_forall (fun G ↦ div_nonneg (hp G) hH.le))
      (fun _ h ↦ (le_div_iff₀ hH).mpr (by simpa only [one_mul] using h.le))
  calc
    _ ≤ (ENNReal.ofReal (∫ G, D G / H ∂μ)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    _ = (∫ G, D G ∂μ) / H := by
      rw [integral_div, ENNReal.toReal_ofReal (div_nonneg (integral_nonneg hp) hH.le)]
    _ = _ := by
      rw [windowLaw_integral (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R n
        (f := fun η ↦ (mass η : ℝ))
        (NNReal.continuous_coe.measurable.comp measurable_mass)]
      simp only [windowPointMeasure_mass, NNReal.coe_natCast]
      rfl

theorem testDifference_probability_tendsto_zero
    (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (hlocal : HasUniformLocalLimit (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
      (M.alpha hM) (M.beta hM) lambda)
    (p : VariationMark)
    (hTV : ∀ δ > 0, Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n p δ)
      atTop (𝓝 0))
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (M.empiricalNormalizedGraphLaw level lambda hlower hlo n).real
      {G | ε ≤ |testDifference M level a b R n p F G|}) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := exists_window_mass_bound
    (M.empiricalNormalizedGraphLaw level lambda hlower hlo) (M.beta_pos hM) hlocal ha hab R
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ ↦ hc.trans_le measureReal_nonneg)
  · intro γ hγ
    obtain ⟨H, hH⟩ := exists_nat_gt (max 1 (2 * B / γ))
    have hHp : 0 < (H : ℝ) := zero_lt_one.trans ((le_max_left _ _).trans_lt hH)
    have hcut : B / (H : ℝ) < γ / 2 := by
      have hh : 2 * B < (H : ℝ) * γ := (div_lt_iff₀ hγ).mp ((le_max_right _ _).trans_lt hH)
      apply (div_lt_iff₀ hHp).mpr
      nlinarith
    obtain ⟨δ, hδ, hclose⟩ := exists_uniform_mark_radius
      (E := SurplusWindow a b R) (A := VariationMark) p H F (ε / 2) (by positivity)
    have hbad := hTV δ hδ
    simp_rw [CountableKernel.growingWindowBadProbability,
      M.empiricalMarkedWindowLaw_badProbability_eq] at hbad
    filter_upwards [hbad.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < γ / 2))] with n hn
    let x := CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)
    let μ := M.empiricalNormalizedGraphLaw level lambda hlower hlo n
    let A : Set (SimpleGraph (Fin (n + 1))) :=
      {G | (H : ℝ) < (Fintype.card (WindowComponent a b R 1 G) : ℝ)}
    have hsub : {G : SimpleGraph (Fin (n + 1)) | ε ≤ |testDifference M level a b R n p F G|} ⊆
        A ∪ badTVEvent x a b R p δ := by
      intro G hG
      by_cases hA : G ∈ A
      · exact Or.inl hA
      · right
        by_contra hv
        have hcard : Fintype.card (WindowComponent a b R 1 G) ≤ H := by
          have hh : ¬ (H : ℝ) < (Fintype.card (WindowComponent a b R 1 G) : ℝ) := hA
          exact_mod_cast le_of_not_gt hh
        have hy (C : WindowComponent a b R 1 G) : dist (ofProbability (componentMark x C.val)) p < δ := by
          by_contra hC
          exact hv ⟨C, le_of_not_gt hC⟩
        have hh := ofFintype_mark_close p H F (ε / 2) δ hclose hcard
          (windowAtom a b R 1) (fun C ↦ ofProbability (componentMark x C.val)) hy
        have hl : |testDifference M level a b R n p F G| < ε / 2 := hh
        exact (not_lt_of_ge hG) (hl.trans (by linarith))
    have hs : μ.real {G | ε ≤ |testDifference M level a b R n p F G|} ≤
        B / (H : ℝ) + μ.real (badTVEvent x a b R p δ) := by
      apply ((measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)).trans
      apply add_le_add _ le_rfl
      exact (sample_mass_probability_le M level lambda a b R n hlower hlo H hHp).trans
        (div_le_div_of_nonneg_right (hbound n) hHp.le)
    exact hs.trans_lt (by change B / (H : ℝ) + _ < γ; linarith)

theorem testDifference_l1_tendsto_zero
    (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (hlocal : HasUniformLocalLimit (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
      (M.alpha hM) (M.beta hM) lambda)
    (p : VariationMark)
    (hTV : ∀ δ > 0, Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n p δ)
      atTop (𝓝 0))
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ G, |testDifference M level a b R n p F G|
      ∂M.empiricalNormalizedGraphLaw level lambda hlower hlo n) atTop (𝓝 0) :=
  integral_abs_tendsto_zero (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
    (fun n ↦ testDifference M level a b R n p F) (fun _ ↦ measurable_of_countable _)
    (2 * ‖F‖) (by positivity) (fun n G ↦ testDifference_bound M level a b R n p F G)
    (fun ε hε ↦ testDifference_probability_tendsto_zero M hM level lambda a b ha hab R
      hlower hlo hlocal p hTV F ε hε)

end PerronWright.CountableTVWindowTestTransfer
