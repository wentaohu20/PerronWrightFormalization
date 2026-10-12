import PerronWright.Probability.CountableTVWindowConvergence

/-! # Full weak transfer for actual graph window marks

The source consists of literal finite graph probabilities and literal
natural-type assignments. The mark space has no compactness requirement.
An actual first-mass bound and actual bad-mark probability estimates give
bounded-test closeness to the constant-mark pushforward, and hence full
weak convergence whenever the actual unmarked window laws converge.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Real Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GraphWindowMarkTransfer

open CountableVariationMarks CountableComponentWindowLaw CountableTVWindowProfile
open ComponentWindowPointMeasures EmpiricalTypeMarks
open FinitePointMeasureCompact FinitePointMeasureFintype FinitePointMeasureMarking
open FinitePointMeasureConstantMarkNeighborhood BoundedConcentrationTransfer
open CountableTVWindowConvergence GraphWindowSource GraphWindowFactorialLimits

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]
variable (x : (n : ℕ) → Fin (n+1) → ℕ)

def markedWindowLaw (a b : ℝ) (R n : ℕ) :
    ProbabilityMeasure (PointMeasure (MarkedWindow a b R)) :=
  ⟨(ρ n).map (fun G ↦ markedWindowPointMeasure (x n) G a b R),
    Measure.isProbabilityMeasure_map (measurable_markedWindowPointMeasure _ a b R).aemeasurable⟩

theorem markedWindowLaw_integral (a b : ℝ) (R n : ℕ)
    {F : PointMeasure (MarkedWindow a b R) → ℝ} (hF : Measurable F) :
    (∫ η, F η ∂(markedWindowLaw ρ x a b R n : Measure _)) =
      ∫ G, F (markedWindowPointMeasure (x n) G a b R) ∂ρ n :=
  integral_map (measurable_markedWindowPointMeasure _ a b R).aemeasurable hF.aestronglyMeasurable

omit [∀ n, IsProbabilityMeasure (ρ n)] in
def testDifference (a b : ℝ) (R n : ℕ) (p : VariationMark)
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) (G : SimpleGraph (Fin (n+1))) : ℝ :=
  F (markedWindowPointMeasure (x n) G a b R) -
    F (constantMark p (windowPointMeasure a b R 1 G))

omit [∀ n, IsProbabilityMeasure (ρ n)] in
theorem testDifference_bound (a b : ℝ) (R n : ℕ) (p : VariationMark)
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) (G : SimpleGraph (Fin (n+1))) :
    |testDifference x a b R n p F G| ≤ 2 * ‖F‖ := by
  have ha := norm_coe_le_norm F (markedWindowPointMeasure (x n) G a b R)
  have hb := norm_coe_le_norm F (constantMark p (windowPointMeasure a b R 1 G))
  simp only [Real.norm_eq_abs] at ha hb
  exact (abs_sub _ _).trans (by linarith)

theorem sample_mass_probability_le (a b : ℝ) (R n : ℕ) (H : ℝ) (hH : 0 < H) :
    (ρ n).real {G | H < (Fintype.card (WindowComponent a b R 1 G) : ℝ)} ≤
      (∫ G, (Fintype.card (WindowComponent a b R 1 G) : ℝ) ∂ρ n) / H := by
  let D : SimpleGraph (Fin (n+1)) → ℝ := fun G ↦ (Fintype.card (WindowComponent a b R 1 G) : ℝ)
  have hI : Integrable D (ρ n) := Integrable.of_finite
  have hp (G) : 0 ≤ D G := Nat.cast_nonneg _
  have hh : (ρ n) {G | H < D G} ≤ ENNReal.ofReal (∫ G, D G / H ∂ρ n) :=
    (hI.div_const H).measure_le_integral
      (Eventually.of_forall (fun G ↦ div_nonneg (hp G) hH.le))
      (fun _ h ↦ (le_div_iff₀ hH).mpr (by simpa only [one_mul] using h.le))
  calc
    _ ≤ (ENNReal.ofReal (∫ G, D G / H ∂ρ n)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    _ = _ := by
      rw [integral_div, ENNReal.toReal_ofReal (div_nonneg (integral_nonneg hp) hH.le)]

theorem testDifference_probability_tendsto_zero (a b : ℝ) (R : ℕ)
    (B : ℝ) (_hB : 0 ≤ B)
    (hmass : ∀ n, (∫ G, (Fintype.card (WindowComponent a b R 1 G) : ℝ) ∂ρ n) ≤ B)
    (p : VariationMark)
    (hTV : ∀ δ > 0, Tendsto (fun n ↦ (ρ n).real (badTVEvent (x n) a b R p δ)) atTop (𝓝 0))
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (ρ n).real {G | ε ≤ |testDifference x a b R n p F G|}) atTop (𝓝 0) := by
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
    filter_upwards [(hTV δ hδ).eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < γ / 2))]
      with n hn
    let A : Set (SimpleGraph (Fin (n+1))) :=
      {G | (H : ℝ) < (Fintype.card (WindowComponent a b R 1 G) : ℝ)}
    have hsub : {G : SimpleGraph (Fin (n+1)) | ε ≤ |testDifference x a b R n p F G|} ⊆
        A ∪ badTVEvent (x n) a b R p δ := by
      intro G hG
      by_cases hA : G ∈ A
      · exact Or.inl hA
      · right
        by_contra hv
        have hcard : Fintype.card (WindowComponent a b R 1 G) ≤ H := by
          have hh : ¬ (H : ℝ) < (Fintype.card (WindowComponent a b R 1 G) : ℝ) := hA
          exact_mod_cast le_of_not_gt hh
        have hy (C : WindowComponent a b R 1 G) :
            dist (ofProbability (componentMark (x n) C.val)) p < δ := by
          by_contra hC
          exact hv ⟨C, le_of_not_gt hC⟩
        have hh := ofFintype_mark_close p H F (ε / 2) δ hclose hcard
          (windowAtom a b R 1) (fun C ↦ ofProbability (componentMark (x n) C.val)) hy
        have hl : |testDifference x a b R n p F G| < ε / 2 := hh
        exact (not_lt_of_ge hG) (hl.trans (by linarith))
    have hs : (ρ n).real {G | ε ≤ |testDifference x a b R n p F G|} ≤
        B / (H : ℝ) + (ρ n).real (badTVEvent (x n) a b R p δ) := by
      apply ((measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)).trans
      apply add_le_add _ le_rfl
      exact (sample_mass_probability_le ρ a b R n H hHp).trans
        (div_le_div_of_nonneg_right (hmass n) hHp.le)
    exact hs.trans_lt (by change B / (H : ℝ) + _ < γ; linarith)

theorem testDifference_l1_tendsto_zero (a b : ℝ) (R : ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hmass : ∀ n, (∫ G, (Fintype.card (WindowComponent a b R 1 G) : ℝ) ∂ρ n) ≤ B)
    (p : VariationMark)
    (hTV : ∀ δ > 0, Tendsto (fun n ↦ (ρ n).real (badTVEvent (x n) a b R p δ)) atTop (𝓝 0))
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ G, |testDifference x a b R n p F G| ∂ρ n) atTop (𝓝 0) :=
  integral_abs_tendsto_zero ρ (fun n ↦ testDifference x a b R n p F)
    (fun _ ↦ measurable_of_countable _) (2 * ‖F‖) (by positivity)
    (fun n G ↦ testDifference_bound x a b R n p F G)
    (fun ε hε ↦ testDifference_probability_tendsto_zero ρ x a b R B hB hmass p hTV F ε hε)

theorem canonicalMarkedWindowLaw_integral (a b : ℝ) (R n : ℕ) (p : VariationMark)
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) :
    (∫ η, F η ∂(canonicalMarkedWindowLaw p a b R (windowLaw ρ a b R n) : Measure _)) =
      ∫ G, F (constantMark p (windowPointMeasure a b R 1 G)) ∂ρ n := by
  unfold canonicalMarkedWindowLaw
  rw [ProbabilityMeasure.toMeasure_map, integral_map
    (continuous_mapPoint (fun z ↦ (z, p)) (continuous_id.prodMk continuous_const)).measurable.aemeasurable
      F.continuous.measurable.aestronglyMeasurable]
  exact windowLaw_integral ρ a b R n (f := fun η ↦ F (constantMark p η))
    ((F.continuous.comp (continuous_mapPoint _ (continuous_id.prodMk continuous_const))).measurable)

theorem means_difference_integral (a b : ℝ) (R n : ℕ) (p : VariationMark)
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) :
    (∫ η, F η ∂(markedWindowLaw ρ x a b R n : Measure _)) -
      (∫ η, F η ∂(canonicalMarkedWindowLaw p a b R (windowLaw ρ a b R n) : Measure _)) =
      ∫ G, testDifference x a b R n p F G ∂ρ n := by
  rw [markedWindowLaw_integral ρ x a b R n F.continuous.measurable,
    canonicalMarkedWindowLaw_integral ρ a b R n p F,
    ← integral_sub Integrable.of_finite Integrable.of_finite]
  rfl

theorem means_difference_tendsto_zero (a b : ℝ) (R : ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hmass : ∀ n, (∫ G, (Fintype.card (WindowComponent a b R 1 G) : ℝ) ∂ρ n) ≤ B)
    (p : VariationMark)
    (hTV : ∀ δ > 0, Tendsto (fun n ↦ (ρ n).real (badTVEvent (x n) a b R p δ)) atTop (𝓝 0))
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) :
    Tendsto (fun n ↦
      (∫ η, F η ∂(markedWindowLaw ρ x a b R n : Measure _)) -
        (∫ η, F η ∂(canonicalMarkedWindowLaw p a b R (windowLaw ρ a b R n) : Measure _)))
      atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _
    (testDifference_l1_tendsto_zero ρ x a b R B hB hmass p hTV F)
  exact Eventually.of_forall (fun n ↦ by
    rw [means_difference_integral ρ x a b R n p F]
    exact abs_integral_le_integral_abs)

theorem markedWindowLaw_tendsto (a b : ℝ) (R : ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hmass : ∀ n, (∫ G, (Fintype.card (WindowComponent a b R 1 G) : ℝ) ∂ρ n) ≤ B)
    (p : VariationMark)
    (hTV : ∀ δ > 0, Tendsto (fun n ↦ (ρ n).real (badTVEvent (x n) a b R p δ)) atTop (𝓝 0))
    (μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hsource : Tendsto (windowLaw ρ a b R) atTop (𝓝 μ)) :
    Tendsto (markedWindowLaw ρ x a b R) atTop (𝓝 (canonicalMarkedWindowLaw p a b R μ)) := by
  have hc := (continuous_canonicalMarkedWindowLaw p a b R).tendsto μ |>.comp hsource
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  have hCF := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hc F
  have hdiff := means_difference_tendsto_zero ρ x a b R B hB hmass p hTV F
  simpa only [Function.comp_apply, zero_add, sub_add_cancel] using hdiff.add hCF

theorem markedWindowLaw_tendsto_of_local_limit
    {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (p : VariationMark)
    (hTV : ∀ δ > 0, Tendsto (fun n ↦ (ρ n).real (badTVEvent (x n) a b R p δ)) atTop (𝓝 0))
    (μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hsource : Tendsto (windowLaw ρ a b R) atTop (𝓝 μ)) :
    Tendsto (markedWindowLaw ρ x a b R) atTop (𝓝 (canonicalMarkedWindowLaw p a b R μ)) := by
  obtain ⟨B, hB, hb⟩ := GraphWindowFactorialLimits.exists_window_mass_bound ρ hbeta hlocal ha hab R
  apply markedWindowLaw_tendsto ρ x a b R B hB _ p hTV μ hsource
  intro n
  have hh := hb n
  rw [windowLaw_integral ρ a b R n
    (f := fun η ↦ (mass η : ℝ))
    (NNReal.continuous_coe.measurable.comp measurable_mass)] at hh
  simpa only [windowPointMeasure_mass, NNReal.coe_natCast] using hh

end PerronWright.GraphWindowMarkTransfer
