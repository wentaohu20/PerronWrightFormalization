import PerronWright.Probability.FiniteIrreducibleMarkedComponentProcess
import PerronWright.Probability.FiniteIrreducibleWindowMarkConcentration
import PerronWright.Probability.FiniteIrreducibleWindowCountLaw
import PerronWright.Probability.FinitePointMeasureMarkingContinuity
import PerronWright.Probability.BoundedConcentrationTransfer

/-! # Genuine deterministic window-law transfer to canonical Perron marking -/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000

namespace PerronWright.FiniteIrreducibleMarkedWindowTransfer

open FiniteIrreducibleMarkedComponentProcess FiniteIrreducibleComponentProcess
  FiniteIrreducibleWindowMarkConcentration FiniteIrreducibleWindowCountLaw
  ComponentWindowMarkedLaw ComponentWindowPointMeasures EmpiricalTypeMarks WeakProbabilityMarks
  FinitePointMeasureCompact FinitePointMeasureFintype FinitePointMeasureMarking
  FinitePointMeasureMarkingContinuity BoundedConcentrationTransfer
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def testDifference (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (a b : ℝ) (R n : ℕ) (x : Fin n → S)
    (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  F (markedWindowPointMeasure x G a b R) -
    F (constantMark (perronWeakMark M hM) (windowPointMeasure a b R 1 G))

omit [DiscreteTopology S] in
theorem testDifference_bound (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (a b : ℝ) (R n : ℕ) (x : Fin n → S)
    (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) (G : SimpleGraph (Fin n)) :
    |testDifference M hM a b R n x F G| ≤ 2*‖F‖ := by
  have ha := norm_coe_le_norm F (markedWindowPointMeasure x G a b R)
  have hb := norm_coe_le_norm F (constantMark (perronWeakMark M hM) (windowPointMeasure a b R 1 G))
  simp only [Real.norm_eq_abs] at ha hb
  exact (abs_sub _ _).trans (by linarith)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem sample_mass_probability_le (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S) (H : ℝ) (hH : 0 < H) :
    (graphLaw M lambda n x).real
      {G | H < (Fintype.card (WindowComponent a b R 1 G) : ℝ)} ≤
      (∫ η, (mass η : ℝ) ∂(FiniteIrreducibleComponentProcess.unmarkedWindowLaw
        M lambda a b R n x : Measure (PointMeasure (SurplusWindow a b R))))/H := by
  let μ := graphLaw M lambda n x
  let D : SimpleGraph (Fin n) → ℝ := fun G ↦ (Fintype.card (WindowComponent a b R 1 G) : ℝ)
  have hI : Integrable D μ := Integrable.of_finite
  have hp (G) : 0 ≤ D G := Nat.cast_nonneg _
  have hh : μ {G | H < D G} ≤ ENNReal.ofReal (∫ G, D G/H ∂μ) :=
    (hI.div_const H).measure_le_integral
      (Eventually.of_forall (fun G ↦ div_nonneg (hp G) hH.le))
      (fun _ h ↦ (le_div_iff₀ hH).mpr (by simpa only [one_mul] using h.le))
  calc
    _ ≤ (ENNReal.ofReal (∫ G, D G/H ∂μ)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    _ = (∫ G, D G ∂μ)/H := by
      rw [integral_div,ENNReal.toReal_ofReal (div_nonneg (integral_nonneg hp) hH.le)]
    _ = _ := by
      rw [FiniteIrreducibleComponentProcess.windowLaw_integral M lambda a b R n x
        (f := fun η ↦ (mass η : ℝ))
        (NNReal.continuous_coe.measurable.comp measurable_mass)]
      simp only [windowPointMeasure_mass,NNReal.coe_natCast]
      rfl

theorem testDifference_probability_tendsto_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (graphLaw M lambda n (x n)).real
      {G | ε ≤ |testDifference M hM a b R n (x n) F G|}) atTop (𝓝 0) := by
  obtain ⟨B,hB,hbound⟩ := exists_window_mass_bound M hM lambda a b ha hab R x D hD hround
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ ↦ hc.trans_le measureReal_nonneg)
  · intro γ hγ
    obtain ⟨H,hH⟩ := exists_nat_gt (max 1 (2*B/γ))
    have hHp : 0 < (H : ℝ) := zero_lt_one.trans ((le_max_left _ _).trans_lt hH)
    have hcut : B/(H : ℝ) < γ/2 := by
      have hh : 2*B < (H : ℝ)*γ := (div_lt_iff₀ hγ).mp ((le_max_right _ _).trans_lt hH)
      apply (div_lt_iff₀ hHp).mpr
      nlinarith
    obtain ⟨U,hU,hclose⟩ := exists_mark_neighborhood (perronWeakMark M hM) H F (ε/2) (by positivity)
    let V := ofProbability ⁻¹' U
    have hV : V ∈ 𝓝 (FiniteIrreducibleConnectedTypeLaw.perronLaw M hM) :=
      (continuous_ofProbability.tendsto _) hU
    have hbad := badWeakEvent_probability_tendsto_zero M hM lambda a b ha hab R x D hD hround V hV
    filter_upwards [hbad.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < γ/2))] with n hn
    let μ := graphLaw M lambda n (x n)
    let A : Set (SimpleGraph (Fin n)) :=
      {G | (H : ℝ) < (Fintype.card (WindowComponent a b R 1 G) : ℝ)}
    have hsub : {G : SimpleGraph (Fin n) | ε ≤ |testDifference M hM a b R n (x n) F G|} ⊆
        A ∪ badWeakEvent (x n) a b R V := by
      intro G hG
      by_cases hA : G ∈ A
      · exact Or.inl hA
      · right
        by_contra hv
        have hcard : Fintype.card (WindowComponent a b R 1 G) ≤ H := by
          have hAR : ¬ (H : ℝ) < (Fintype.card (WindowComponent a b R 1 G) : ℝ) := hA
          exact_mod_cast (le_of_not_gt hAR)
        have hy (C : WindowComponent a b R 1 G) : ofProbability (componentMark (x n) C.val) ∈ U := by
          by_contra hC
          exact hv ⟨C,hC⟩
        have hh := ofFintype_mark_close (perronWeakMark M hM) H F (ε/2) U hclose hcard
          (windowAtom a b R 1) (fun C ↦ ofProbability (componentMark (x n) C.val)) hy
        have hl : |testDifference M hM a b R n (x n) F G| < ε/2 := hh
        exact (not_lt_of_ge hG) (hl.trans (by linarith))
    have hs : μ.real {G | ε ≤ |testDifference M hM a b R n (x n) F G|} ≤
        B/(H : ℝ)+μ.real (badWeakEvent (x n) a b R V) := by
      apply ((measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)).trans
      apply add_le_add _ le_rfl
      exact (sample_mass_probability_le M lambda a b R n (x n) H hHp).trans
        (div_le_div_of_nonneg_right (hbound n) hHp.le)
    exact hs.trans_lt (by change B/(H : ℝ)+_ < γ; linarith)

theorem testDifference_l1_tendsto_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ G, |testDifference M hM a b R n (x n) F G|
      ∂graphLaw M lambda n (x n)) atTop (𝓝 0) :=
  integral_abs_tendsto_zero (fun n ↦ graphLaw M lambda n (x n))
    (fun n ↦ testDifference M hM a b R n (x n) F)
    (fun _ ↦ measurable_of_countable _) (2*‖F‖) (by positivity)
    (fun n G ↦ testDifference_bound M hM a b R n (x n) F G)
    (fun ε hε ↦ testDifference_probability_tendsto_zero M hM lambda a b ha hab R x D hD hround F ε hε)

end PerronWright.FiniteIrreducibleMarkedWindowTransfer
