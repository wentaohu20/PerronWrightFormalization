import PerronWright.Probability.ComponentWindowMarkedLaw
import PerronWright.Probability.FinitePointMeasureMarkingContinuity
import PerronWright.Probability.BoundedConcentrationTransfer

/-! # Actual window-law continuous tests transfer to constant Perron marks

Uniform atom-map continuity, the genuine graph window mass bound and
the proved actual bad weak-mark event control yield bounded-test L1
transfer. No point-process coupling or integrability interface is assumed.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Topology
open scoped PerronWright.ComponentWindowMarkedLaw

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.ComponentWindowMarkedTransfer

open WeakProbabilityMarks FinitePointMeasureCompact FinitePointMeasureFintype
  FinitePointMeasureMarking FinitePointMeasureMarkingContinuity ComponentWindowPointMeasures
  ComponentWindowMarkedLaw CompactWindowMarkConcentration EmpiricalTypeMarks
  EmpiricalMarkConcentration ComponentWindowTightness BoundedConcentrationTransfer ProfileSquareMoment

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

def perronWeakMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) : WeakMark S :=
  ofProbability (perronMark M hM)

def testDifference (M : CompactBJRModel S) (hM : M.IsRegularCritical) (a b : ℝ) (R n : ℕ)
    (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) (p : AnnealedTypedGraph.State S n) : ℝ :=
  F (markedWindowPointMeasure p.1 (AnnealedTypedGraph.graph p) a b R) -
    F (constantMark (perronWeakMark M hM) (windowPointMeasure a b R 1 (AnnealedTypedGraph.graph p)))

theorem testDifference_measurable (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (a b : ℝ) (R n : ℕ) (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) :
    Measurable (testDifference M hM a b R n F) :=
  (F.continuous.measurable.comp (measurable_markedWindowPointMeasure a b R n)).sub
    (F.continuous.measurable.comp ((continuous_constantMark (perronWeakMark M hM)).measurable.comp
      ((measurable_windowPointMeasure a b R 1 n).comp (AnnealedTypedGraph.measurable_graph n))))

theorem testDifference_bound (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (a b : ℝ) (R n : ℕ) (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ)
    (p : AnnealedTypedGraph.State S n) : |testDifference M hM a b R n F p| ≤ 2*‖F‖ := by
  have ha := norm_coe_le_norm F (markedWindowPointMeasure p.1 (AnnealedTypedGraph.graph p) a b R)
  have hb := norm_coe_le_norm F (constantMark (perronWeakMark M hM)
    (windowPointMeasure a b R 1 (AnnealedTypedGraph.graph p)))
  simp only [Real.norm_eq_abs] at ha hb
  exact (abs_sub _ _).trans (by linarith)

theorem typed_windowMass_integral_eq_unmarked (M : CompactBJRModel S)
    (lambda a b : ℝ) (R n : ℕ) :
    (∫ p : AnnealedTypedGraph.State S n,
      (Fintype.card (WindowComponent a b R 1 (AnnealedTypedGraph.graph p)) : ℝ)
        ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n) =
      ∫ η, (mass η : ℝ) ∂(unmarkedWindowLaw M lambda a b R n :
        Measure (PointMeasure (SurplusWindow a b R))) := by
  rw [AnnealedTypedGraph.graph_expectation M _ (CriticalScaling.time_nonneg lambda n) n
    (fun G ↦ (Fintype.card (WindowComponent a b R 1 G) : ℝ))]
  exact (windowLaw_mass_integral M lambda a b R 1 n).symm

theorem sample_mass_probability_le (M : CompactBJRModel S) (lambda a b : ℝ) (R n : ℕ)
    (H : ℝ) (hH : 0 < H) :
    (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n).real
        {p | H < (Fintype.card (WindowComponent a b R 1 (AnnealedTypedGraph.graph p)) : ℝ)} ≤
      (∫ η, (mass η : ℝ) ∂(unmarkedWindowLaw M lambda a b R n :
        Measure (PointMeasure (SurplusWindow a b R)))) / H := by
  let μ := AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n
  let D : AnnealedTypedGraph.State S n → ℝ := fun p ↦
    (Fintype.card (WindowComponent a b R 1 (AnnealedTypedGraph.graph p)) : ℝ)
  have hI : Integrable D μ := typed_windowMass_integrable M lambda a b R n
  have hpos (p) : 0 ≤ D p := Nat.cast_nonneg _
  have hh : μ {p | H < D p} ≤ ENNReal.ofReal (∫ p, D p/H ∂μ) :=
    (hI.div_const H).measure_le_integral
      (Eventually.of_forall (fun p ↦ div_nonneg (hpos p) hH.le))
      (fun _ hp ↦ (le_div_iff₀ hH).mpr (by simpa only [one_mul] using hp.le))
  calc
    _ ≤ (ENNReal.ofReal (∫ p, D p/H ∂μ)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    _ = (∫ p, D p ∂μ)/H := by
      rw [integral_div,ENNReal.toReal_ofReal (div_nonneg (integral_nonneg hpos) hH.le)]
    _ = _ := by rw [typed_windowMass_integral_eq_unmarked M lambda a b R n]

theorem testDifference_probability_tendsto_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n).real
        {p | ε ≤ |testDifference M hM a b R n F p|}) atTop (𝓝 0) := by
  obtain ⟨B,hB,hbound⟩ := exists_window_mass_bound M hM hQP lambda a b ha hab R 1 zero_lt_one
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
    have hV : V ∈ 𝓝 (perronMark M hM) :=
      (continuous_ofProbability.tendsto (perronMark M hM)) hU
    have hbad := badWeakEvent_probability_tendsto_zero M hM hQP lambda a b ha hab R V hV
    filter_upwards [hbad.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < γ/2))] with n hn
    let μ := AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n
    let A : Set (AnnealedTypedGraph.State S n) :=
      {p | (H : ℝ) < (Fintype.card (WindowComponent a b R 1 (AnnealedTypedGraph.graph p)) : ℝ)}
    have hsub : {p : AnnealedTypedGraph.State S n | ε ≤ |testDifference M hM a b R n F p|} ⊆
        A ∪ badWeakEvent a b R n V := by
      intro p hp
      by_cases hA : p ∈ A
      · exact Or.inl hA
      · right
        by_contra hv
        have hcard : Fintype.card (WindowComponent a b R 1 (AnnealedTypedGraph.graph p)) ≤ H := by
          have hAR : ¬ (H : ℝ) <
              (Fintype.card (WindowComponent a b R 1 (AnnealedTypedGraph.graph p)) : ℝ) := hA
          exact_mod_cast (le_of_not_gt hAR)
        have hy (C : WindowComponent a b R 1 (AnnealedTypedGraph.graph p)) :
            ofProbability (componentMark p.1 C.val) ∈ U := by
          by_contra hC
          exact hv ⟨C,hC⟩
        have hh := ofFintype_mark_close (perronWeakMark M hM) H F (ε/2) U hclose hcard
          (windowAtom a b R 1) (fun C ↦ ofProbability (componentMark p.1 C.val)) hy
        have hl : |testDifference M hM a b R n F p| < ε/2 := hh
        exact (not_lt_of_ge hp) (hl.trans (by linarith))
    have hs : μ.real {p | ε ≤ |testDifference M hM a b R n F p|} ≤
        B/(H : ℝ)+μ.real (badWeakEvent a b R n V) := by
      apply ((measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)).trans
      apply add_le_add _ le_rfl
      exact (sample_mass_probability_le M lambda a b R n H hHp).trans
        (div_le_div_of_nonneg_right (hbound n) hHp.le)
    exact hs.trans_lt (by change B/(H : ℝ)+_ < γ; linarith)

/-- Genuine bounded continuous point-process tests are L1-close on the
actual sampled graph/type probability space to constant Perron marking. -/
theorem testDifference_l1_tendsto_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ p, |testDifference M hM a b R n F p|
      ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n) atTop (𝓝 0) :=
  integral_abs_tendsto_zero
    (fun n ↦ AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n)
    (fun n ↦ testDifference M hM a b R n F)
    (fun n ↦ testDifference_measurable M hM a b R n F)
    (2*‖F‖) (by positivity) (fun n p ↦ testDifference_bound M hM a b R n F p)
    (fun ε hε ↦ testDifference_probability_tendsto_zero M hM hQP lambda a b ha hab R F ε hε)

end PerronWright.ComponentWindowMarkedTransfer
