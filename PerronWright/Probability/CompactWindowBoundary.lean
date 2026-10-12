import PerronWright.Probability.PointMeasureBoundary
import PerronWright.Probability.FinitePointMeasureCounts
import PerronWright.Probability.ComponentWindowFactorialCounts
import PerronWright.Probability.CompactAnnealedFactorialBound
import Mathlib.Topology.Order.DenselyOrdered

/-!
# No fixed size-boundary atoms in actual compact-window weak law limits

The single fixed-window integer factorial bound is used for every
shrinking size strip. The exact number of integer sizes is at most its
scaled width plus one. Open-strip Portmanteau then transfers the
resulting expectation bound in the correct lower-semicontinuous
direction, and shrinking strips prove actual almost sure boundary
nullity. No atom-free or continuity-set premise is imposed on the
model law.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.CompactWindowBoundary

open ComponentCounts ComponentWindowPointMeasures ComponentWindowFactorialCounts
open FinitePointMeasureCompact FinitePointMeasureMeasurable PointMeasureBoundary

def boundary (a b : ℝ) (R : ℕ) (c : ℝ) : Set (SurplusWindow a b R) :=
  {z | z.1.val = c}

def openStrip (a b : ℝ) (R : ℕ) (c δ : ℝ) : Set (SurplusWindow a b R) :=
  {z | |z.1.val - c| < δ}

theorem isClosed_boundary (a b : ℝ) (R : ℕ) (c : ℝ) :
    IsClosed (boundary a b R c) :=
  isClosed_eq (continuous_subtype_val.comp continuous_fst) continuous_const

theorem measurableSet_boundary (a b : ℝ) (R : ℕ) (c : ℝ) :
    MeasurableSet (boundary a b R c) := (isClosed_boundary a b R c).measurableSet

theorem isOpen_openStrip (a b : ℝ) (R : ℕ) (c δ : ℝ) :
    IsOpen (openStrip a b R c δ) :=
  isOpen_lt ((continuous_subtype_val.comp continuous_fst).sub continuous_const).abs
    continuous_const

theorem boundary_subset_openStrip (a b : ℝ) (R : ℕ) (c δ : ℝ) (hδ : 0 < δ) :
    boundary a b R c ⊆ openStrip a b R c δ := by
  intro z hz
  change |z.1.val - c| < δ
  rw [hz, sub_self, abs_zero]
  exact hδ

/-- This estimate counts genuine integer sizes, including an extra
possible grid point and with no asymptotic replacement of the grid. -/
theorem integerWindow_one_card_le (d lo hi : ℝ) (hd : 0 < d)
    (hlo : 0 ≤ lo) (hlh : lo ≤ hi) :
    ((integerWindow d (fun _ : Fin 1 ↦ lo) (fun _ ↦ hi)).card : ℝ) ≤
      (hi - lo) * d + 1 := by
  have hceil : ⌈lo * d⌉₊ ≤ ⌊hi * d⌋₊ + 1 :=
    (Nat.ceil_le_ceil (mul_le_mul_of_nonneg_right hlh hd.le)).trans
      (Nat.ceil_le_floor_add_one _)
  have hfloor : (⌊hi * d⌋₊ : ℝ) ≤ hi * d :=
    Nat.floor_le (mul_nonneg (hlo.trans hlh) hd.le)
  have hc : lo * d ≤ (⌈lo * d⌉₊ : ℝ) := Nat.le_ceil _
  simp only [integerWindow, Pi.card_Icc, Fin.prod_univ_one, Nat.card_Icc]
  rw [Nat.cast_sub hceil]
  push_cast
  nlinarith

theorem surplusIndices_one_card (R : ℕ) : (surplusIndices 1 R).card = R + 1 := by
  simp [surplusIndices, Pi.card_Icc]

/-- A genuine graph's open-strip count is bounded by the genuine
closed clipped-window mass, via an injective map of literal components. -/
theorem count_openStrip_le_slice (a b : ℝ) (R : ℕ) (c δ : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    count (windowPointMeasure a b R 1 G) (openStrip a b R c δ) ≤
      size (windowPointMeasure (max a (c - δ)) (min b (c + δ)) R 1 G) := by
  rw [windowPointMeasure_count _ _ _ _ _ (isOpen_openStrip a b R c δ).measurableSet,
    windowPointMeasure_size]
  let f : {C : WindowComponent a b R 1 G //
      windowAtom a b R 1 C ∈ openStrip a b R c δ} →
      WindowComponent (max a (c - δ)) (min b (c + δ)) R 1 G := fun C ↦
    ⟨C.val.val, by
      have hs := C.property
      change |(componentAtom 1 C.val.val).1 - c| < δ at hs
      have hslow := (abs_lt.mp hs).1
      have hshi := (abs_lt.mp hs).2
      exact ⟨⟨max_le C.val.property.1.1 (by linarith),
        le_min C.val.property.1.2 (by linarith)⟩, C.val.property.2⟩⟩
  apply Fintype.card_le_of_injective f
  intro C D h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun X : WindowComponent (max a (c - δ)) (min b (c + δ)) R 1 G ↦
    X.val) h

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- The exact q=1 source factorial estimate sums to a width-sensitive
first-mass estimate for every closed subwindow. -/
theorem slice_mass_integral_le (M : CompactBJRModel S) (lambda a b lo hi : ℝ)
    (R n : ℕ) (hn : 0 < n) (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hal : a ≤ lo) (hhb : hi ≤ b) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ k r : Fin 1 → ℕ,
      (∀ i, r i ≤ R) →
      (∀ i, (k i : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b) →
      (∫ G, (ComponentCounts.count G k r : ℝ) ∂AnnealedGraph.law M
        (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) ≤
          B / (n : ℝ) ^ (2 / 3 : ℝ)) :
    (∫ η, (mass η : ℝ) ∂(unmarkedWindowLaw M lambda lo hi R n :
      Measure (PointMeasure (SurplusWindow lo hi R)))) ≤
      B * (R + 1 : ℕ) * (hi - lo + 1 / (n : ℝ) ^ (2 / 3 : ℝ)) := by
  let d : ℝ := (n : ℝ) ^ (2 / 3 : ℝ)
  have hd : 0 < d := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  have he : (∫ η, (mass η : ℝ) ∂(unmarkedWindowLaw M lambda lo hi R n :
      Measure (PointMeasure (SurplusWindow lo hi R)))) =
      ∫ η, ((size η).descFactorial 1 : ℝ) ∂(unmarkedWindowLaw M lambda lo hi R n :
        Measure (PointMeasure (SurplusWindow lo hi R))) := by
    simp only [Nat.descFactorial_one, mass_eq_size, NNReal.coe_natCast]
  rw [he, windowLaw_descFactorial_expectation_eq_sum M lambda lo hi (hlo.trans hlh)
    R n 1 hn]
  have hsum : (∑ r ∈ surplusIndices 1 R,
      ∑ k ∈ integerWindow d (fun _ ↦ lo) (fun _ ↦ hi),
        (∫ G, (ComponentCounts.count G k r : ℝ) ∂AnnealedGraph.law M
          (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n)) ≤
      ∑ _r ∈ surplusIndices 1 R,
        ∑ _k ∈ integerWindow d (fun _ : Fin 1 ↦ lo) (fun _ ↦ hi), B / d := by
    apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro k hk
    apply hbound k r (mem_surplusIndices.mp hr)
    have hk' := (mem_integerWindow hd (fun _ ↦ lo) (fun _ ↦ hi)
      (fun _ ↦ hlo.trans hlh)).mp hk
    intro i
    exact ⟨hal.trans (hk' i).1, (hk' i).2.trans hhb⟩
  apply hsum.trans
  simp only [Finset.sum_const, nsmul_eq_mul, surplusIndices_one_card]
  have hcard := integerWindow_one_card_le d lo hi hd hlo hlh
  calc
    ((R + 1 : ℕ) : ℝ) *
        (((integerWindow d (fun _ : Fin 1 ↦ lo) (fun _ ↦ hi)).card : ℝ) * (B / d)) ≤
      ((R + 1 : ℕ) : ℝ) * (((hi - lo) * d + 1) * (B / d)) := by
        gcongr
    _ = B * (R + 1 : ℕ) * (hi - lo + 1 / (n : ℝ) ^ (2 / 3 : ℝ)) := by
      change _ = B * (R + 1 : ℕ) * (hi - lo + 1 / d)
      field_simp [hd.ne']

/-- One fixed-window q=1 bound controls every center and every positive
strip width, uniformly along the source graph sequence. -/
theorem exists_eventual_openStrip_integral_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop, ∀ c ∈ Set.Icc a b, ∀ δ : ℝ, 0 < δ →
      (∫ η, ((η : FiniteMeasure (SurplusWindow a b R)) :
        Measure (SurplusWindow a b R)).real (openStrip a b R c δ)
        ∂(unmarkedWindowLaw M lambda a b R n :
          Measure (PointMeasure (SurplusWindow a b R)))) ≤
            B * (R + 1 : ℕ) * (2 * δ + 1 / (n : ℝ) ^ (2 / 3 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ :=
    CompactAnnealedFactorialBound.exists_integer_tuple_expectation_bound M hM hQP
      (q := 1) (by omega) R lambda a b ha hab
  refine ⟨B, hB, ?_⟩
  filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
  intro c hc δ hδ
  let lo := max a (c - δ)
  let hi := min b (c + δ)
  have hlo : 0 ≤ lo := ha.le.trans (le_max_left _ _)
  have hlc : lo ≤ c := max_le hc.1 (by linarith)
  have hch : c ≤ hi := le_min hc.2 (by linarith)
  have hlh : lo ≤ hi := hlc.trans hch
  have hwidth : hi - lo ≤ 2 * δ := by
    have hhi : hi ≤ c + δ := min_le_right _ _
    have hlow : c - δ ≤ lo := le_max_right _ _
    linarith
  have hslice := slice_mass_integral_le M lambda a b lo hi R n (by omega)
    hlo hlh (le_max_left _ _) (min_le_left _ _) B hB.le (by
      intro k r hr hk
      have hh := hn k r hr hk
      norm_num only [Nat.cast_one, mul_one] at hh
      exact hh)
  have hmeas := (isOpen_openStrip a b R c δ).measurableSet
  have hcompare : (∫ η, ((η : FiniteMeasure (SurplusWindow a b R)) :
        Measure (SurplusWindow a b R)).real (openStrip a b R c δ)
        ∂(unmarkedWindowLaw M lambda a b R n :
          Measure (PointMeasure (SurplusWindow a b R)))) ≤
      ∫ η, (mass η : ℝ) ∂(unmarkedWindowLaw M lambda lo hi R n :
        Measure (PointMeasure (SurplusWindow lo hi R))) := by
    simp_rw [measure_real_eq_count _ hmeas]
    unfold unmarkedWindowLaw
    rw [windowLaw_count_integral M lambda a b R 1 n hmeas,
      windowLaw_mass_integral M lambda lo hi R 1 n]
    apply integral_mono Integrable.of_finite Integrable.of_finite
    intro G
    have hh := count_openStrip_le_slice a b R c δ G
    rw [windowPointMeasure_count _ _ _ _ _ hmeas, windowPointMeasure_size] at hh
    dsimp only [lo, hi]
    exact Nat.cast_le.mpr hh
  apply (hcompare.trans hslice).trans
  gcongr

/-- The actual expected open-strip mass of any actual weak subsequential
limit is at most a constant times its width. -/
theorem exists_limit_openStrip_lintegral_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) atTop (𝓝 ν)) :
    ∃ B : ℝ, 0 < B ∧ ∀ c ∈ Set.Icc a b, ∀ δ : ℝ, 0 < δ →
      (∫⁻ η, ((η : FiniteMeasure (SurplusWindow a b R)) :
        Measure (SurplusWindow a b R)) (openStrip a b R c δ)
        ∂(ν : Measure (PointMeasure (SurplusWindow a b R)))) ≤
          ENNReal.ofReal (B * (R + 1 : ℕ) * (2 * δ)) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  obtain ⟨B, hB, hb⟩ := exists_eventual_openStrip_integral_bound M hM hQP lambda a b ha hab R
  refine ⟨B, hB, ?_⟩
  intro c hc δ hδ
  have hd : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (2 / 3 : ℝ)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun m ↦ B * (R + 1 : ℕ) *
      (2 * δ + 1 / (N m : ℝ) ^ (2 / 3 : ℝ))) atTop
      (𝓝 (B * (R + 1 : ℕ) * (2 * δ))) := by
    simpa only [one_div, add_zero, Pi.inv_apply, Function.comp_def] using
      tendsto_const_nhds.mul (tendsto_const_nhds.add ((hd.comp hN).inv_tendsto_atTop))
  apply lintegral_eval_open_le_of_eventual_bound (E := SurplusWindow a b R)
    (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) ν hν (isOpen_openStrip a b R c δ)
    (fun m ↦ windowLaw_integrable M lambda a b R 1 (N m)
      (measurable_eval_real (isOpen_openStrip a b R c δ).measurableSet))
    _ _ hg
  exact (hN.eventually hb).mono (fun m hm ↦ hm c hc δ hδ)

/-- Every fixed size-coordinate boundary, including either endpoint,
almost surely carries no actual point in a genuine weak subsequential
limit of the model window laws. -/
theorem ae_boundary_eq_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) atTop (𝓝 ν))
    (c : ℝ) :
    ∀ᵐ η : PointMeasure (SurplusWindow a b R) ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) :
        Measure (SurplusWindow a b R)) (boundary a b R c) = 0 := by
  by_cases hc : c ∈ Set.Icc a b
  · let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
    let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
    obtain ⟨B, hB, hb⟩ :=
      exists_limit_openStrip_lintegral_bound M hM hQP lambda a b ha hab R N hN ν hν
    let δ : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
    have hδpos (m : ℕ) : 0 < δ m := by dsimp only [δ]; positivity
    have hδ : Tendsto δ atTop (𝓝 0) := by
      have ht : Tendsto (fun m : ℕ ↦ (m : ℝ) + 1) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      simpa only [δ, one_div, Function.comp_def] using
        (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ ↦ r⁻¹) atTop (𝓝 0)).comp ht
    have hg : Tendsto (fun m ↦ ENNReal.ofReal (B * (R + 1 : ℕ) * (2 * δ m)))
        atTop (𝓝 0) := by
      have hr : Tendsto (fun m ↦ B * (R + 1 : ℕ) * (2 * δ m)) atTop (𝓝 0) := by
        convert (tendsto_const_nhds.mul (tendsto_const_nhds.mul hδ)) using 1
        simp only [mul_zero]
      simpa only [ENNReal.ofReal_zero, Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto 0).comp hr
    exact ae_eval_eq_zero_of_open_bounds (E := SurplusWindow a b R) ν (boundary a b R c)
      (measurableSet_boundary a b R c) (fun m ↦ openStrip a b R c (δ m))
      (fun m ↦ boundary_subset_openStrip a b R c (δ m) (hδpos m))
      _ hg (fun m ↦ hb c hc (δ m) (hδpos m))
  · have he : boundary a b R c = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hc (hz ▸ z.1.property)
    simp [he]

theorem ae_boundary_count_eq_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) atTop (𝓝 ν))
    (c : ℝ) :
    ∀ᵐ η ∂(ν : Measure (PointMeasure (SurplusWindow a b R))), count η (boundary a b R c) = 0 := by
  filter_upwards [ae_boundary_eq_zero M hM hQP lambda a b ha hab R N hN ν hν c] with η hη
  have hz : (η : FiniteMeasure (SurplusWindow a b R)) (boundary a b R c) = 0 :=
    (FiniteMeasure.null_iff_toMeasure_null _ _).mpr hη
  simp [FinitePointMeasureCompact.count, hz]

theorem boundary_lintegral_eq_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) atTop (𝓝 ν))
    (c : ℝ) :
    (∫⁻ η, ((η : FiniteMeasure (SurplusWindow a b R)) :
      Measure (SurplusWindow a b R)) (boundary a b R c)
      ∂(ν : Measure (PointMeasure (SurplusWindow a b R)))) = 0 := by
  exact (lintegral_eq_zero_iff (measurable_eval (measurableSet_boundary a b R c))).mpr
    (ae_boundary_eq_zero M hM hQP lambda a b ha hab R N hN ν hν c)

theorem boundary_integral_eq_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) atTop (𝓝 ν))
    (c : ℝ) :
    (∫ η, ((η : FiniteMeasure (SurplusWindow a b R)) :
      Measure (SurplusWindow a b R)).real (boundary a b R c)
      ∂(ν : Measure (PointMeasure (SurplusWindow a b R)))) = 0 := by
  have hz : (fun η : PointMeasure (SurplusWindow a b R) ↦
      ((η : FiniteMeasure (SurplusWindow a b R)) :
        Measure (SurplusWindow a b R)).real (boundary a b R c))
          =ᵐ[(ν : Measure (PointMeasure (SurplusWindow a b R)))] 0 := by
    filter_upwards [ae_boundary_eq_zero M hM hQP lambda a b ha hab R N hN ν hν c]
      with η hη
    simp only [measureReal_def, hη, ENNReal.toReal_zero, Pi.zero_apply]
  rw [integral_congr_ae hz]
  simp only [Pi.zero_apply, integral_zero]

/-- The actual relative-window frontier of a size-surplus cell is
contained in its two size boundaries; surplus sets are genuinely clopen. -/
theorem frontier_sizeSurplusCell_subset (a b : ℝ) (R : ℕ)
    (J : Set ℝ) (T : Set ℕ) (lo hi : ℝ) (hJ : frontier J ⊆ {lo, hi}) :
    frontier (windowEmbedding a b R ⁻¹' (J ×ˢ T)) ⊆
      boundary a b R lo ∪ boundary a b R hi := by
  intro z hz
  have hh := (continuous_windowEmbedding a b R).frontier_preimage_subset (J ×ˢ T) hz
  rw [frontier_prod_eq, (isClopen_discrete T).frontier_eq, Set.prod_empty,
    Set.empty_union] at hh
  have hx := hJ hh.1
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, boundary,
    Set.mem_union, Set.mem_ofPred_eq, windowEmbedding] using hx

theorem frontier_Ico_subset (lo hi : ℝ) : frontier (Set.Ico lo hi) ⊆ {lo, hi} := by
  by_cases h : lo < hi
  · rw [frontier_Ico h]
  · rw [Set.Ico_eq_empty h, frontier_empty]
    exact Set.empty_subset _

theorem frontier_Ioc_subset (lo hi : ℝ) : frontier (Set.Ioc lo hi) ⊆ {lo, hi} := by
  by_cases h : lo < hi
  · rw [frontier_Ioc h]
  · rw [Set.Ioc_eq_empty h, frontier_empty]
    exact Set.empty_subset _

theorem ae_sizeSurplusCell_frontier_eq_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) atTop (𝓝 ν))
    (J : Set ℝ) (T : Set ℕ) (lo hi : ℝ) (hJ : frontier J ⊆ {lo, hi}) :
    ∀ᵐ η : PointMeasure (SurplusWindow a b R) ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (windowEmbedding a b R ⁻¹' (J ×ˢ T))) = 0 := by
  filter_upwards [ae_boundary_eq_zero M hM hQP lambda a b ha hab R N hN ν hν lo,
    ae_boundary_eq_zero M hM hQP lambda a b ha hab R N hN ν hν hi] with η hl hh
  apply measure_mono_null (frontier_sizeSurplusCell_subset a b R J T lo hi hJ)
  exact measure_union_null hl hh

theorem ae_Ico_cell_frontier_eq_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) atTop (𝓝 ν))
    (lo hi : ℝ) (T : Set ℕ) :
    ∀ᵐ η : PointMeasure (SurplusWindow a b R) ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (windowEmbedding a b R ⁻¹' (Set.Ico lo hi ×ˢ T))) = 0 :=
  ae_sizeSurplusCell_frontier_eq_zero M hM hQP lambda a b ha hab R N hN ν hν
    _ T lo hi (frontier_Ico_subset lo hi)

theorem ae_Ioc_cell_frontier_eq_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) atTop (𝓝 ν))
    (lo hi : ℝ) (T : Set ℕ) :
    ∀ᵐ η : PointMeasure (SurplusWindow a b R) ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (windowEmbedding a b R ⁻¹' (Set.Ioc lo hi ×ˢ T))) = 0 :=
  ae_sizeSurplusCell_frontier_eq_zero M hM hQP lambda a b ha hab R N hN ν hν
    _ T lo hi (frontier_Ioc_subset lo hi)

/-- The genuine finite vector of half-open cell counts is continuous at
almost every actual limiting point measure. This is a conclusion of
the model bounds, not an assumed continuous-mapping interface. -/
theorem ae_continuousAt_Ico_count_vector (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) atTop (𝓝 ν))
    {d : ℕ} (lo hi : Fin d → ℝ) (T : Fin d → Set ℕ) :
    ∀ᵐ η ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ContinuousAt (fun ζ : PointMeasure (SurplusWindow a b R) ↦ fun i : Fin d ↦
        FinitePointMeasureCompact.count ζ
          (windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ T i))) η := by
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  have hfront : ∀ i : Fin d, ∀ᵐ η : PointMeasure (SurplusWindow a b R)
      ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ T i))) = 0 :=
    fun i ↦ ae_Ico_cell_frontier_eq_zero M hM hQP lambda a b ha hab R N hN ν hν
      (lo i) (hi i) (T i)
  filter_upwards [ae_all_iff.mpr hfront] with η hη
  exact FinitePointMeasureCounts.tendsto_count_vector_of_null_frontiers tendsto_id
    (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ T i))
    (fun i ↦ (measurable_windowEmbedding a b R)
      (measurableSet_Ico.prod MeasurableSet.of_discrete)) hη

theorem ae_continuousAt_Ioc_count_vector (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) atTop (𝓝 ν))
    {d : ℕ} (lo hi : Fin d → ℝ) (T : Fin d → Set ℕ) :
    ∀ᵐ η ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ContinuousAt (fun ζ : PointMeasure (SurplusWindow a b R) ↦ fun i : Fin d ↦
        FinitePointMeasureCompact.count ζ
          (windowEmbedding a b R ⁻¹' (Set.Ioc (lo i) (hi i) ×ˢ T i))) η := by
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  have hfront : ∀ i : Fin d, ∀ᵐ η : PointMeasure (SurplusWindow a b R)
      ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (windowEmbedding a b R ⁻¹' (Set.Ioc (lo i) (hi i) ×ˢ T i))) = 0 :=
    fun i ↦ ae_Ioc_cell_frontier_eq_zero M hM hQP lambda a b ha hab R N hN ν hν
      (lo i) (hi i) (T i)
  filter_upwards [ae_all_iff.mpr hfront] with η hη
  exact FinitePointMeasureCounts.tendsto_count_vector_of_null_frontiers tendsto_id
    (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ioc (lo i) (hi i) ×ˢ T i))
    (fun i ↦ (measurable_windowEmbedding a b R)
      (measurableSet_Ioc.prod MeasurableSet.of_discrete)) hη

end PerronWright.CompactWindowBoundary
