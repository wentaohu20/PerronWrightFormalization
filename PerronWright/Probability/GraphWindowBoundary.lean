import PerronWright.Probability.GraphWindowFactorialLimits
import PerronWright.Probability.CompactWindowBoundary

/-! # Boundary nullity for actual finite-graph window limits

The literal source is a probability measure on graphs with `n+1` vertices.
The proved uniform local factorial conclusion gives a width-sensitive
first-mass bound. Open-set Portmanteau and shrinking strips imply that
every weak subsequential window limit has no fixed size-coordinate atom.
Half-open cell counts are consequently almost everywhere continuous.
No boundary-nullity or count-continuity assumption is introduced.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GraphWindowBoundary

open ComponentCounts ComponentWindowPointMeasures ComponentWindowFactorialCounts
open FinitePointMeasureCompact FinitePointMeasureMeasurable PointMeasureBoundary
open GraphWindowSource GraphWindowFactorialLimits
open CompactWindowBoundary (boundary openStrip isClosed_boundary measurableSet_boundary
  isOpen_openStrip boundary_subset_openStrip integerWindow_one_card_le surplusIndices_one_card
  count_openStrip_le_slice frontier_sizeSurplusCell_subset frontier_Ico_subset frontier_Ioc_subset)

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]

omit [∀ n, IsProbabilityMeasure (ρ n)] in
/-- Uniform numerical local convergence yields the genuine single-component
integer expectation bound on every fixed positive size window. -/
theorem exists_integer_one_expectation_bound {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop, ∀ k r : Fin 1 → ℕ,
      (∀ i, r i ≤ R) →
      (∀ i, (k i : ℝ)/((n+1 : ℕ) : ℝ)^(2/3 : ℝ) ∈ Set.Icc a b) →
      (∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n) ≤
        B/((n+1 : ℕ) : ℝ)^(2/3 : ℝ) := by
  obtain ⟨B,hB,hbound⟩ := exists_uniform_scaled_bound ρ hbeta hlocal
    (q := 1) (by omega) R ha hab
  refine ⟨B,hB,?_⟩
  filter_upwards [hbound] with n hn k r hr hk
  have hd : 0 < ((n+1 : ℕ) : ℝ)^(2/3 : ℝ) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) _
  let y : Fin 1 → ℝ := fun i ↦ (k i : ℝ)/((n+1 : ℕ) : ℝ)^(2/3 : ℝ)
  have hf : (fun i ↦ CriticalScaling.size (y i) (n+1)) = k := by
    funext i
    dsimp only [y,CriticalScaling.size]
    rw [div_mul_cancel₀ _ hd.ne']
    simp
  have he := hn r hr y (FactorialDensity.mem_sizeWindow.mpr hk)
  simp only [localExpectation,hf] at he
  norm_num only [Nat.cast_one,mul_one] at he
  apply (le_div_iff₀ hd).mpr
  simpa only [mul_comm] using (le_abs_self _).trans he

/-- The exact q=1 source factorial estimate sums to a width-sensitive
first-mass estimate for every closed subwindow. -/
theorem slice_mass_integral_le (a b lo hi : ℝ)
    (R n : ℕ) (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hal : a ≤ lo) (hhb : hi ≤ b) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ k r : Fin 1 → ℕ,
      (∀ i, r i ≤ R) →
      (∀ i, (k i : ℝ) / ((n+1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b) →
      (∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n) ≤
          B / ((n+1 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) :
    (∫ η, (mass η : ℝ) ∂(windowLaw ρ lo hi R n :
      Measure (PointMeasure (SurplusWindow lo hi R)))) ≤
      B * (R + 1 : ℕ) * (hi - lo + 1 / ((n+1 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) := by
  let d : ℝ := ((n+1 : ℕ) : ℝ) ^ (2 / 3 : ℝ)
  have hd : 0 < d := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) _
  have he : (∫ η, (mass η : ℝ) ∂(windowLaw ρ lo hi R n :
      Measure (PointMeasure (SurplusWindow lo hi R)))) =
      ∫ η, ((size η).descFactorial 1 : ℝ) ∂(windowLaw ρ lo hi R n :
        Measure (PointMeasure (SurplusWindow lo hi R))) := by
    simp only [Nat.descFactorial_one, mass_eq_size, NNReal.coe_natCast]
  rw [he, windowLaw_descFactorial_expectation_eq_sum ρ lo hi (hlo.trans hlh)
    R n 1]
  have hsum : (∑ r ∈ surplusIndices 1 R,
      ∑ k ∈ integerWindow d (fun _ ↦ lo) (fun _ ↦ hi),
        (∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n)) ≤
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
    _ = B * (R + 1 : ℕ) * (hi - lo + 1 / ((n+1 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) := by
      change _ = B * (R + 1 : ℕ) * (hi - lo + 1 / d)
      field_simp [hd.ne']

/-- One fixed-window q=1 bound controls every center and every positive
strip width, uniformly along the source graph sequence. -/
theorem exists_eventual_openStrip_integral_bound {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop, ∀ c ∈ Set.Icc a b, ∀ δ : ℝ, 0 < δ →
      (∫ η, ((η : FiniteMeasure (SurplusWindow a b R)) :
        Measure (SurplusWindow a b R)).real (openStrip a b R c δ)
        ∂(windowLaw ρ a b R n :
          Measure (PointMeasure (SurplusWindow a b R)))) ≤
            B * (R + 1 : ℕ) * (2 * δ + 1 / ((n+1 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ :=
    exists_integer_one_expectation_bound ρ hbeta hlocal a b ha hab R
  refine ⟨B, hB, ?_⟩
  filter_upwards [hb] with n hn
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
  have hslice := slice_mass_integral_le ρ a b lo hi R n
    hlo hlh (le_max_left _ _) (min_le_left _ _) B hB.le (by
      intro k r hr hk
      have hh := hn k r hr hk
      norm_num only [Nat.cast_one, mul_one] at hh
      exact hh)
  have hmeas := (isOpen_openStrip a b R c δ).measurableSet
  have hcompare : (∫ η, ((η : FiniteMeasure (SurplusWindow a b R)) :
        Measure (SurplusWindow a b R)).real (openStrip a b R c δ)
        ∂(windowLaw ρ a b R n :
          Measure (PointMeasure (SurplusWindow a b R)))) ≤
      ∫ η, (mass η : ℝ) ∂(windowLaw ρ lo hi R n :
        Measure (PointMeasure (SurplusWindow lo hi R))) := by
    simp_rw [measure_real_eq_count _ hmeas]
    have hcount : Measurable (fun η : PointMeasure (SurplusWindow a b R) ↦
        (count η (openStrip a b R c δ) : ℝ)) :=
      (measurable_of_countable (fun z : ℕ ↦ (z : ℝ))).comp (measurable_count hmeas)
    have hmass : Measurable (fun η : PointMeasure (SurplusWindow lo hi R) ↦
        (mass η : ℝ)) := NNReal.continuous_coe.measurable.comp measurable_mass
    rw [windowLaw_integral ρ a b R n
      hcount, windowLaw_integral ρ lo hi R n hmass]
    apply integral_mono Integrable.of_finite Integrable.of_finite
    intro G
    simpa only [mass_eq_size, NNReal.coe_natCast] using
      (Nat.cast_le (α := ℝ)).mpr (count_openStrip_le_slice a b R c δ G)
  apply (hcompare.trans hslice).trans
  gcongr

/-- The actual expected open-strip mass of any actual weak subsequential
limit is at most a constant times its width. -/
theorem exists_limit_openStrip_lintegral_bound {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν)) :
    ∃ B : ℝ, 0 < B ∧ ∀ c ∈ Set.Icc a b, ∀ δ : ℝ, 0 < δ →
      (∫⁻ η, ((η : FiniteMeasure (SurplusWindow a b R)) :
        Measure (SurplusWindow a b R)) (openStrip a b R c δ)
        ∂(ν : Measure (PointMeasure (SurplusWindow a b R)))) ≤
          ENNReal.ofReal (B * (R + 1 : ℕ) * (2 * δ)) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  obtain ⟨B, hB, hb⟩ := exists_eventual_openStrip_integral_bound ρ hbeta hlocal a b ha hab R
  refine ⟨B, hB, ?_⟩
  intro c hc δ hδ
  have hd : Tendsto (fun n : ℕ ↦ ((n+1 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hg : Tendsto (fun m ↦ B * (R + 1 : ℕ) *
      (2 * δ + 1 / ((N m+1 : ℕ) : ℝ) ^ (2 / 3 : ℝ))) atTop
      (𝓝 (B * (R + 1 : ℕ) * (2 * δ))) := by
    simpa only [one_div, add_zero, Pi.inv_apply, Function.comp_def] using
      tendsto_const_nhds.mul (tendsto_const_nhds.add ((hd.comp hN).inv_tendsto_atTop))
  apply lintegral_eval_open_le_of_eventual_bound (E := SurplusWindow a b R)
    (fun m ↦ windowLaw ρ a b R (N m)) ν hν (isOpen_openStrip a b R c δ)
    (fun m ↦ windowLaw_integrable ρ a b R (N m)
      (measurable_eval_real (isOpen_openStrip a b R c δ).measurableSet))
    _ _ hg
  exact (hN.eventually hb).mono (fun m hm ↦ hm c hc δ hδ)

/-- Every fixed size-coordinate boundary, including either endpoint,
almost surely carries no actual point in a genuine weak subsequential
limit of the model window laws. -/
theorem ae_boundary_eq_zero {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν))
    (c : ℝ) :
    ∀ᵐ η : PointMeasure (SurplusWindow a b R) ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) :
        Measure (SurplusWindow a b R)) (boundary a b R c) = 0 := by
  by_cases hc : c ∈ Set.Icc a b
  · let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
    let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
    obtain ⟨B, hB, hb⟩ :=
      exists_limit_openStrip_lintegral_bound ρ hbeta hlocal a b ha hab R N hN ν hν
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

theorem ae_boundary_count_eq_zero {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν))
    (c : ℝ) :
    ∀ᵐ η ∂(ν : Measure (PointMeasure (SurplusWindow a b R))), count η (boundary a b R c) = 0 := by
  filter_upwards [ae_boundary_eq_zero ρ hbeta hlocal a b ha hab R N hN ν hν c] with η hη
  have hz : (η : FiniteMeasure (SurplusWindow a b R)) (boundary a b R c) = 0 :=
    (FiniteMeasure.null_iff_toMeasure_null _ _).mpr hη
  simp [FinitePointMeasureCompact.count, hz]

theorem boundary_lintegral_eq_zero {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν))
    (c : ℝ) :
    (∫⁻ η, ((η : FiniteMeasure (SurplusWindow a b R)) :
      Measure (SurplusWindow a b R)) (boundary a b R c)
      ∂(ν : Measure (PointMeasure (SurplusWindow a b R)))) = 0 := by
  exact (lintegral_eq_zero_iff (measurable_eval (measurableSet_boundary a b R c))).mpr
    (ae_boundary_eq_zero ρ hbeta hlocal a b ha hab R N hN ν hν c)

theorem boundary_integral_eq_zero {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν))
    (c : ℝ) :
    (∫ η, ((η : FiniteMeasure (SurplusWindow a b R)) :
      Measure (SurplusWindow a b R)).real (boundary a b R c)
      ∂(ν : Measure (PointMeasure (SurplusWindow a b R)))) = 0 := by
  have hz : (fun η : PointMeasure (SurplusWindow a b R) ↦
      ((η : FiniteMeasure (SurplusWindow a b R)) :
        Measure (SurplusWindow a b R)).real (boundary a b R c))
          =ᵐ[(ν : Measure (PointMeasure (SurplusWindow a b R)))] 0 := by
    filter_upwards [ae_boundary_eq_zero ρ hbeta hlocal a b ha hab R N hN ν hν c]
      with η hη
    simp only [measureReal_def, hη, ENNReal.toReal_zero, Pi.zero_apply]
  rw [integral_congr_ae hz]
  simp only [Pi.zero_apply, integral_zero]

theorem ae_sizeSurplusCell_frontier_eq_zero {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν))
    (J : Set ℝ) (T : Set ℕ) (lo hi : ℝ) (hJ : frontier J ⊆ {lo, hi}) :
    ∀ᵐ η : PointMeasure (SurplusWindow a b R) ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (windowEmbedding a b R ⁻¹' (J ×ˢ T))) = 0 := by
  filter_upwards [ae_boundary_eq_zero ρ hbeta hlocal a b ha hab R N hN ν hν lo,
    ae_boundary_eq_zero ρ hbeta hlocal a b ha hab R N hN ν hν hi] with η hl hh
  apply measure_mono_null (frontier_sizeSurplusCell_subset a b R J T lo hi hJ)
  exact measure_union_null hl hh

theorem ae_Ico_cell_frontier_eq_zero {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν))
    (lo hi : ℝ) (T : Set ℕ) :
    ∀ᵐ η : PointMeasure (SurplusWindow a b R) ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (windowEmbedding a b R ⁻¹' (Set.Ico lo hi ×ˢ T))) = 0 :=
  ae_sizeSurplusCell_frontier_eq_zero ρ hbeta hlocal a b ha hab R N hN ν hν
    _ T lo hi (frontier_Ico_subset lo hi)

theorem ae_Ioc_cell_frontier_eq_zero {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν))
    (lo hi : ℝ) (T : Set ℕ) :
    ∀ᵐ η : PointMeasure (SurplusWindow a b R) ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (windowEmbedding a b R ⁻¹' (Set.Ioc lo hi ×ˢ T))) = 0 :=
  ae_sizeSurplusCell_frontier_eq_zero ρ hbeta hlocal a b ha hab R N hN ν hν
    _ T lo hi (frontier_Ioc_subset lo hi)

/-- The genuine finite vector of half-open cell counts is continuous at
almost every actual limiting point measure. This is a conclusion of
the model bounds, not an assumed continuous-mapping interface. -/
theorem ae_continuousAt_Ico_count_vector {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν))
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
    fun i ↦ ae_Ico_cell_frontier_eq_zero ρ hbeta hlocal a b ha hab R N hN ν hν
      (lo i) (hi i) (T i)
  filter_upwards [ae_all_iff.mpr hfront] with η hη
  exact FinitePointMeasureCounts.tendsto_count_vector_of_null_frontiers tendsto_id
    (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ T i))
    (fun i ↦ (measurable_windowEmbedding a b R)
      (measurableSet_Ico.prod MeasurableSet.of_discrete)) hη

theorem ae_continuousAt_Ioc_count_vector {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν))
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
    fun i ↦ ae_Ioc_cell_frontier_eq_zero ρ hbeta hlocal a b ha hab R N hN ν hν
      (lo i) (hi i) (T i)
  filter_upwards [ae_all_iff.mpr hfront] with η hη
  exact FinitePointMeasureCounts.tendsto_count_vector_of_null_frontiers tendsto_id
    (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ioc (lo i) (hi i) ×ˢ T i))
    (fun i ↦ (measurable_windowEmbedding a b R)
      (measurableSet_Ioc.prod MeasurableSet.of_discrete)) hη

end PerronWright.GraphWindowBoundary



