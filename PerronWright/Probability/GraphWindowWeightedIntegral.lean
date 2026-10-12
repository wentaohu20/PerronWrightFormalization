import PerronWright.Probability.GraphWindowFactorialLimits
import PerronWright.Probability.CriticalWeightedFloorIntegral

/-! # Weighted floor integration for actual finite graph source laws

The graph law is not replaced by a numeric moment interface: its literal
floor expectation is integrated cell by cell. The local formula implies
the weighted limit by dominated convergence, including a.e.-continuous
indicator tests. The countable terminal supplies that formula itself.
-/

open MeasureTheory Set Filter Topology
open scoped Real BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GraphWindowWeightedIntegral

open GraphWindowSource GraphWindowFactorialLimits CriticalWeightedFloorIntegral
  CriticalFloorCells CriticalFloorWindow FactorialDensity

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))

theorem integrableOn_weightedFloor_cell {n q : ℕ} (k r : Fin q → ℕ)
    (F : (Fin q → ℝ) → ℝ) :
    IntegrableOn (fun x ↦ F (normalizedFloor (n+1) x) * localExpectation ρ n x r)
      (cell (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) k) volume := by
  apply ((integrableOn_localExpectation_cell ρ k r).const_mul
    (F (normalizedInteger (n+1) k))).congr
  filter_upwards [ae_restrict_mem (measurableSet_cell _ k)] with x hx
  rw [normalizedFloor_eq_on_cell (Nat.succ_pos n) k hx]

theorem integral_weightedFloor_cell {n q : ℕ} (k r : Fin q → ℕ)
    (F : (Fin q → ℝ) → ℝ) :
    (∫ x in cell (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) k,
      F (normalizedFloor (n+1) x) * localExpectation ρ n x r) =
        F (normalizedInteger (n+1) k) * ∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n := by
  calc
    _ = ∫ x in cell (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) k,
        F (normalizedInteger (n+1) k) * localExpectation ρ n x r :=
      setIntegral_congr_fun (measurableSet_cell _ k)
        (fun x hx ↦ by rw [normalizedFloor_eq_on_cell (Nat.succ_pos n) k hx])
    _ = _ := by rw [integral_const_mul, GraphWindowSource.integral_localExpectation_cell]

theorem integral_weightedFloor_grid {n q : ℕ} (A : Finset (Fin q → ℕ))
    (r : Fin q → ℕ) (F : (Fin q → ℝ) → ℝ) :
    (∫ x in ⋃ k ∈ A, cell (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) k,
      F (normalizedFloor (n+1) x) * localExpectation ρ n x r) =
        ∑ k ∈ A, F (normalizedInteger (n+1) k) *
          ∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n := by
  rw [integral_biUnion_finset A (fun k _ ↦ measurableSet_cell _ k)
    (fun _ _ _ _ hkl ↦ disjoint_cells
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) _) hkl)
    (fun k _ ↦ integrableOn_weightedFloor_cell ρ k r F)]
  exact Finset.sum_congr rfl (fun k _ ↦ integral_weightedFloor_cell ρ k r F)

theorem weighted_grid_integral_tendsto {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {q : ℕ} (hq : 0 < q) (r : Fin q → ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (F : (Fin q → ℝ) → ℝ) (B : ℝ) (hB : 0 ≤ B) (hFb : ∀ x, ‖F x‖ ≤ B)
    (hFc : ∀ᵐ x ∂(volume : Measure (Fin q → ℝ)), ContinuousAt F x) :
    Tendsto (fun n : ℕ ↦ ∫ x in sizeWindow q (a/2) (b+1),
      (grid q (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) a b).indicator
        (fun x ↦ F (normalizedFloor (n+1) x) * localExpectation ρ n x r) x)
      atTop (𝓝 (∫ x in sizeWindow q a b, F x * density alpha beta lambda x r)) := by
  let U := sizeWindow q (a/2) (b+1)
  have hUa : 0 < a/2 := by positivity
  have hUab : a/2 ≤ b+1 := by linarith
  have hsub : sizeWindow q a b ⊆ U := by
    intro x hx
    apply mem_sizeWindow.mpr
    intro i
    have hxi := mem_sizeWindow.mp hx i
    constructor <;> linarith [hxi.1,hxi.2]
  let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr (by
    change volume (Set.Icc (fun _ : Fin q ↦ a/2) (fun _ ↦ b+1)) ≠ ⊤
    exact isCompact_Icc.measure_lt_top.ne)
  let R := Finset.univ.sup r
  have hr (i) : r i ≤ R := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨A,hA,hbound⟩ := exists_uniform_scaled_bound ρ hbeta hlocal hq R hUa hUab
  have hwms : MeasurableSet (sizeWindow q a b) := measurableSet_Icc
  have heq : (∫ x in U, (sizeWindow q a b).indicator
      (fun x ↦ F x * density alpha beta lambda x r) x) =
      ∫ x in sizeWindow q a b, F x * density alpha beta lambda x r := by
    rw [setIntegral_indicator hwms,Set.inter_eq_right.mpr hsub]
  rw [← heq]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ B*A)
  · exact Eventually.of_forall (fun n ↦
      (((measurable_weightedFloor (n+1) F).mul (measurable_localExpectation ρ n r)).indicator
        (measurableSet_grid q _ a b)).aestronglyMeasurable)
  · filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem (s := U) measurableSet_Icc] with x hx
    by_cases hg : x ∈ grid q (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) a b
    · rw [Set.indicator_of_mem hg,norm_mul]
      have hE : ‖localExpectation ρ n x r‖ ≤ A := by
        simpa only [Real.norm_eq_abs] using hn r hr x hx
      exact mul_le_mul (hFb _) hE (norm_nonneg _) hB
    · simp only [Set.indicator_of_notMem hg,norm_zero]
      exact mul_nonneg hB hA.le
  · exact integrable_const (B*A)
  · have hae : (Set.univ.pi (fun _ : Fin q ↦ Set.Ioo a b)) =ᵐ[(volume : Measure (Fin q → ℝ))]
        sizeWindow q a b := Measure.univ_pi_Ioo_ae_eq_Icc
    filter_upwards [ae_restrict_mem (s := U) measurableSet_Icc,ae_restrict_of_ae hae,
      ae_restrict_of_ae hFc] with x hx he hc
    have hxpos (i) : 0 ≤ x i := hUa.le.trans (mem_sizeWindow.mp hx i).1
    have hfloor : Tendsto (fun n : ℕ ↦ normalizedFloor (n+1) x) atTop (𝓝 x) := by
      apply tendsto_pi_nhds.mpr
      intro i
      exact (CriticalScaling.size_normalized_tendsto (hxpos i)).comp (tendsto_add_atTop_nat 1)
    have hFt := hc.tendsto.comp hfloor
    have hEt := factorial_pointwise_tendsto ρ hlocal hq r hUa hUab x
      (fun i ↦ (mem_sizeWindow.mp hx i).1) (fun i ↦ (mem_sizeWindow.mp hx i).2)
    have hevent := (tendsto_add_atTop_nat 1).eventually
      (critical_grid_indicator_eventually ha hab hxpos (Iff.of_eq he))
    by_cases hw : x ∈ sizeWindow q a b
    · simpa only [Set.indicator_of_mem hw] using (hFt.mul hEt).congr' (by
        filter_upwards [hevent] with n hn
        exact (Set.indicator_of_mem (hn.mpr hw)
          (fun x ↦ F (normalizedFloor (n+1) x) * localExpectation ρ n x r)).symm)
    · simp only [Set.indicator_of_notMem hw]
      apply (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).congr'
      filter_upwards [hevent] with n hn
      exact (Set.indicator_of_notMem (fun h ↦ hw (hn.mp h))
        (fun x ↦ F (normalizedFloor (n+1) x) * localExpectation ρ n x r)).symm

theorem weighted_integer_window_expectation_tendsto {alpha beta lambda : ℝ}
    (hbeta : 0 < beta) (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {q : ℕ} (hq : 0 < q) (r : Fin q → ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (F : (Fin q → ℝ) → ℝ) (B : ℝ) (hB : 0 ≤ B) (hFb : ∀ x, ‖F x‖ ≤ B)
    (hFc : ∀ᵐ x ∂(volume : Measure (Fin q → ℝ)), ContinuousAt F x) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ indices q (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) a b,
      F (normalizedInteger (n+1) k) * ∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n)
      atTop (𝓝 (∫ x in sizeWindow q a b, F x * density alpha beta lambda x r)) := by
  apply (weighted_grid_integral_tendsto ρ hbeta hlocal hq r ha hab F B hB hFb hFc).congr'
  filter_upwards [] with n
  have hh : 0 < ((n+1 : ℕ) : ℝ)^(2/3 : ℝ) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) _
  have hsmall : 1/((n+1 : ℕ) : ℝ)^(2/3 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hh).mpr
    simpa only [one_mul] using Real.one_le_rpow
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (by norm_num : (0 : ℝ) ≤ 2/3)
  have hsub := grid_subset_expanded (q := q) hh ha (ha.le.trans hab) hsmall
  rw [setIntegral_indicator (measurableSet_grid q _ a b),Set.inter_eq_right.mpr hsub]
  exact integral_weightedFloor_grid ρ _ r F

end PerronWright.GraphWindowWeightedIntegral
