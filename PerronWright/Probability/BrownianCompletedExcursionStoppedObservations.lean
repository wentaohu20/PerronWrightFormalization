import PerronWright.Probability.BrownianMinimumFutureReturnPathGeometry
import Mathlib.Order.Interval.Finset.Fin

/-! # Actual stopped-zero observations and finite lifetime strata

The true source hits zero at its literal positive return. Hence its whole
stopped path is the original path strictly before that return and zero at
and after it. A monotone finite observation vector has a unique initial
segment before each lifetime; the corresponding measurable strata form
a genuine disjoint partition. No excursion shape law is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedExcursionStoppedObservations

open BrownianPathLaw BrownianPathIndependentIncrements
open BrownianMinimumFutureEntranceSource BrownianMinimumFutureFirstReturn
open BrownianMinimumFutureReturnPathGeometry

theorem pastPath_zero_endpoint (ζ : ℝ≥0) (g : Path) (hg : g ζ = 0) (t : ℝ≥0) :
    pastPath ζ g t = if t < ζ then g t else 0 := by
  by_cases ht : t < ζ
  · simp only [pastPath_eval, min_eq_left ht.le, if_pos ht]
  · simp only [pastPath_eval, min_eq_right (le_of_not_gt ht), hg, if_neg ht]

theorem ae_returnTaggedPast_zero_fill :
    ∀ᵐ g : Path ∂unitSourceLaw, ∀ t : ℝ≥0,
      (returnTaggedPast g).2 t = if t < (returnTaggedPast g).1 then g t else 0 := by
  filter_upwards [ae_unitSourceLaw_firstReturn_exact_zero] with g hg
  intro t
  exact pastPath_zero_endpoint _ g hg t

def aliveCount (N : ℕ) (times : Fin N → ℝ≥0) (ζ : ℝ≥0) : ℕ :=
  (Finset.univ.filter (fun i ↦ times i < ζ)).card

theorem aliveCount_le (N : ℕ) (times : Fin N → ℝ≥0) (ζ : ℝ≥0) :
    aliveCount N times ζ ≤ N := by
  simpa only [aliveCount, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun i ↦ times i < ζ)

theorem before_lifetime_iff_index_lt_count (N : ℕ) (times : Fin N → ℝ≥0)
    (hmono : Monotone times) (ζ : ℝ≥0) (i : Fin N) :
    times i < ζ ↔ i.val < aliveCount N times ζ := by
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j ↦ times j < ζ) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        (hmono (Finset.mem_Iic.mp hj)).trans_lt hi⟩
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    change i.val + 1 ≤ aliveCount N times ζ at hc
    omega
  · intro hi
    by_contra htime
    have hsub : Finset.univ.filter (fun j ↦ times j < ζ) ⊆ Finset.Iio i := by
      intro j hj
      have hbefore := (Finset.mem_filter.mp hj).2
      apply Finset.mem_Iio.mpr
      exact lt_of_not_ge (fun hji ↦ htime ((hmono hji).trans_lt hbefore))
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    change aliveCount N times ζ ≤ i.val at hc
    omega

def lifetimeStratum (N : ℕ) (times : Fin N → ℝ≥0) (k : Fin (N + 1)) : Set ℝ≥0 :=
  {ζ | ∀ i : Fin N, times i < ζ ↔ i.val < k.val}

theorem measurableSet_lifetimeStratum (N : ℕ) (times : Fin N → ℝ≥0) (k : Fin (N + 1)) :
    MeasurableSet (lifetimeStratum N times k) := by
  have hm (i : Fin N) : MeasurableSet {ζ : ℝ≥0 | times i < ζ ↔ i.val < k.val} := by
    by_cases hi : i.val < k.val
    · simpa only [hi, iff_true, id_eq] using measurableSet_lt (measurable_const : Measurable (fun _ : ℝ≥0 ↦ times i)) measurable_id
    · simpa only [hi, iff_false, not_lt, id_eq] using measurableSet_le measurable_id (measurable_const : Measurable (fun _ : ℝ≥0 ↦ times i))
  simpa only [lifetimeStratum, Set.ofPred_forall] using MeasurableSet.iInter hm

theorem lifetime_mem_count_stratum (N : ℕ) (times : Fin N → ℝ≥0) (hmono : Monotone times)
    (ζ : ℝ≥0) :
    ζ ∈ lifetimeStratum N times ⟨aliveCount N times ζ, by have h := aliveCount_le N times ζ; omega⟩ := by
  intro i
  exact before_lifetime_iff_index_lt_count N times hmono ζ i

theorem lifetimeStrata_disjoint (N : ℕ) (times : Fin N → ℝ≥0)
    (k l : Fin (N + 1)) (hkl : k ≠ l) :
    Disjoint (lifetimeStratum N times k) (lifetimeStratum N times l) := by
  apply Set.disjoint_left.mpr
  intro ζ hk hl
  have hval : k.val ≠ l.val := fun he ↦ hkl (Fin.ext he)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · let i : Fin N := ⟨k.val, by have h := l.isLt; omega⟩
    have ht : times i < ζ := (hl i).mpr hlt
    have hi := (hk i).mp ht
    exact (lt_irrefl k.val) hi
  · let i : Fin N := ⟨l.val, by have h := k.isLt; omega⟩
    have ht : times i < ζ := (hk i).mpr hgt
    have hi := (hl i).mp ht
    exact (lt_irrefl l.val) hi

theorem lifetimeStrata_cover (N : ℕ) (times : Fin N → ℝ≥0) (hmono : Monotone times) :
    (⋃ k : Fin (N + 1), lifetimeStratum N times k) = univ := by
  apply Set.eq_univ_of_forall
  intro ζ
  exact mem_iUnion.mpr ⟨⟨aliveCount N times ζ, by have h := aliveCount_le N times ζ; omega⟩,
    lifetime_mem_count_stratum N times hmono ζ⟩

def zeroFill (N : ℕ) (k : Fin (N + 1)) (v : Fin k.val → ℝ) : Fin N → ℝ := fun i ↦
  if hi : i.val < k.val then v ⟨i.val, hi⟩ else 0

theorem continuous_zeroFill (N : ℕ) (k : Fin (N + 1)) : Continuous (zeroFill N k) := by
  apply continuous_pi
  intro i
  by_cases hi : i.val < k.val
  · simp only [zeroFill, dif_pos hi]
    exact continuous_apply _
  · simp only [zeroFill, dif_neg hi]
    exact continuous_const

theorem stopped_tuple_zeroFill (N : ℕ) (times : Fin N → ℝ≥0) (ζ : ℝ≥0)
    (k : Fin (N + 1)) (hζ : ζ ∈ lifetimeStratum N times k) (g : Path) (hg : g ζ = 0) :
    (fun i : Fin N ↦ pastPath ζ g (times i)) =
      zeroFill N k (fun j : Fin k.val ↦ g (times ⟨j.val, by have h := k.isLt; omega⟩)) := by
  funext i
  rw [pastPath_zero_endpoint ζ g hg]
  by_cases hi : i.val < k.val
  · rw [if_pos ((hζ i).mpr hi)]
    simp only [zeroFill, dif_pos hi]
  · rw [if_neg (fun ht ↦ hi ((hζ i).mp ht))]
    simp only [zeroFill, dif_neg hi]

theorem ae_returnTaggedPast_tuple_zeroFill (N : ℕ) (times : Fin N → ℝ≥0) :
    ∀ᵐ g : Path ∂unitSourceLaw, ∀ k : Fin (N + 1),
      (returnTaggedPast g).1 ∈ lifetimeStratum N times k →
      (fun i : Fin N ↦ (returnTaggedPast g).2 (times i)) =
        zeroFill N k (fun j : Fin k.val ↦ g (times ⟨j.val, by have h := k.isLt; omega⟩)) := by
  filter_upwards [ae_unitSourceLaw_firstReturn_exact_zero] with g hg
  intro k hk
  exact stopped_tuple_zeroFill N times _ k hk g hg

theorem lintegral_eq_sum_lifetime_strata (N : ℕ) (times : Fin N → ℝ≥0)
    (hmono : Monotone times) (μ : Measure (ℝ≥0 × Path))
    (H : ℝ≥0 × Path → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ q, H q ∂μ) = ∑ k : Fin (N + 1),
      ∫⁻ q in {q : ℝ≥0 × Path | q.1 ∈ lifetimeStratum N times k}, H q ∂μ := by
  have hs (k : Fin (N + 1)) : MeasurableSet {q : ℝ≥0 × Path | q.1 ∈ lifetimeStratum N times k} :=
    measurable_fst (measurableSet_lifetimeStratum N times k)
  simp_rw [← lintegral_indicator (hs _)]
  rw [← lintegral_finsetSum _ (fun k _ ↦ hH.indicator (hs k))]
  apply lintegral_congr
  intro q
  let k : Fin (N + 1) := ⟨aliveCount N times q.1, by have h := aliveCount_le N times q.1; omega⟩
  have hk : q.1 ∈ lifetimeStratum N times k := lifetime_mem_count_stratum N times hmono q.1
  symm
  rw [Finset.sum_eq_single k]
  · have hkQ : q ∈ {q : ℝ≥0 × Path | q.1 ∈ lifetimeStratum N times k} := hk
    exact indicator_of_mem hkQ H
  · intro l hl hlk
    apply indicator_of_notMem
    intro hmem
    exact Set.disjoint_left.mp (lifetimeStrata_disjoint N times l k hlk) hmem hk
  · intro hnot
    exact (hnot (Finset.mem_univ k)).elim

end PerronWright.BrownianCompletedExcursionStoppedObservations
