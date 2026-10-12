import PerronWright.Probability.CriticalSizeTuple
import PerronWright.Probability.ConnectedTypeDomination

/-!
# Genuine connected sampling on a positive critical-size window

The normalizing constants of the actual connected laws are proved positive
uniformly in the real size window and bounded surplus range.  This removes
the normalization hypotheses when these laws are used in the local theorem.
-/

open Filter Topology
open scoped Real Topology

noncomputable section
set_option maxHeartbeats 600000

namespace PerronWright.CriticalConnectedSampling

/-- Literal floors diverge uniformly when the real size is bounded below
by one fixed positive constant. -/
theorem eventually_size_ge_on_window (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (a : ℝ) (ha : 0 < a) (K : ℕ) :
    ∀ᶠ m in atTop, ∀ x : ℝ, a ≤ x → K ≤ CriticalScaling.size x (N m) := by
  have ht : Tendsto (fun m ↦ (N m : ℝ)^(2/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/3)).comp
      (tendsto_natCast_atTop_atTop.comp hN)
  filter_upwards [ht.eventually (eventually_ge_atTop ((K : ℝ)/a))] with m hm x hx
  apply Nat.le_floor
  have h := mul_le_mul_of_nonneg_right hm ha.le
  rw [div_mul_cancel₀ _ ha.ne'] at h
  calc
    (K : ℝ) ≤ (N m : ℝ)^(2/3 : ℝ) * a := h
    _ ≤ (N m : ℝ)^(2/3 : ℝ) * x :=
      mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = x * (N m : ℝ)^(2/3 : ℝ) := mul_comm _ _

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Positivity is derived from actual enumeration, not a new sampling
interface.  It is uniform even over all real continuous fields. -/
theorem eventually_normalizers_pos_on_window (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (a : ℝ) (ha : 0 < a) :
    ∀ᶠ m in atTop, ∀ x : ℝ, a ≤ x → ∀ r : ℕ, r ≤ R → ∀ g : C(S,ℝ),
      0 < M.fieldConnectedWeight g (CriticalScaling.size x (N m)) r := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (ConnectedTypeLaw.eventually_all_field_normalizers_pos M hM R)
  filter_upwards [eventually_size_ge_on_window N hN a ha K] with m hm x hx r hr g
  exact hK _ (hm x hx) r hr g

end PerronWright.CriticalConnectedSampling
