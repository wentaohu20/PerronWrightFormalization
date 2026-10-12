import PerronWright.Probability.ConnectedTypeLaw
import PerronWright.Enumeration.CompactPerronWrightTheorem

/-!
# Positivity of the connected-law normalizer

The connected law's normalization hypothesis is not left as a new
probabilistic interface: the proved Perron--Wright formula implies its
eventual positivity for every fixed bounded surplus range.
-/

open Filter Topology
open scoped Topology Real

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.ConnectedTypeLaw

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem zero_field_eq_connectedWeight (M : CompactBJRModel S) (k r : ℕ) :
    M.fieldConnectedWeight 0 k r = M.connectedWeight 1 k r := by
  have hg : M.scalarField 1 = 0 := by
    ext x
    simp [CompactBJRModel.scalarField]
  simpa only [hg, one_zpow, one_mul] using
    (M.connectedWeight_scalarField 1 zero_lt_one k r).symm

/-- Uniform eventual positivity over every fixed finite surplus range,
derived from enumeration rather than included among the assumptions. -/
theorem eventually_zero_field_normalizer_pos (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ r : ℕ, r ≤ R → 0 < M.fieldConnectedWeight 0 k r := by
  obtain ⟨K, hK, hbound⟩ :=
    CompactPerronWrightTheorem.exists_boundedSurplus_gaussian_relative_bound
      M hM R 0 le_rfl
  have hs : Tendsto (fun k : ℕ ↦ K * (k : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop)
  filter_upwards [hbound, eventually_ge_atTop 1,
    hs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk hk1 hkerr
  intro r hr
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hw := PerronWrightFormulaMainTerm.wrightConstant_pos r
  have hb := M.beta_pos hM
  have hP : 0 < BoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm
      M hM k r 1 := by
    unfold BoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm
    positivity
  have he := hk r hr 1 (by simp)
  have hratio : 0 < M.connectedWeight 1 k r /
      BoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm M hM k r 1 := by
    linarith [(abs_sub_lt_iff.mp (he.trans_lt hkerr)).2]
  rw [zero_field_eq_connectedWeight]
  exact (div_pos_iff_of_pos_right hP).mp hratio

end PerronWright.ConnectedTypeLaw
