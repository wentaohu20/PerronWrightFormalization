import PerronWright.Analysis.ScalarFieldResponse
import PerronWright.Enumeration.FieldAnalytic

open MeasureTheory
noncomputable section

namespace PerronWright.ScalarFieldResponse

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem scalarFieldComplex_ofReal (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t) :
    scalarFieldComplex M (t : ℂ) =
      CompactBJRModel.complexifyField (M.scalarField t) := by
  ext x
  simp only [scalarFieldComplex, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.one_apply,
    mul_one, CompactBJRModel.complexifyField_apply,
    CompactBJRModel.scalarField_apply, TreeCritical.degree_apply]
  rw [← Complex.ofReal_log ht.le]
  push_cast
  rw [show M.degreeFunction x = M.kernel.degree M.mu x from
    M.kernel.degreeMap_apply M.mu x]

theorem connectedWeight_scalarFieldComplex (M : CompactBJRModel S)
    (t : ℝ) (ht : 0 < t) (k r : ℕ) :
    (M.connectedWeight t k r : ℂ) =
      (t : ℂ) ^ ((r : ℤ) - 1) *
        M.complexFieldConnectedWeight (scalarFieldComplex M (t : ℂ)) k r := by
  rw [scalarFieldComplex_ofReal M t ht,
    M.complexFieldConnectedWeight_complexifyField]
  exact_mod_cast M.connectedWeight_scalarField t ht k r

end PerronWright.ScalarFieldResponse
