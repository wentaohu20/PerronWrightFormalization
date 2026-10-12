import PerronWright.Analysis.FiniteIrreducibleComplexL2Bridge
import PerronWright.Model.FiniteIrreducibleBipartite
import PerronWright.Analysis.PerronSpectrum

/-!
# The adapter does not silently impose primitivity

A negative unit eigenvalue of the literal finite matrix operator implies
that the constructed discrete BJR data fail B2.  The concrete critical
two-type bipartite example therefore has a genuine B1 witness but no B2.
-/

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem bjrModel_not_b2_of_negative_unit_eigenvalue (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (hneg : Module.End.HasEigenvalue M.operator.toLinearMap (-1)) :
    ¬ M.bjrModel.B2 := by
  intro hb2
  have hM : M.bjrModel.IsRegularCritical := ⟨M.bjrModel_b1 hcrit, hb2⟩
  apply PerronWright.l2_not_hasEigenvalue_neg_one M.bjrModel hM (M.b1Witness hcrit)
  obtain ⟨v, hv, hvne⟩ := hneg.exists_hasEigenvector
  have heq := Module.End.mem_eigenspace_iff.mp hv
  change M.operator v = (-1 : ℝ) • v at heq
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := M.l2Equiv v)
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    change M.l2Operator (M.l2Equiv v) = (-1 : ℝ) • M.l2Equiv v
    rw [M.l2Operator_apply, M.l2Equiv.symm_apply_apply, heq, map_smul]
  · intro hz
    exact hvne (M.l2Equiv.injective (hz.trans M.l2Equiv.map_zero.symm))

theorem bipartite_bjrModel_not_b2
    [MetricSpace (Fin 2)] [DiscreteTopology (Fin 2)]
    [MeasurableSpace (Fin 2)] [BorelSpace (Fin 2)] : ¬ bipartite.bjrModel.B2 :=
  bipartite.bjrModel_not_b2_of_negative_unit_eigenvalue bipartite_critical
    bipartite_has_negative_unit_eigenvalue

end PerronWright.FiniteIrreducibleModel
