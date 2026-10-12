import PerronWright.Analysis.FiniteIrreducibleComplexL2Bridge
import PerronWright.Analysis.FiniteIrreducibleComplexPeriodicity

/-!
# Canonical discrete realization without ambient topology assumptions

A finite type is embedded in the real line by its finite enumeration.
The induced metric and its Borel sigma algebra are constructed here, so
the BJR realization and B1 conclusions require only the literal finite
model and its actual matrix spectral criticality.
-/

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]

@[instance_reducible] def discreteMetricSpace (S : Type*) [Fintype S] : MetricSpace S :=
  MetricSpace.induced (fun a ↦ ((Fintype.equivFin S a).val : ℝ))
    (fun _a _b h ↦ (Fintype.equivFin S).injective (Fin.ext (Nat.cast_injective h))) inferInstance

def discreteBJRModel (M : FiniteIrreducibleModel S) :
    letI : MetricSpace S := discreteMetricSpace S
    letI : MeasurableSpace S := borel S
    letI : BorelSpace S := ⟨rfl⟩
    CompactBJRModel S := by
  letI : MetricSpace S := discreteMetricSpace S
  letI : MeasurableSpace S := borel S
  letI : BorelSpace S := ⟨rfl⟩
  exact M.bjrModel

theorem discreteBJRModel_b1 (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    letI : MetricSpace S := discreteMetricSpace S
    letI : MeasurableSpace S := borel S
    letI : BorelSpace S := ⟨rfl⟩
    M.discreteBJRModel.B1 := by
  let : MetricSpace S := discreteMetricSpace S
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  exact M.bjrModel_b1 hcrit

theorem discreteBJRModel_not_b2_of_negative_unit_eigenvalue (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (hneg : Module.End.HasEigenvalue M.operator.toLinearMap (-1)) :
    letI : MetricSpace S := discreteMetricSpace S
    letI : MeasurableSpace S := borel S
    letI : BorelSpace S := ⟨rfl⟩
    ¬ M.discreteBJRModel.B2 := by
  let : MetricSpace S := discreteMetricSpace S
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  exact M.bjrModel_not_b2_of_negative_unit_eigenvalue hcrit hneg

end PerronWright.FiniteIrreducibleModel
