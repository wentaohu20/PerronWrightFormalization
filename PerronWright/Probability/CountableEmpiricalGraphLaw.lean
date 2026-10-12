import PerronWright.Probability.CountableEmpiricalFiniteApproximation
import PerronWright.Probability.FiniteIrreducibleComponentProcess
import PerronWright.Probability.CriticalParameterDrift

/-! # Actual empirical countable graph laws and exact finite-model bridges

The source vertices have their literal natural-number types. Spectral
normalization uses the actual empirical spectral root, not a supplied
positive-root or graph-law identification premise. The unrenormalized
law is exactly a normalized law at the proved effective parameter.
No graph-limit conclusion is asserted by these finite-size identities.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright.CountableKernel

theorem retainedPairKernel_nonneg (M : CountableKernel) {n : ℕ}
    (x : Fin n → ℕ) (e : Sym2 (Fin n)) : 0 ≤ retainedPairKernel M x e := by
  induction e using Sym2.inductionOn with
  | _ i j => exact M.nonneg (x i) (x j)

def empiricalNormalizedHazards (M : CountableKernel) (level : ℕ → ℕ)
    (lambda : ℝ) (n : ℕ) (e : AnnealedGraph.Edge (n + 1)) : ℝ :=
  CriticalScaling.time lambda (n + 1) *
    M.retainedPairKernel (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) e.val /
      (((n + 1 : ℕ) : ℝ) * M.empiricalSpectralRadius level n)

theorem empiricalNormalizedHazards_nonneg (M : CountableKernel) (level : ℕ → ℕ)
    (lambda : ℝ) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (n : ℕ) (e : AnnealedGraph.Edge (n + 1)) :
    0 ≤ M.empiricalNormalizedHazards level lambda n e :=
  div_nonneg (mul_nonneg (CriticalScaling.time_nonneg lambda (n + 1))
    (M.retainedPairKernel_nonneg _ e.val)) (mul_nonneg (Nat.cast_nonneg _)
      (M.empiricalOperator_exists_nonnegative_perron level n hlower hlo).1.le)

/-- The literal empirical countable graph measure, including the actual
finite independent edge law rather than only its one-edge marginals. -/
def empiricalNormalizedGraphLaw (M : CountableKernel) (level : ℕ → ℕ)
    (lambda : ℝ) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (n : ℕ) : Measure (SimpleGraph (Fin (n + 1))) :=
  FixedTypeGraph.law (M.empiricalNormalizedHazards level lambda n)
    (M.empiricalNormalizedHazards_nonneg level lambda hlower hlo n)

instance empiricalNormalizedGraphLaw_isProbability (M : CountableKernel) (level : ℕ → ℕ)
    (lambda : ℝ) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (n : ℕ) : IsProbabilityMeasure (M.empiricalNormalizedGraphLaw level lambda hlower hlo n) := by
  unfold empiricalNormalizedGraphLaw
  infer_instance

theorem empiricalFiniteModel_graphLaw_eq (M : CountableKernel) (level : ℕ → ℕ)
    (hpos : ∀ n a, a ∈ Finset.range (level (n + 1) + 1) → 0 < M.empiricalWeights level n a)
    (lambda : ℝ) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (n : ℕ) :
    FiniteIrreducibleComponentProcess.graphLaw (M.empiricalFiniteModel level hpos hlower hlo n)
      lambda (n + 1) (M.empiricalVertexTypes level n) =
      M.empiricalNormalizedGraphLaw level lambda hlower hlo n := by
  unfold FiniteIrreducibleComponentProcess.graphLaw FiniteIrreducibleTypedGraphLaw.law
    empiricalNormalizedGraphLaw
  congr 1
  funext e
  exact M.finiteCriticalModel_hazard _ _ _ _ _ (hpos n) hlower hlo _ _ e

def empiricalUnnormalizedHazards (M : CountableKernel) (level : ℕ → ℕ)
    (lambda : ℝ) (n : ℕ) (e : AnnealedGraph.Edge (n + 1)) : ℝ :=
  CriticalScaling.time lambda (n + 1) *
    M.retainedPairKernel (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) e.val /
      ((n + 1 : ℕ) : ℝ)

theorem empiricalUnnormalizedHazards_nonneg (M : CountableKernel) (level : ℕ → ℕ)
    (lambda : ℝ) (n : ℕ) (e : AnnealedGraph.Edge (n + 1)) :
    0 ≤ M.empiricalUnnormalizedHazards level lambda n e :=
  div_nonneg (mul_nonneg (CriticalScaling.time_nonneg lambda (n + 1))
    (M.retainedPairKernel_nonneg _ e.val)) (Nat.cast_nonneg _)

def empiricalUnnormalizedGraphLaw (M : CountableKernel) (level : ℕ → ℕ)
    (lambda : ℝ) (n : ℕ) : Measure (SimpleGraph (Fin (n + 1))) :=
  FixedTypeGraph.law (M.empiricalUnnormalizedHazards level lambda n)
    (M.empiricalUnnormalizedHazards_nonneg level lambda n)

instance empiricalUnnormalizedGraphLaw_isProbability (M : CountableKernel) (level : ℕ → ℕ)
    (lambda : ℝ) (n : ℕ) : IsProbabilityMeasure (M.empiricalUnnormalizedGraphLaw level lambda n) := by
  unfold empiricalUnnormalizedGraphLaw
  infer_instance

/-- Exact law equality at the actual shifted parameter. Positivity of
the empirical spectral root is proved internally from the paper kernel. -/
theorem empiricalUnnormalizedGraphLaw_eq_normalized (M : CountableKernel) (level : ℕ → ℕ)
    (lambda : ℝ) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (n : ℕ) :
    M.empiricalUnnormalizedGraphLaw level lambda n =
      M.empiricalNormalizedGraphLaw level
        (CriticalParameterDrift.effectiveParameter lambda
          (fun m ↦ M.empiricalSpectralRadius level (m - 1)) (n + 1)) hlower hlo n := by
  unfold empiricalUnnormalizedGraphLaw empiricalNormalizedGraphLaw
  congr 1
  funext e
  have hσ := (M.empiricalOperator_exists_nonnegative_perron level n hlower hlo).1
  have he := CriticalParameterDrift.edge_hazard_eq (Nat.succ_pos n) lambda
    (fun m ↦ M.empiricalSpectralRadius level (m - 1)) (by simpa using hσ)
    (M.retainedPairKernel (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) e.val)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel,
    empiricalUnnormalizedHazards, empiricalNormalizedHazards] using he

end PerronWright.CountableKernel
