import PerronWright.Model.CountableFinitePerronBridge
import PerronWright.Model.CountablePerronLawApproximation
import PerronWright.Probability.FiniteIrreducibleConnectedTypeLaw
import PerronWright.Probability.FiniteIrreducibleTypedGraphLaw

/-! # Literal countable retained graph hazards and canonical mark laws

The finite critical model has exactly the paper's retained edge hazards.
Its canonical mark, embedded into the original countable type space, is
exactly the proved finite-law Perron measure. These are exact identities;
no local asymptotic or process convergence is an assumption.
-/

open MeasureTheory
open scoped BigOperators Classical
noncomputable section

namespace PerronWright.CountableKernel

theorem finiteCriticalModel_perronMeasure_map (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (hpos : ∀ a ∈ s, 0 < w a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (hF : (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).IsCritical) :
    (FiniteIrreducibleConnectedTypeLaw.perronMeasure
      (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo) hF).map
        (fun a : s ↦ (a : ℕ)) = M.finitePerronLaw w hw hs s hzero hlower hlo := by
  rw [FiniteIrreducibleConnectedTypeLaw.perronMeasure,
    Measure.map_finset_sum' measurable_subtype_coe.aemeasurable]
  simp_rw [Measure.map_smul, Measure.map_dirac' measurable_subtype_coe,
    M.finiteCriticalModel_perronFunction]
  change (∑ a : s, ENNReal.ofReal
    (w a * M.finitePerronFunction w hw hs s hzero hlower hlo a) • Measure.dirac (a : ℕ)) = _
  ext A hA
  rw [Measure.finsetSum_apply, finitePerronLaw, Measure.sum_apply _ hA]
  rw [Finset.sum_coe_sort s (fun a : ℕ ↦
    (ENNReal.ofReal (w a * M.finitePerronFunction w hw hs s hzero hlower hlo a) •
      Measure.dirac a) A)]
  exact (tsum_eq_sum (fun a ha ↦ by simp [hzero a ha])).symm

def retainedPairKernel (M : CountableKernel) {n : ℕ} (x : Fin n → ℕ) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j ↦ M.kernel (x i) (x j), fun i j ↦ M.symmetric (x i) (x j)⟩

@[simp] theorem retainedPairKernel_mk (M : CountableKernel) {n : ℕ}
    (x : Fin n → ℕ) (i j : Fin n) : retainedPairKernel M x s(i,j) = M.kernel (x i) (x j) := rfl

theorem finiteCriticalModel_pairKernel (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (hpos : ∀ a ∈ s, 0 < w a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    {n : ℕ} (x : Fin n → s) (e : Sym2 (Fin n)) :
    FiniteIrreducibleTypedGraphLaw.pairKernel
      (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo) x e =
      retainedPairKernel M (fun i ↦ (x i : ℕ)) e / M.weightedSpectralRadius w hw hs := by
  induction e using Sym2.inductionOn with
  | _ i j => rfl

/-- The exact paper hazard, also at n=0 under the common total division
convention. The retained spectral normalization is not an extra premise. -/
theorem finiteCriticalModel_hazard (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (hpos : ∀ a ∈ s, 0 < w a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    {n : ℕ} (x : Fin n → s) (t : ℝ) (e : AnnealedGraph.Edge n) :
    FiniteIrreducibleTypedGraphLaw.hazard
      (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo) t x e =
      t * retainedPairKernel M (fun i ↦ (x i : ℕ)) e.val /
        ((n : ℝ) * M.weightedSpectralRadius w hw hs) := by
  rw [FiniteIrreducibleTypedGraphLaw.hazard, M.finiteCriticalModel_pairKernel]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem finiteCriticalModel_law_real_edge (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (hpos : ∀ a ∈ s, 0 < w a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    {n : ℕ} (x : Fin n → s) (t : ℝ) (ht : 0 ≤ t) (e : AnnealedGraph.Edge n) :
    (FiniteIrreducibleTypedGraphLaw.law
      (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo) t ht x).real
      {G | e.val ∈ G.edgeSet} =
      1 - Real.exp (-(t * retainedPairKernel M (fun i ↦ (x i : ℕ)) e.val /
        ((n : ℝ) * M.weightedSpectralRadius w hw hs))) := by
  rw [FiniteIrreducibleTypedGraphLaw.law_real_edge]
  change 1 - Real.exp (-FiniteIrreducibleTypedGraphLaw.hazard
    (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo) t x e) = _
  rw [M.finiteCriticalModel_hazard]

end PerronWright.CountableKernel
