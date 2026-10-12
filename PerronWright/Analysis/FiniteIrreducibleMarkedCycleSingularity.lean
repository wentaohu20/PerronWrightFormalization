import PerronWright.Analysis.FiniteIrreducibleMarkedPathResidue
import PerronWright.Analysis.AnalyticVerticalPrimitive

/-!
# The marked-cycle logarithmic derivative at the finite irreducible fold

This module extracts the scalar singularity directly from the marked
path kernel.  The diagonal pairing of `(I-L)⁻¹K` with the vertical profile
velocity has residue `-1`; its remaining part is jointly analytic.  A
coefficientwise analytic primitive then supplies the normalized regular
primitive, without a Fredholm determinant or logarithm interface.
-/

open MeasureTheory PerronWright
open scoped Topology

noncomputable section

namespace PerronWright.FiniteIrreducibleMarkedCycleSingularity

namespace MPR

export PerronWright.FiniteIrreducibleMarkedPathResolvent
  (profile profile_analytic scalarIntegralCLM scalarIntegralCLM_apply
   residueKernel residueKernel_analytic
   pathRemainderKernel pathRemainderKernel_analytic
   pathResolventKernel pathResolventKernel_fixed_residue_split)

end MPR

namespace MResidue

export PerronWright.FiniteIrreducibleMarkedPathResidue
  (profileVertical profileVertical_analytic
   residueDiagonalPairing residueDiagonalPairing_analytic
   residue_diagonal_vertical_eq_neg_one)

end MResidue

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

private def verticalDirection : C(S, ℂ) × ℂ := (0, 1)

/-- Vertical velocity of the actual joint tree profile. -/
def jointProfileVertical (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) : C(S, ℂ) :=
  (fderiv ℂ (MPR.profile M hM) q) verticalDirection

theorem jointProfileVertical_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (jointProfileVertical M hM) (0, 0) := by
  have hf : AnalyticAt ℂ (fderiv ℂ (MPR.profile M hM)) (0, 0) :=
    (MPR.profile_analytic M hM).fderiv
  exact ((ContinuousLinearMap.apply ℂ _ verticalDirection).analyticAt
    (fderiv ℂ (MPR.profile M hM) (0, 0))).comp_of_eq hf rfl

@[simp] theorem jointProfileVertical_axis (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (g : C(S, ℂ)) :
    jointProfileVertical M hM (g, 0) = MResidue.profileVertical M hM g :=
  rfl

private def diagonalMap : C(S, S × S) :=
  ⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩

private def diagonalRestrictionCLM : C(S × S, ℂ) →L[ℂ] C(S, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ diagonalMap

omit [Fintype S] [DecidableEq S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
@[simp] private theorem diagonalRestrictionCLM_apply
    (k : C(S × S, ℂ)) (x : S) :
    diagonalRestrictionCLM k x = k (x, x) :=
  rfl

private def diagonalPairing (M : FiniteIrreducibleModel S)
    (k : C(S × S, ℂ)) (v : C(S, ℂ)) : ℂ :=
  MPR.scalarIntegralCLM M (diagonalRestrictionCLM k * v)

private theorem diagonalPairing_add_left (M : FiniteIrreducibleModel S)
    (k l : C(S × S, ℂ)) (v : C(S, ℂ)) :
    diagonalPairing M (k + l) v =
      diagonalPairing M k v + diagonalPairing M l v := by
  unfold diagonalPairing
  simp only [map_add, add_mul]

private theorem diagonalPairing_smul_left (M : FiniteIrreducibleModel S)
    (c : ℂ) (k : C(S × S, ℂ)) (v : C(S, ℂ)) :
    diagonalPairing M (c • k) v = c * diagonalPairing M k v := by
  unfold diagonalPairing
  have hmul : (c • diagonalRestrictionCLM k) * v =
      c • (diagonalRestrictionCLM k * v) := by
    ext x
    simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul]
    ring
  rw [map_smul, hmul, map_smul]
  simp only [smul_eq_mul]

private theorem diagonalPairing_analytic
    (M : FiniteIrreducibleModel S) {k : C(S, ℂ) × ℂ → C(S × S, ℂ)}
    {v : C(S, ℂ) × ℂ → C(S, ℂ)}
    (hk : AnalyticAt ℂ k (0, 0)) (hv : AnalyticAt ℂ v (0, 0)) :
    AnalyticAt ℂ (fun q => diagonalPairing M (k q) (v q)) (0, 0) := by
  have hdiag : AnalyticAt ℂ (fun q => diagonalRestrictionCLM (k q)) (0, 0) :=
    (diagonalRestrictionCLM (S := S)).analyticAt _ |>.comp hk
  exact (MPR.scalarIntegralCLM M).analyticAt _ |>.comp (hdiag.mul hv)

/-- The pole residue paired with the joint vertical profile velocity. -/
def jointResiduePairing (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) : ℂ :=
  diagonalPairing M (MPR.residueKernel M hM q.1)
    (jointProfileVertical M hM q)

theorem jointResiduePairing_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (jointResiduePairing M hM) (0, 0) := by
  have hk : AnalyticAt ℂ
      (fun q : C(S, ℂ) × ℂ => MPR.residueKernel M hM q.1) (0, 0) :=
    (MPR.residueKernel_analytic M hM).comp_of_eq analyticAt_fst rfl
  exact diagonalPairing_analytic M hk (jointProfileVertical_analytic M hM)

@[simp] theorem jointResiduePairing_axis (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (g : C(S, ℂ)) :
    jointResiduePairing M hM (g, 0) =
      MResidue.residueDiagonalPairing M hM g :=
  rfl

private def residueCorrection (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) : ℂ :=
  jointResiduePairing M hM q -
    MResidue.residueDiagonalPairing M hM q.1

private theorem residueCorrection_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (residueCorrection M hM) (0, 0) := by
  have haxis : AnalyticAt ℂ
      (fun q : C(S, ℂ) × ℂ =>
        MResidue.residueDiagonalPairing M hM q.1) (0, 0) :=
    (MResidue.residueDiagonalPairing_analytic M hM).comp_of_eq
      analyticAt_fst rfl
  exact (jointResiduePairing_analytic M hM).sub haxis

private theorem residueCorrection_axis (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (g : C(S, ℂ)) :
    residueCorrection M hM (g, 0) = 0 := by
  simp [residueCorrection]

private def regularPairing (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) : ℂ :=
  diagonalPairing M (MPR.pathRemainderKernel M hM q)
    (jointProfileVertical M hM q)

private theorem regularPairing_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (regularPairing M hM) (0, 0) :=
  diagonalPairing_analytic M (MPR.pathRemainderKernel_analytic M hM)
    (jointProfileVertical_analytic M hM)

/-- Raw diagonal pairing supplied by the marked-path resolvent.  Its Neumann
expansion begins with path length one; the length-one and length-two analytic
terms must still be removed before identifying the simple-cycle derivative. -/
def cycleResolventDerivative (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) : ℂ :=
  diagonalPairing M (MPR.pathResolventKernel M hM q)
    (jointProfileVertical M hM q)

private theorem cycleResolventDerivative_kernel_split
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      cycleResolventDerivative M hM q =
        q.2⁻¹ * jointResiduePairing M hM q + regularPairing M hM q := by
  filter_upwards [MPR.pathResolventKernel_fixed_residue_split M hM] with q hq
  intro hX
  rw [cycleResolventDerivative, hq hX,
    diagonalPairing_add_left, diagonalPairing_smul_left]
  rfl

/-- The raw marked-path pairing is `-1/X` plus a jointly analytic scalar
germ.  The coefficient `-1` is the exact Perron residue.  Removing the first
two finite path terms changes only the analytic regular part. -/
theorem exists_cycleResolventDerivative_regularPart
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ A : C(S, ℂ) × ℂ → ℂ,
      AnalyticAt ℂ A (0, 0) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
        cycleResolventDerivative M hM q = -q.2⁻¹ + A q := by
  have hzero : ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      residueCorrection M hM (g, 0) = 0 :=
    Filter.Eventually.of_forall (residueCorrection_axis M hM)
  obtain ⟨Q, hQa, hQfactor⟩ :=
    AnalyticVerticalDivision.analytic_vertical_division_smul
      (residueCorrection_analytic M hM) hzero
  let A : C(S, ℂ) × ℂ → ℂ := fun q => Q q + regularPairing M hM q
  refine ⟨A, hQa.add (regularPairing_analytic M hM), ?_⟩
  have hresidue : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      MResidue.residueDiagonalPairing M hM q.1 = -1 :=
    (show Filter.Tendsto (fun q : C(S, ℂ) × ℂ => q.1)
        (nhds (0, 0)) (nhds 0) from continuousAt_fst.tendsto).eventually
      (MResidue.residue_diagonal_vertical_eq_neg_one M hM)
  filter_upwards [cycleResolventDerivative_kernel_split M hM,
    hQfactor, hresidue] with q hsplit hfactor hresidue
  intro hX
  have hjoint : jointResiduePairing M hM q = -1 + q.2 * Q q := by
    calc
      jointResiduePairing M hM q =
          residueCorrection M hM q +
            MResidue.residueDiagonalPairing M hM q.1 := by
        unfold residueCorrection
        abel
      _ = q.2 • Q q + (-1) := by rw [hfactor, hresidue]
      _ = -1 + q.2 * Q q := by simp only [smul_eq_mul, add_comm]
  rw [hsplit hX, hjoint]
  change q.2⁻¹ * (-1 + q.2 * Q q) + regularPairing M hM q =
    -q.2⁻¹ + (Q q + regularPairing M hM q)
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hX]
  ring

/-- The analytic regular part has a normalized jointly analytic primitive in
the fold coordinate. -/
theorem exists_cycleResolvent_regularPrimitive
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ A H : C(S, ℂ) × ℂ → ℂ,
      AnalyticAt ℂ A (0, 0) ∧
      AnalyticAt ℂ H (0, 0) ∧
      (∀ g : C(S, ℂ), H (g, 0) = 0) ∧
      (∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
        cycleResolventDerivative M hM q = -q.2⁻¹ + A q) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        (fderiv ℂ H q) (0, 1) = A q := by
  obtain ⟨A, hAa, hsplit⟩ :=
    exists_cycleResolventDerivative_regularPart M hM
  obtain ⟨H, hHa, hHaxis, hHderiv⟩ :=
    AnalyticVerticalPrimitive.analytic_vertical_primitive hAa
  exact ⟨A, H, hAa, hHa, hHaxis, hsplit, hHderiv⟩

end PerronWright.FiniteIrreducibleMarkedCycleSingularity


