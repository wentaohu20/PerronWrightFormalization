import PerronWright.Enumeration.CubicActualProfileIntegral
import PerronWright.Enumeration.FixedSurplusCubicNoncubicSplit
import PerronWright.Enumeration.PositiveSurplusWrightConstant

/-!
# The actual fixed-degree cubic coefficient in kernel coordinates

This file combines the exact presentation fibre regrouping with the complex
profile integral of a reconstructed subdivision.  It identifies the cubic
part of the genuine finite-core coefficient, on a monomial profile, with a
finite sum over labelled cubic kernels and admissible length profiles.  The
normalization is the same inverse global multiplicity used by the analytic
resolvent amplitude.
-/

open MeasureTheory PerronWright
open scoped Classical BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem sum_ite_eq_sum_subtype
    {A R : Type*} [Fintype A] [DecidableEq A] [AddCommMonoid R]
    (p : A → Prop) [DecidablePred p] (f : A → R) :
    (∑ a : A, if p a then f a else 0) =
      ∑ a : {a // p a}, f a.1 := by
  classical
  let F : A → R := fun a ↦ if p a then f a else 0
  calc
    (∑ a : A, if p a then f a else 0) = ∑ a : A, F a := rfl
    _ = ∑ a ∈ (Finset.univ.filter p), F a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : p a <;> simp [F, ha]
    _ = ∑ a : {a // p a}, F a.1 := by
      exact Finset.sum_subtype (Finset.univ.filter p) (by simp) F
    _ = ∑ a : {a // p a}, f a.1 := by
      apply Fintype.sum_congr
      intro a
      simp [F, a.2]

private def admissibleCubicSubtypeEquiv (k ell : ℕ) :
    {H : {H : SimpleGraph (Fin k) //
      IsAdmissibleAttachmentCore k ell H} //
      IsCubicAdmissibleAttachmentCore k ell H.1} ≃
      CubicAdmissibleAttachmentCore k ell where
  toFun H := ⟨H.1.1, H.2⟩
  invFun G := ⟨⟨G.1, G.2.1⟩, G.2⟩
  left_inv H := by
    rcases H with ⟨⟨H, hA⟩, hC⟩
    rfl
  right_inv G := by
    rcases G with ⟨G, hC⟩
    rfl

private theorem finset_univ_eq_of_fintype
    {A : Type*} (i₁ i₂ : Fintype A) :
    @Finset.univ A i₁ = @Finset.univ A i₂ := by
  ext a
  simp

/-- The actual finite admissible-profile coefficient in the cubic kernel
coordinates, with the exact global presentation normalization. -/
def positiveSurplusCubicAdmissibleProfileCoefficient
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (ell d : ℕ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      letI := cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
      ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
        cubicLengthProfileComplexKernelIntegral M tau K L

/-- At the core size, the monomial profile turns the filtered cubic
fixed-core coefficient into the literal sum over cubic admissible cores. -/
theorem fixedSurplusCubicCoreProfileCoeff_X_mul_C_eq_coreWeightSum
    (M : CompactBJRModel S) (tau : C(S, ℂ)) (ell k : ℕ) :
    fixedSurplusCubicCoreProfileCoeff M
        (PowerSeries.X * PowerSeries.C tau) ell k k =
      ∑ G : CubicAdmissibleAttachmentCore k ell,
        finiteComplexGraphWeight M tau G.1 := by
  classical
  unfold fixedSurplusCubicCoreProfileCoeff
  simp_rw [fixedCoreProfileCompositionSeries_X_mul_C_coeff M tau]
  rw [sum_ite_eq_sum_subtype
    (p := fun H : {H : SimpleGraph (Fin k) //
      IsAdmissibleAttachmentCore k ell H} ↦
        IsCubicAdmissibleAttachmentCore k ell H.1)
    (f := fun H ↦ finiteComplexGraphWeight M tau H.1)]
  exact Fintype.sum_equiv (admissibleCubicSubtypeEquiv k ell)
    (fun H : {H : {H : SimpleGraph (Fin k) //
      IsAdmissibleAttachmentCore k ell H} //
      IsCubicAdmissibleAttachmentCore k ell H.1} ↦
        finiteComplexGraphWeight M tau H.1.1)
    (fun G : CubicAdmissibleAttachmentCore k ell ↦
      finiteComplexGraphWeight M tau G.1)
    (fun _ ↦ rfl)

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
private theorem rootedTreeTailAt_X_mul_C
    (tau : C(S, ℂ)) (x : S) :
    rootedTreeTailAt (PowerSeries.X * PowerSeries.C tau) x =
      PowerSeries.C (tau x) := by
  ext n
  rw [rootedTreeTailAt_coeff]
  simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C]
  by_cases hn : n = 0 <;> simp [hn]

/-- A monomial vertex profile has no fixed-core coefficient away from the
literal number of core vertices. -/
theorem fixedCoreProfileCompositionSeries_X_mul_C_coeff_eq_zero_of_ne
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {q k : ℕ} (H : SimpleGraph (Fin q)) (hk : k ≠ q) :
    PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M
          (PowerSeries.X * PowerSeries.C tau) H) = 0 := by
  by_cases hlt : k < q
  · exact fixedCoreProfileCompositionSeries_coeff_eq_zero_of_lt
      M (PowerSeries.X * PowerSeries.C tau) H hlt
  · have hqk : q < k := by omega
    let n := k - q
    have hn : 0 < n := by omega
    have hkn : k = n + q := by omega
    rw [hkn, fixedCoreProfileCompositionSeries_coeff]
    apply integral_eq_zero_of_ae
    filter_upwards [] with roots
    simp_rw [rootedTreeTailAt_X_mul_C]
    rw [← map_prod]
    simp only [PowerSeries.coeff_C, if_neg hn.ne', mul_zero,
      Pi.zero_apply]

/-- Antidiagonal reindexing of the cubic part of the fixed-surplus profile
coefficient by the core size. -/
theorem cubicFixedSurplusProfileCompositionCoeff_eq_sum_range
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell k : ℕ) :
    cubicFixedSurplusProfileCompositionCoeff M T ell k =
      ∑ q ∈ Finset.range (k + 1),
        fixedSurplusCubicCoreProfileCoeff M T ell q k /
          (q.factorial : ℂ) := by
  unfold cubicFixedSurplusProfileCompositionCoeff
  let f : ℕ × ℕ → ℂ := fun p ↦
    fixedSurplusCubicCoreProfileCoeff M T ell p.1 k /
      (p.1.factorial : ℂ)
  change (∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k}, f p.1) = _
  rw [Finset.sum_coe_sort]
  change (∑ p ∈ coreOffSizePairs k, f p) = _
  rw [coreOffSizePairs, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- On a monomial profile the antidiagonal cubic composition has only the
core-size term. -/
theorem cubicFixedSurplusProfileCompositionCoeff_X_mul_C
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (ell k : ℕ) :
    cubicFixedSurplusProfileCompositionCoeff M
        (PowerSeries.X * PowerSeries.C tau) ell k =
      fixedSurplusCubicCoreProfileCoeff M
          (PowerSeries.X * PowerSeries.C tau) ell k k /
        (k.factorial : ℂ) := by
  rw [cubicFixedSurplusProfileCompositionCoeff_eq_sum_range]
  apply Finset.sum_eq_single k
  · intro q hq hqk
    have hzero : fixedSurplusCubicCoreProfileCoeff M
        (PowerSeries.X * PowerSeries.C tau) ell q k = 0 := by
      unfold fixedSurplusCubicCoreProfileCoeff
      apply Finset.sum_eq_zero
      intro H _
      by_cases hH : IsCubicAdmissibleAttachmentCore q ell H.1
      · simp only [hH, if_true]
        exact fixedCoreProfileCompositionSeries_X_mul_C_coeff_eq_zero_of_ne
          M tau H.1 hqk.symm
      · simp [hH]
    rw [hzero, zero_div]
  · intro hknot
    exact False.elim (hknot (Finset.mem_range.mpr (by omega)))

/-- Exact presentation regrouping of the actual cubic-core weight into
admissible length profiles. -/
theorem sum_cubicAdmissibleCore_complexWeight_eq_lengthProfiles
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k ell : ℕ} (hell : 0 < ell) (s₀ : S) :
    (∑ G : CubicAdmissibleAttachmentCore k ell,
        finiteComplexGraphWeight M tau G.1) =
      (k.factorial : ℂ) /
          (((2 * ell).factorial : ℂ) * ((3 * ell).factorial : ℂ)) *
        letI := labelledConnectedCubicKernelFintype ell
        ∑ K : LabelledConnectedCubicKernel ell,
          (((2 ^ Fintype.card (CubicKernelLoopEdge K.graph) : ℕ) : ℂ)⁻¹ *
            letI := cubicKernelLengthProfileFintype k ell K.graph
            ∑ L : CubicKernelLengthProfile k ell K.graph,
              cubicLengthProfileComplexKernelIntegral M tau K L) := by
  let _ : Fintype (LabelledConnectedCubicKernel ell) :=
    labelledConnectedCubicKernelFintype ell
  let _ : ∀ K : LabelledConnectedCubicKernel ell,
      Fintype (CubicKernelLengthProfile k ell K.graph) :=
    fun K ↦ cubicKernelLengthProfileFintype k ell K.graph
  let _ : ∀ K : LabelledConnectedCubicKernel ell,
      Fintype (CubicKernelSubdivisionDatum k ell K.graph) :=
    fun K ↦ cubicKernelSubdivisionDatumFintype k ell K.graph
  rw [← sum_cubicKernelPresentations_invMultiplicity_graphInvariant
    (k := k) (ell := ell) hell
      (fun G ↦ finiteComplexGraphWeight M tau G)]
  rw [finset_univ_eq_of_fintype
    (cubicKernelPresentationFintype (k := k) (ell := ell) hell)
    (inferInstance : Fintype (CubicKernelPresentation k ell))]
  calc
    (∑ P : CubicKernelPresentation k ell,
        (P.globalMultiplicity : ℂ)⁻¹ *
          finiteComplexGraphWeight M tau P.2.reconstructedGraph) =
        ∑ P : CubicKernelPresentation k ell,
          (P.globalMultiplicity : ℂ)⁻¹ *
            cubicLengthProfileComplexKernelIntegral M tau P.1 P.2.profile := by
      apply Fintype.sum_congr
      intro P
      rw [finiteComplexGraphWeight_reconstructedGraph_eq_cubicLengthProfileIntegral
        M tau P.1 P.2 s₀]
    _ = (k.factorial : ℂ) /
          (((2 * ell).factorial : ℂ) * ((3 * ell).factorial : ℂ)) *
        ∑ K : LabelledConnectedCubicKernel ell,
          (((2 ^ Fintype.card (CubicKernelLoopEdge K.graph) : ℕ) : ℂ)⁻¹ *
            ∑ L : CubicKernelLengthProfile k ell K.graph,
              cubicLengthProfileComplexKernelIntegral M tau K L) := by
      simpa only using sum_cubicKernelPresentations_invMultiplicity_profile
        (k := k) (ell := ell)
        (fun K L ↦ cubicLengthProfileComplexKernelIntegral M tau K L)

/-- After labelled-EGF division, the exact cubic core sum has precisely the
inverse multiplicity used in the analytic cubic amplitude. -/
theorem fixedSurplusCubicCoreProfileCoeff_div_factorial_eq_admissibleProfile
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell d : ℕ} (hell : 0 < ell) (s₀ : S) :
    fixedSurplusCubicCoreProfileCoeff M
        (PowerSeries.X * PowerSeries.C tau) ell
        (2 * ell + d) (2 * ell + d) /
        ((2 * ell + d).factorial : ℂ) =
      positiveSurplusCubicAdmissibleProfileCoefficient M tau ell d := by
  rw [fixedSurplusCubicCoreProfileCoeff_X_mul_C_eq_coreWeightSum]
  rw [sum_cubicAdmissibleCore_complexWeight_eq_lengthProfiles
    M tau hell s₀]
  unfold positiveSurplusCubicAdmissibleProfileCoefficient
  let _ : Fintype (LabelledConnectedCubicKernel ell) :=
    labelledConnectedCubicKernelFintype ell
  let _ : ∀ K : LabelledConnectedCubicKernel ell,
      Fintype (CubicKernelLengthProfile (2 * ell + d) ell K.graph) :=
    fun K ↦ cubicKernelLengthProfileFintype (2 * ell + d) ell K.graph
  have hkfac : (((2 * ell + d).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * ell + d)
  rw [mul_div_assoc]
  field_simp [hkfac]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro K _
  unfold labelledCubicKernelInverseMultiplicity
    labelledCubicKernelGlobalMultiplicity
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- The genuine cubic part of the fixed-surplus composition coefficient,
specialized to a monomial profile, is the exact admissible labelled-kernel
profile coefficient. -/
theorem cubicFixedSurplusProfileCompositionCoeff_X_mul_C_eq_admissibleProfile
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell d : ℕ} (hell : 0 < ell) (s₀ : S) :
    cubicFixedSurplusProfileCompositionCoeff M
        (PowerSeries.X * PowerSeries.C tau) ell (2 * ell + d) =
      positiveSurplusCubicAdmissibleProfileCoefficient M tau ell d := by
  rw [cubicFixedSurplusProfileCompositionCoeff_X_mul_C]
  exact fixedSurplusCubicCoreProfileCoeff_div_factorial_eq_admissibleProfile
    M tau hell s₀

end PerronWright.GraphCore
