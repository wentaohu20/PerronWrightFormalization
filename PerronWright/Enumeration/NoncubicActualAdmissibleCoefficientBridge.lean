import PerronWright.Enumeration.VariablePresentationProfileRegroup
import PerronWright.Enumeration.PositiveSurplusNoncubicProfileTaylor

/-!
# The actual noncubic coefficient in bounded-kernel coordinates

This file is the finite, graph-theoretic end of the noncubic profile
bridge.  On a monomial vertex profile, only the literal core size can
contribute to the fixed-surplus composition coefficient.  At that size,
the exact variable-kernel presentation classification identifies the
actual labelled-core sum with the finite inverse-coordinate-multiplicity
sum over connected noncubic bounded kernels and admissible length
profiles.

No analytic continuation or infinite-series interchange is used here.
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

/-- Restricting the ambient admissible-core type to the complement of the
cubic condition is exactly the intrinsic noncubic admissible-core type. -/
private def admissibleNoncubicSubtypeEquiv (k ell : ℕ) :
    {H : {H : SimpleGraph (Fin k) //
      IsAdmissibleAttachmentCore k ell H} //
      ¬IsCubicAdmissibleAttachmentCore k ell H.1} ≃
      NoncubicAdmissibleAttachmentCore k ell where
  toFun H :=
    ⟨H.1.1, H.1.2, fun hcubic ↦ H.2 ⟨H.1.2, hcubic⟩⟩
  invFun G :=
    ⟨⟨G.1, G.2.1⟩, not_isCubic_of_isNoncubic G.2⟩
  left_inv H := by
    rcases H with ⟨⟨H, hA⟩, hnoncubic⟩
    rfl
  right_inv G := by
    rcases G with ⟨G, hG⟩
    rfl

/-- The conditional noncubic part of the ambient admissible-core sum is
the literal sum over noncubic admissible cores. -/
theorem fixedSurplusNoncubicCoreProfileCoeff_eq_noncubicAdmissible_sum
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell q k : ℕ) :
    fixedSurplusNoncubicCoreProfileCoeff M T ell q k =
      ∑ G : NoncubicAdmissibleAttachmentCore q ell,
        PowerSeries.coeff k
          (fixedCoreProfileCompositionSeries M T G.1) := by
  classical
  unfold fixedSurplusNoncubicCoreProfileCoeff
  calc
    (∑ H : {H : SimpleGraph (Fin q) //
          IsAdmissibleAttachmentCore q ell H},
        if IsCubicAdmissibleAttachmentCore q ell H.1 then 0
        else PowerSeries.coeff k
          (fixedCoreProfileCompositionSeries M T H.1)) =
        ∑ H : {H : SimpleGraph (Fin q) //
            IsAdmissibleAttachmentCore q ell H},
          if ¬IsCubicAdmissibleAttachmentCore q ell H.1 then
            PowerSeries.coeff k
              (fixedCoreProfileCompositionSeries M T H.1) else 0 := by
      apply Fintype.sum_congr
      intro H
      by_cases hH : IsCubicAdmissibleAttachmentCore q ell H.1 <;>
        simp [hH]
    _ = ∑ H : {H : {H : SimpleGraph (Fin q) //
          IsAdmissibleAttachmentCore q ell H} //
          ¬IsCubicAdmissibleAttachmentCore q ell H.1},
        PowerSeries.coeff k
          (fixedCoreProfileCompositionSeries M T H.1.1) := by
      exact sum_ite_eq_sum_subtype
        (p := fun H : {H : SimpleGraph (Fin q) //
          IsAdmissibleAttachmentCore q ell H} ↦
            ¬IsCubicAdmissibleAttachmentCore q ell H.1)
        (f := fun H ↦ PowerSeries.coeff k
          (fixedCoreProfileCompositionSeries M T H.1))
    _ = ∑ G : NoncubicAdmissibleAttachmentCore q ell,
        PowerSeries.coeff k
          (fixedCoreProfileCompositionSeries M T G.1) := by
      exact Fintype.sum_equiv (admissibleNoncubicSubtypeEquiv q ell)
        (fun H : {H : {H : SimpleGraph (Fin q) //
          IsAdmissibleAttachmentCore q ell H} //
          ¬IsCubicAdmissibleAttachmentCore q ell H.1} ↦
            PowerSeries.coeff k
              (fixedCoreProfileCompositionSeries M T H.1.1))
        (fun G : NoncubicAdmissibleAttachmentCore q ell ↦
          PowerSeries.coeff k
            (fixedCoreProfileCompositionSeries M T G.1))
        (fun _ ↦ rfl)

/-- At the core size, a monomial profile turns the filtered noncubic
fixed-core coefficient into the literal sum over noncubic admissible
cores. -/
theorem fixedSurplusNoncubicCoreProfileCoeff_X_mul_C_eq_coreWeightSum
    (M : CompactBJRModel S) (tau : C(S, ℂ)) (ell k : ℕ) :
    fixedSurplusNoncubicCoreProfileCoeff M
        (PowerSeries.X * PowerSeries.C tau) ell k k =
      fixedSurplusNoncubicCoreWeightSum M tau ell k := by
  classical
  unfold fixedSurplusNoncubicCoreProfileCoeff
    fixedSurplusNoncubicCoreWeightSum
  simp_rw [fixedCoreProfileCompositionSeries_X_mul_C_coeff M tau]
  calc
    (∑ H : {H : SimpleGraph (Fin k) //
          IsAdmissibleAttachmentCore k ell H},
        if IsCubicAdmissibleAttachmentCore k ell H.1 then 0
        else finiteComplexGraphWeight M tau H.1) =
        ∑ H : {H : SimpleGraph (Fin k) //
            IsAdmissibleAttachmentCore k ell H},
          if ¬IsCubicAdmissibleAttachmentCore k ell H.1 then
            finiteComplexGraphWeight M tau H.1 else 0 := by
      apply Fintype.sum_congr
      intro H
      by_cases hH : IsCubicAdmissibleAttachmentCore k ell H.1 <;>
        simp [hH]
    _ = ∑ H : {H : {H : SimpleGraph (Fin k) //
          IsAdmissibleAttachmentCore k ell H} //
          ¬IsCubicAdmissibleAttachmentCore k ell H.1},
        finiteComplexGraphWeight M tau H.1.1 := by
      exact sum_ite_eq_sum_subtype
        (p := fun H : {H : SimpleGraph (Fin k) //
          IsAdmissibleAttachmentCore k ell H} ↦
            ¬IsCubicAdmissibleAttachmentCore k ell H.1)
        (f := fun H ↦ finiteComplexGraphWeight M tau H.1)
    _ = ∑ G : NoncubicAdmissibleAttachmentCore k ell,
        finiteComplexGraphWeight M tau G.1 := by
      exact Fintype.sum_equiv (admissibleNoncubicSubtypeEquiv k ell)
        (fun H : {H : {H : SimpleGraph (Fin k) //
          IsAdmissibleAttachmentCore k ell H} //
          ¬IsCubicAdmissibleAttachmentCore k ell H.1} ↦
            finiteComplexGraphWeight M tau H.1.1)
        (fun G : NoncubicAdmissibleAttachmentCore k ell ↦
          finiteComplexGraphWeight M tau G.1)
        (fun _ ↦ rfl)

/-- Antidiagonal reindexing of the noncubic part of the fixed-surplus
profile coefficient by the literal core size. -/
theorem noncubicFixedSurplusProfileCompositionCoeff_eq_sum_range
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell k : ℕ) :
    noncubicFixedSurplusProfileCompositionCoeff M T ell k =
      ∑ q ∈ Finset.range (k + 1),
        fixedSurplusNoncubicCoreProfileCoeff M T ell q k /
          (q.factorial : ℂ) := by
  unfold noncubicFixedSurplusProfileCompositionCoeff
  let f : ℕ × ℕ → ℂ := fun p ↦
    fixedSurplusNoncubicCoreProfileCoeff M T ell p.1 k /
      (p.1.factorial : ℂ)
  change (∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k}, f p.1) = _
  rw [Finset.sum_coe_sort]
  change (∑ p ∈ coreOffSizePairs k, f p) = _
  rw [coreOffSizePairs, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- On a monomial profile the noncubic antidiagonal composition has only
the core-size term. -/
theorem noncubicFixedSurplusProfileCompositionCoeff_X_mul_C
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (ell k : ℕ) :
    noncubicFixedSurplusProfileCompositionCoeff M
        (PowerSeries.X * PowerSeries.C tau) ell k =
      fixedSurplusNoncubicCoreProfileCoeff M
          (PowerSeries.X * PowerSeries.C tau) ell k k /
        (k.factorial : ℂ) := by
  rw [noncubicFixedSurplusProfileCompositionCoeff_eq_sum_range]
  apply Finset.sum_eq_single k
  · intro q hq hqk
    have hzero : fixedSurplusNoncubicCoreProfileCoeff M
        (PowerSeries.X * PowerSeries.C tau) ell q k = 0 := by
      unfold fixedSurplusNoncubicCoreProfileCoeff
      apply Finset.sum_eq_zero
      intro H _
      by_cases hH : IsCubicAdmissibleAttachmentCore q ell H.1
      · simp [hH]
      · simp only [hH, if_false]
        exact fixedCoreProfileCompositionSeries_X_mul_C_coeff_eq_zero_of_ne
          M tau H.1 hqk.symm
    rw [hzero, zero_div]
  · intro hknot
    exact False.elim (hknot (Finset.mem_range.mpr (by omega)))

/-- After labelled-EGF division, the monomial noncubic coefficient is the
finite inverse-coordinate-multiplicity sum over connected bounded kernels
and their admissible length profiles. -/
theorem noncubicFixedSurplusProfileCompositionCoeff_X_mul_C_eq_kernelProfiles
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell k : ℕ} (hell : 0 < ell) (s₀ : S) :
    letI : ∀ K : LabelledConnectedNoncubicKernel ell,
        Fintype (BoundedKernelLengthProfile k
          K.1.toLabelledBoundedKernel) :=
      fun K ↦ boundedKernelLengthProfileFintype k
        K.1.toLabelledBoundedKernel
    noncubicFixedSurplusProfileCompositionCoeff M
        (PowerSeries.X * PowerSeries.C tau) ell k =
      ∑ K : LabelledConnectedNoncubicKernel ell,
        labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K *
          ∑ L : BoundedKernelLengthProfile k
              K.1.toLabelledBoundedKernel,
            boundedKernelLengthProfileIntegral M tau
              K.1.toLabelledBoundedKernel L := by
  rw [noncubicFixedSurplusProfileCompositionCoeff_X_mul_C]
  rw [fixedSurplusNoncubicCoreProfileCoeff_X_mul_C_eq_coreWeightSum]
  rw [fixedSurplusNoncubicCoreWeightSum_eq_connectedKernelProfiles
    M tau hell s₀]
  let _ := labelledConnectedNoncubicKernelFintype ell
  let _ (K : LabelledConnectedNoncubicKernel ell) :
      Fintype (BoundedKernelLengthProfile k
        K.1.toLabelledBoundedKernel) :=
    boundedKernelLengthProfileFintype k K.1.toLabelledBoundedKernel
  have hkfac : ((k.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  unfold labelledConnectedNoncubicKernelInverseCoordinateMultiplicity
  exact mul_div_cancel_left₀ _ hkfac

/-- The genuine noncubic part of the fixed-surplus composition
coefficient, specialized to a monomial profile, is exactly the finite
admissible bounded-kernel profile coefficient of the same total size. -/
theorem
    noncubicFixedSurplusProfileCompositionCoeff_X_mul_C_eq_admissibleProfile
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell k : ℕ} (hell : 0 < ell) (s₀ : S) :
    noncubicFixedSurplusProfileCompositionCoeff M
        (PowerSeries.X * PowerSeries.C tau) ell k =
      positiveSurplusNoncubicAdmissibleProfileCoefficient M tau ell k := by
  rw [noncubicFixedSurplusProfileCompositionCoeff_X_mul_C_eq_kernelProfiles
    M tau hell s₀]
  rfl

/-- The canonical fixed-size bounded-kernel composition series is exactly
the actual noncubic fixed-core series with the labelled-EGF factorial
normalization.  This is an identity of full power series, not merely of
their diagonal monomial values. -/
theorem
    positiveSurplusNoncubicFixedSizeProfileCompositionSeries_eq_actual
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    {ell k : ℕ} (hell : 0 < ell) :
    positiveSurplusNoncubicFixedSizeProfileCompositionSeries M T ell k =
      (k.factorial : ℂ)⁻¹ •
        fixedSurplusNoncubicCoreProfileSeries M T ell k := by
  let _ := labelledConnectedNoncubicKernelFintype ell
  let _ (K : LabelledConnectedNoncubicKernel ell) :
      Fintype (BoundedKernelLengthProfile k
        K.1.toLabelledBoundedKernel) :=
    boundedKernelLengthProfileFintype k K.1.toLabelledBoundedKernel
  let _ (K : LabelledConnectedNoncubicKernel ell) :
      Fintype (BoundedKernelSubdivisionDatum k
        K.1.toLabelledBoundedKernel) :=
    boundedKernelSubdivisionDatumFintype k K.1.toLabelledBoundedKernel
  let _ : Fintype (ConnectedNoncubicBoundedKernelPresentation k ell) :=
    connectedNoncubicBoundedKernelPresentationFintype hell
  ext n
  let W : SimpleGraph (Fin k) → ℂ := fun G ↦
    PowerSeries.coeff n (fixedCoreProfileCompositionSeries M T G)
  have hglobal :=
    sum_connectedNoncubicPresentations_invMultiplicity_graphInvariant
      (𝕜 := ℂ) (k := k) (ell := ell) hell W
  rw [Fintype.sum_sigma] at hglobal
  have hnested :
      (∑ K : LabelledConnectedNoncubicKernel ell,
        labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K *
          ∑ D : BoundedKernelSubdivisionDatum k
              K.1.toLabelledBoundedKernel,
            PowerSeries.coeff n
              (boundedKernelSubdivisionProfileCompositionSeries M T D)) =
        ∑ G : NoncubicAdmissibleAttachmentCore k ell,
          PowerSeries.coeff n
            (fixedCoreProfileCompositionSeries M T G.1) := by
    simpa only [W, Finset.mul_sum,
      ConnectedNoncubicBoundedKernelPresentation.globalMultiplicity,
      ConnectedNoncubicBoundedKernelPresentation.toBoundedKernelPresentation,
      BoundedKernelPresentation.globalMultiplicity,
      labelledConnectedNoncubicKernelInverseCoordinateMultiplicity,
      boundedKernelSubdivisionProfileCompositionSeries] using hglobal
  unfold positiveSurplusNoncubicFixedSizeProfileCompositionSeries
    fixedSurplusNoncubicCoreProfileSeries
  simp only [map_sum, PowerSeries.coeff_smul, smul_eq_mul]
  calc
    (∑ K : LabelledConnectedNoncubicKernel ell,
        labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K *
          ((((k.factorial : ℕ) : ℂ))⁻¹ *
            ∑ D : BoundedKernelSubdivisionDatum k
                K.1.toLabelledBoundedKernel,
              PowerSeries.coeff n
                (boundedKernelSubdivisionProfileCompositionSeries M T D))) =
        ∑ K : LabelledConnectedNoncubicKernel ell,
          ((((k.factorial : ℕ) : ℂ))⁻¹ *
            (labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K *
              ∑ D : BoundedKernelSubdivisionDatum k
                  K.1.toLabelledBoundedKernel,
                PowerSeries.coeff n
                  (boundedKernelSubdivisionProfileCompositionSeries M T D))) := by
      apply Finset.sum_congr rfl
      intro K _
      ring
    _ = ((((k.factorial : ℕ) : ℂ))⁻¹ *
        ∑ G : NoncubicAdmissibleAttachmentCore k ell,
          PowerSeries.coeff n
            (fixedCoreProfileCompositionSeries M T G.1)) := by
      rw [← Finset.mul_sum, hnested]

/-- Coefficient form of the preceding full-series identity. -/
theorem
    positiveSurplusNoncubicFixedSizeProfileCompositionSeries_coeff_eq_actual
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    {ell k : ℕ} (hell : 0 < ell) (n : ℕ) :
    PowerSeries.coeff n
        (positiveSurplusNoncubicFixedSizeProfileCompositionSeries
          M T ell k) =
      fixedSurplusNoncubicCoreProfileCoeff M T ell k n /
        (k.factorial : ℂ) := by
  rw [positiveSurplusNoncubicFixedSizeProfileCompositionSeries_eq_actual
    M T hell]
  rw [PowerSeries.coeff_smul]
  rw [fixedSurplusNoncubicCoreProfileCoeff_eq_noncubicAdmissible_sum]
  simp only [fixedSurplusNoncubicCoreProfileSeries, map_sum,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The degree-`n` coefficient of the finite sum of canonical fixed-size
kernel series is the actual noncubic fixed-surplus composition
coefficient.  Fixed core sizes above `n` are absent for the usual
composition-order reason. -/
theorem
    coeff_finite_noncubic_fixedSize_sum_eq_actualCompositionCoeff
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    {ell : ℕ} (hell : 0 < ell) (n : ℕ) :
    PowerSeries.coeff n
        (∑ k ∈ Finset.range (n + 1),
          positiveSurplusNoncubicFixedSizeProfileCompositionSeries
            M T ell k) =
      noncubicFixedSurplusProfileCompositionCoeff M T ell n := by
  rw [noncubicFixedSurplusProfileCompositionCoeff_eq_sum_range]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact
    positiveSurplusNoncubicFixedSizeProfileCompositionSeries_coeff_eq_actual
      M T hell n

/-- The complete canonical bounded-kernel profile-composition series is
the actual noncubic fixed-surplus composition series coefficient by
coefficient. -/
theorem positiveSurplusNoncubicProfileCompositionSeries_eq_actual
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    {ell : ℕ} (hell : 0 < ell) :
    positiveSurplusNoncubicProfileCompositionSeries M T ell =
      PowerSeries.mk
        (noncubicFixedSurplusProfileCompositionCoeff M T ell) := by
  apply PowerSeries.ext
  intro n
  rw [positiveSurplusNoncubicProfileCompositionSeries_coeff]
  unfold positiveSurplusNoncubicProfileCompositionCoeff
  rw [coeff_finite_noncubic_fixedSize_sum_eq_actualCompositionCoeff
    M T hell n]
  simp

/-- Fixed-size analytic form of the actual bridge.  Along any analytic
one-variable profile germ with zero constant coefficient, the literal
kernel/profile coefficient has the factorial-normalized actual noncubic
fixed-core series as its Taylor series. -/
theorem
    positiveSurplusNoncubicAdmissibleProfileCoefficient_hasFPowerSeriesAt_actual
    (M : CompactBJRModel S) {ell k : ℕ} (hell : 0 < ell)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    HasFPowerSeriesAt
      (fun w ↦ positiveSurplusNoncubicAdmissibleProfileCoefficient
        M (tau w) ell k)
      (oneDimensionalFormalMultilinearSeries
        ((k.factorial : ℂ)⁻¹ •
          fixedSurplusNoncubicCoreProfileSeries M
            (oneDimensionalPowerSeries p) ell k)) 0 := by
  have h :=
    positiveSurplusNoncubicAdmissibleProfileCoefficient_hasFPowerSeriesAt
      M (k := k) hell hp hp0
  rw [positiveSurplusNoncubicFixedSizeProfileCompositionSeries_eq_actual
    M (oneDimensionalPowerSeries p) hell] at h
  exact h

end PerronWright.GraphCore
