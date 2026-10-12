import PerronWright.Enumeration.CubicActualAdmissibleCoefficientBridge

/-!
# Reindexing the positive-surplus cubic profile coefficient

The cubic fixed-surplus composition coefficient is initially indexed by the
core size.  A cubic core of surplus `ell` has `2 * ell` branching vertices,
so its core size is uniquely of the form `2 * ell + d`.  This file records
that shift and packages the resulting finite coefficient identity in the
form needed by the analytic Taylor argument.

No analytic or enumerative hypothesis is added here.  The lower bound on the
core size is read directly from the already proved cubic reconstruction, and
the fixed-size conditional sum is merely reindexed by its cubic subtype.
-/

open scoped Classical
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

private def admissibleCubicSubtypeEquiv (q ell : ℕ) :
    {H : {H : SimpleGraph (Fin q) //
      IsAdmissibleAttachmentCore q ell H} //
      IsCubicAdmissibleAttachmentCore q ell H.1} ≃
      CubicAdmissibleAttachmentCore q ell where
  toFun H := ⟨H.1.1, H.2⟩
  invFun G := ⟨⟨G.1, G.2.1⟩, G.2⟩
  left_inv H := by
    rcases H with ⟨⟨H, hA⟩, hC⟩
    rfl
  right_inv G := by
    rcases G with ⟨G, hC⟩
    rfl

/-- A positive-surplus cubic admissible core contains its `2 * ell`
branching vertices, hence has at least that many vertices. -/
theorem two_mul_surplus_le_of_isCubicAdmissibleAttachmentCore
    {k ell : ℕ} (hell : 0 < ell) {G : SimpleGraph (Fin k)}
    (hG : IsCubicAdmissibleAttachmentCore k ell G) :
    2 * ell ≤ k := by
  obtain ⟨_K, D, _hrec⟩ :=
    (isCubicAdmissibleAttachmentCore_iff_exists_reconstruction
      hell G).mp hG
  have htotal := D.profile.totalLength
  omega

/-- The conditional cubic part of the ambient admissible-core sum is the
literal sum over the subtype of cubic admissible cores. -/
theorem fixedSurplusCubicCoreProfileCoeff_eq_cubicAdmissible_sum
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell q k : ℕ) :
    fixedSurplusCubicCoreProfileCoeff M T ell q k =
      ∑ G : CubicAdmissibleAttachmentCore q ell,
        PowerSeries.coeff k
          (fixedCoreProfileCompositionSeries M T G.1) := by
  classical
  unfold fixedSurplusCubicCoreProfileCoeff
  rw [sum_ite_eq_sum_subtype
    (p := fun H : {H : SimpleGraph (Fin q) //
      IsAdmissibleAttachmentCore q ell H} ↦
        IsCubicAdmissibleAttachmentCore q ell H.1)
    (f := fun H ↦ PowerSeries.coeff k
      (fixedCoreProfileCompositionSeries M T H.1))]
  exact Fintype.sum_equiv (admissibleCubicSubtypeEquiv q ell)
    (fun H : {H : {H : SimpleGraph (Fin q) //
      IsAdmissibleAttachmentCore q ell H} //
      IsCubicAdmissibleAttachmentCore q ell H.1} ↦
      PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M T H.1.1))
    (fun G : CubicAdmissibleAttachmentCore q ell ↦
      PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M T G.1))
    (fun _ ↦ rfl)

/-- Reindex the cubic fixed-surplus composition coefficient by the number
`d` of degree-two subdivision vertices beyond the compulsory `2 * ell`
branch vertices. -/
theorem cubicFixedSurplusProfileCompositionCoeff_eq_shifted_sum
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    {ell : ℕ} (hell : 0 < ell) (k : ℕ) :
    cubicFixedSurplusProfileCompositionCoeff M T ell k =
      ∑ d ∈ Finset.range (k + 1),
        fixedSurplusCubicCoreProfileCoeff M T ell (2 * ell + d) k /
          ((2 * ell + d).factorial : ℂ) := by
  let F : ℕ → ℂ := fun q ↦
    fixedSurplusCubicCoreProfileCoeff M T ell q k /
      (q.factorial : ℂ)
  have hsmall : ∀ q < 2 * ell, F q = 0 := by
    intro q hq
    dsimp only [F]
    have hzero :
        fixedSurplusCubicCoreProfileCoeff M T ell q k = 0 := by
      unfold fixedSurplusCubicCoreProfileCoeff
      apply Fintype.sum_eq_zero
      intro H
      by_cases hH : IsCubicAdmissibleAttachmentCore q ell H.1
      · simp only [hH, if_true]
        exact False.elim (by
          have hmin :=
            two_mul_surplus_le_of_isCubicAdmissibleAttachmentCore
              hell hH
          omega)
      · simp [hH]
    rw [hzero, zero_div]
  have hlarge : ∀ q, k < q → F q = 0 := by
    intro q hq
    dsimp only [F]
    have hzero :
        fixedSurplusCubicCoreProfileCoeff M T ell q k = 0 := by
      unfold fixedSurplusCubicCoreProfileCoeff
      apply Fintype.sum_eq_zero
      intro H
      by_cases hH : IsCubicAdmissibleAttachmentCore q ell H.1
      · simp only [hH, if_true]
        exact fixedCoreProfileCompositionSeries_coeff_eq_zero_of_lt
          M T H.1 hq
      · simp [hH]
    rw [hzero, zero_div]
  rw [cubicFixedSurplusProfileCompositionCoeff_eq_sum_range]
  change (∑ q ∈ Finset.range (k + 1), F q) =
    ∑ d ∈ Finset.range (k + 1), F (2 * ell + d)
  calc
    (∑ q ∈ Finset.range (k + 1), F q) =
        ∑ q ∈ Finset.range (k + 1 + 2 * ell), F q := by
      apply Finset.sum_subset_zero_on_sdiff
      · exact Finset.range_mono (by omega)
      · intro q hq
        have hnot := (Finset.mem_sdiff.mp hq).2
        have hkq : k < q := by
          have hnlt : ¬ q < k + 1 := fun hlt ↦
            hnot (Finset.mem_range.mpr hlt)
          omega
        exact hlarge q hkq
      · intro q hq
        rfl
    _ = ∑ d ∈ Finset.range (k + 1), F (2 * ell + d) := by
      have hsplit := Finset.sum_range_add F (2 * ell) (k + 1)
      have hzero : ∑ q ∈ Finset.range (2 * ell), F q = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        exact hsmall q (Finset.mem_range.mp hq)
      rw [hzero, zero_add] at hsplit
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsplit

/-- The coefficient of the finite shifted sum of literal cubic fixed-core
profile series is the cubic fixed-surplus composition coefficient. -/
theorem coeff_finite_cubic_core_sum_eq_cubicFixedSurplusProfileCompositionCoeff
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    {ell : ℕ} (hell : 0 < ell) (k : ℕ) :
    PowerSeries.coeff k
        (∑ d ∈ Finset.range (k + 1),
          (((2 * ell + d).factorial : ℂ)⁻¹) •
            ∑ G : CubicAdmissibleAttachmentCore (2 * ell + d) ell,
              fixedCoreProfileCompositionSeries M T G.1) =
      cubicFixedSurplusProfileCompositionCoeff M T ell k := by
  rw [cubicFixedSurplusProfileCompositionCoeff_eq_shifted_sum
    M T hell k]
  simp only [map_sum, PowerSeries.coeff_smul, Finset.smul_sum,
    smul_eq_mul, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.mul_sum]
  rw [← fixedSurplusCubicCoreProfileCoeff_eq_cubicAdmissible_sum
    M T ell (2 * ell + d) k]
  ring

end PerronWright.GraphCore
