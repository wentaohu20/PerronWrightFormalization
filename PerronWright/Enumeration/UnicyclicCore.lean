import PerronWright.Enumeration.CoreAttachmentChooseClassification

/-!
# Admissible cores in the unicyclic layer

The attachment-surplus convention uses `ell = 0` for the unicyclic layer.
This module identifies its admissible ordered cores exactly as connected
2-regular finite simple graphs and records the resulting lower bound of three
on the core size.
-/

open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore

/-- At attachment surplus zero, the admissible ordered cores are exactly
the connected finite simple graphs all of whose vertices have degree two. -/
theorem isAdmissibleAttachmentCore_zero_iff_connected_forall_degree_eq_two
    {q : ℕ} (H : SimpleGraph (Fin q)) :
    IsAdmissibleAttachmentCore q 0 H ↔
      H.Connected ∧ ∀ v, H.degree v = 2 := by
  classical
  constructor
  · rintro ⟨hconn, htwo, hedge⟩
    have hmin : ∀ v, 2 ≤ H.degree v := by
      intro v
      obtain ⟨w, -, z, -, hwz, hvw, hvz⟩ :=
        htwo v (Set.mem_univ v)
      have hcard : 1 < (H.neighborFinset v).card :=
        Finset.one_lt_card_iff.mpr
          ⟨w, z, (H.mem_neighborFinset v w).mpr hvw,
            (H.mem_neighborFinset v z).mpr hvz, hwz⟩
      rw [H.card_neighborFinset_eq_degree] at hcard
      omega
    have hsum := degree_excess_eq_two_surplus H hmin (ell := 0) (by
      simpa only [Fintype.card_fin, Nat.add_zero] using hedge)
    simp only [Nat.mul_zero] at hsum
    refine ⟨hconn, fun v ↦ ?_⟩
    have hvzero : H.degree v - 2 = 0 := by
      have hnonneg : ∀ x ∈ (Finset.univ : Finset (Fin q)),
          0 ≤ H.degree x - 2 := by
        intro x _
        exact Nat.zero_le _
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum v
        (Finset.mem_univ v)
    have hvmin := hmin v
    omega
  · rintro ⟨hconn, hdeg⟩
    have htwo : IsTwoCore H Set.univ := by
      intro v _
      have hcard : 1 < (H.neighborFinset v).card := by
        rw [H.card_neighborFinset_eq_degree, hdeg v]
        omega
      obtain ⟨w, z, hw, hz, hwz⟩ := Finset.one_lt_card_iff.mp hcard
      exact ⟨w, Set.mem_univ _, z, Set.mem_univ _, hwz,
        by simpa using hw, by simpa using hz⟩
    have hsumdeg : (∑ v : Fin q, H.degree v) = 2 * q := by
      simp_rw [hdeg]
      simp [mul_comm]
    have hedge_twice : 2 * q = 2 * H.edgeFinset.card := by
      calc
        2 * q = ∑ v : Fin q, H.degree v := hsumdeg.symm
        _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
    have hedge : H.edgeFinset.card = q := by omega
    exact ⟨hconn, htwo, by simpa only [Nat.add_zero] using hedge⟩

/-- Every admissible surplus-zero core has at least three vertices. -/
theorem three_le_of_isAdmissibleAttachmentCore_zero
    {q : ℕ} {H : SimpleGraph (Fin q)}
    (hH : IsAdmissibleAttachmentCore q 0 H) :
    3 ≤ q := by
  have h :=
    (isAdmissibleAttachmentCore_zero_iff_connected_forall_degree_eq_two H).mp hH
  obtain ⟨v⟩ := h.1.nonempty
  have hlt := H.degree_lt_card_verts v
  rw [h.2 v, Fintype.card_fin] at hlt
  omega

end GraphCore
end PerronWright

