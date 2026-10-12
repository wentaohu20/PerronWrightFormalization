import PerronWright.Probability.FiniteIrreducibleTypedGraphLaw
import PerronWright.Probability.FiniteIrreducibleTypeFiberSums
import PerronWright.Probability.FreshTypeEmpiricalIdentities

/-!
# The exact deterministic finite isolation exponent

The sum of all edge hazards touching a selected vertex set is proved
equal to t/n times the literal count-based isolation budget. Its
degree term uses the actual empirical counts, not the target law.
The one-half diagonal correction is retained exactly.
-/

open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleSelectedIsolationExponent

open AnnealedGraph SelectedConfiguration AnnealedResidualFixedBlock
open FiniteIrreducibleTypedGraphLaw FiniteIrreducibleTypePlacementMultiplicity
open FiniteIrreducibleTypeFiberSums

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- True selected type counts in the given ambient assignment. -/
def selectedCount {n : ℕ} (x : Fin n → S) (U : Finset (Fin n)) (a : S) : ℕ :=
  fiberCount (fun v : ↥U ↦ x v.val) a

def exposureBudget (M : FiniteIrreducibleModel S) {n : ℕ}
    (x : Fin n → S) (U : Finset (Fin n)) : ℝ :=
  ∑ a : S, ∑ b : S,
    (selectedCount x U a : ℝ) * M.kernel a b * (fiberCount x b : ℝ)

def selectedQuadratic (M : FiniteIrreducibleModel S) {n : ℕ}
    (x : Fin n → S) (U : Finset (Fin n)) : ℝ :=
  ∑ a : S, ∑ b : S,
    (selectedCount x U a : ℝ) * M.kernel a b * (selectedCount x U b : ℝ)

def selectedDiagonal (M : FiniteIrreducibleModel S) {n : ℕ}
    (x : Fin n → S) (U : Finset (Fin n)) : ℝ :=
  ∑ a : S, (selectedCount x U a : ℝ) * M.kernel a a

/-- The paper's exact count-based B_n(K), before any target-law approximation. -/
def isolationBudget (M : FiniteIrreducibleModel S) {n : ℕ}
    (x : Fin n → S) (U : Finset (Fin n)) : ℝ :=
  exposureBudget M x U - selectedQuadratic M x U / 2 - selectedDiagonal M x U / 2

/-- The finite unordered boundary-pair sum counts each pair once. -/
theorem sum_boundaryEdges {n : ℕ} (U : Finset (Fin n)) (F : Edge n → ℝ) :
    (∑ e ∈ boundaryEdges U, F e) =
      ∑ p : {j : Fin n // j ∉ U} × {i : Fin n // i ∈ U},
        F (boundaryEdge U p) := by
  symm
  apply Finset.sum_bij (fun p _ ↦ boundaryEdge U p)
  · intro p _
    exact boundaryEdge_mem U p
  · intro p _ q _ heq
    exact boundaryEdge_injective U heq
  · intro e he
    obtain ⟨p, hp⟩ := boundaryEdge_surjective U e he
    exact ⟨p, Finset.mem_univ _, hp⟩
  · intro p _
    rfl

theorem internal_pair_sum_eq_upper (M : FiniteIrreducibleModel S)
    {n : ℕ} (x : Fin n → S) (U : Finset (Fin n)) :
    (∑ e ∈ internalEdges U, pairKernel M x e.val) =
      ∑ i ∈ U, ∑ j ∈ U, if i < j then M.kernel (x i) (x j) else 0 := by
  have hs : U.offDiag.filter (fun p ↦ p.1 < p.2) =
      (U ×ˢ U).filter (fun p ↦ p.1 < p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
    constructor
    · rintro ⟨⟨hi, hj, _⟩, hp⟩
      exact ⟨⟨hi, hj⟩, hp⟩
    · rintro ⟨⟨hi, hj⟩, hp⟩
      exact ⟨⟨hi, hj, ne_of_lt hp⟩, hp⟩
  rw [FreshTypeEmpiricalIdentities.sum_internalEdges_eq_sym2,
    Finset.sum_sym2_filter_not_isDiag, hs]
  simp only [pairKernel_mk]
  rw [Finset.sum_filter, Finset.sum_product]

/-- Selected ordered pairs split into two unordered internal copies and
the genuine vertex-label diagonal; equal types are not deleted. -/
theorem selected_pair_sum_eq_twice_internal_add_diagonal
    (M : FiniteIrreducibleModel S) {n : ℕ}
    (x : Fin n → S) (U : Finset (Fin n)) :
    (∑ i ∈ U, ∑ j ∈ U, M.kernel (x i) (x j)) =
      2 * (∑ e ∈ internalEdges U, pairKernel M x e.val) +
        ∑ i ∈ U, M.kernel (x i) (x i) := by
  have hpoint (i j : Fin n) : M.kernel (x i) (x j) =
      (if i < j then M.kernel (x i) (x j) else 0) +
        (if j < i then M.kernel (x i) (x j) else 0) +
          (if i = j then M.kernel (x i) (x j) else 0) := by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · simp only [if_pos hlt, if_neg (not_lt_of_ge hlt.le), if_neg (ne_of_lt hlt), add_zero]
    · subst j
      simp only [lt_self_iff_false, if_false, if_true, zero_add]
    · simp only [if_pos hgt, if_neg (not_lt_of_ge hgt.le), if_neg (ne_of_gt hgt),
        zero_add, add_zero]
  have hswap : (∑ i ∈ U, ∑ j ∈ U,
      if j < i then M.kernel (x i) (x j) else 0) =
        ∑ i ∈ U, ∑ j ∈ U, if i < j then M.kernel (x i) (x j) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [M.symmetric (x i) (x j)]
  have hdiag : (∑ i ∈ U, ∑ j ∈ U,
      if i = j then M.kernel (x i) (x j) else 0) =
        ∑ i ∈ U, M.kernel (x i) (x i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_ite_eq]
    simp only [hi, if_true]
  have he : (∑ i ∈ U, ∑ j ∈ U, M.kernel (x i) (x j)) =
      ∑ i ∈ U, ∑ j ∈ U,
        ((if i < j then M.kernel (x i) (x j) else 0) +
          (if j < i then M.kernel (x i) (x j) else 0) +
            (if i = j then M.kernel (x i) (x j) else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hpoint i j
  rw [he]
  simp_rw [Finset.sum_add_distrib]
  rw [hswap, hdiag, internal_pair_sum_eq_upper]
  ring

theorem boundary_pair_sum_eq (M : FiniteIrreducibleModel S)
    {n : ℕ} (x : Fin n → S) (U : Finset (Fin n)) :
    (∑ e ∈ boundaryEdges U, pairKernel M x e.val) =
      ∑ i ∈ U, ∑ j ∈ Uᶜ, M.kernel (x i) (x j) := by
  rw [sum_boundaryEdges, Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ i : ↥U, ∑ j ∈ Uᶜ, M.kernel (x i.val) (x j) := by
      apply Finset.sum_congr rfl
      intro i _
      let e : {j : Fin n // j ∉ U} ≃ ↥Uᶜ :=
        Equiv.subtypeEquivRight (fun j ↦ Finset.mem_compl.symm)
      calc
        _ = ∑ j : ↥Uᶜ, M.kernel (x i.val) (x j.val) :=
          e.sum_comp (fun j ↦ M.kernel (x i.val) (x j.val))
        _ = _ := Finset.sum_coe_sort Uᶜ (fun j ↦ M.kernel (x i.val) (x j))
    _ = _ := Finset.sum_coe_sort U (fun i ↦ ∑ j ∈ Uᶜ, M.kernel (x i) (x j))

theorem exposureBudget_eq_vertex_sum (M : FiniteIrreducibleModel S)
    {n : ℕ} (x : Fin n → S) (U : Finset (Fin n)) :
    exposureBudget M x U = ∑ i ∈ U, ∑ j : Fin n, M.kernel (x i) (x j) := by
  have h := sum_pair_by_typeFibers (fun i : ↥U ↦ x i.val) x M.kernel
  change (∑ i : ↥U, ∑ j : Fin n, M.kernel (x i.val) (x j)) =
    exposureBudget M x U at h
  rw [← h]
  exact Finset.sum_coe_sort U (fun i ↦ ∑ j : Fin n, M.kernel (x i) (x j))

theorem selectedQuadratic_eq_vertex_sum (M : FiniteIrreducibleModel S)
    {n : ℕ} (x : Fin n → S) (U : Finset (Fin n)) :
    selectedQuadratic M x U = ∑ i ∈ U, ∑ j ∈ U, M.kernel (x i) (x j) := by
  have h := sum_pair_by_typeFibers (fun i : ↥U ↦ x i.val)
    (fun j : ↥U ↦ x j.val) M.kernel
  change (∑ i : ↥U, ∑ j : ↥U, M.kernel (x i.val) (x j.val)) =
    selectedQuadratic M x U at h
  rw [← h]
  calc
    _ = ∑ i : ↥U, ∑ j ∈ U, M.kernel (x i.val) (x j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_coe_sort U (fun j ↦ M.kernel (x i.val) (x j))
    _ = _ := Finset.sum_coe_sort U (fun i ↦ ∑ j ∈ U, M.kernel (x i) (x j))

theorem selectedDiagonal_eq_vertex_sum (M : FiniteIrreducibleModel S)
    {n : ℕ} (x : Fin n → S) (U : Finset (Fin n)) :
    selectedDiagonal M x U = ∑ i ∈ U, M.kernel (x i) (x i) := by
  have h := sum_by_typeFibers (fun i : ↥U ↦ x i.val) (fun a ↦ M.kernel a a)
  change (∑ i : ↥U, M.kernel (x i.val) (x i.val)) = selectedDiagonal M x U at h
  rw [← h]
  exact Finset.sum_coe_sort U (fun i ↦ M.kernel (x i) (x i))

/-- Every prescribed unordered non-diagonal pair is accounted for,
including pairs joining different selected component blocks. -/
theorem sum_prescribed_pairKernel_eq_isolationBudget
    (M : FiniteIrreducibleModel S) {n : ℕ}
    (x : Fin n → S) (U : Finset (Fin n)) :
    (∑ e ∈ prescribedEdges U, pairKernel M x e.val) = isolationBudget M x U := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (prescribedEdges U)
    (fun e ↦ both U e.val) (fun e ↦ pairKernel M x e.val)
  change (∑ e ∈ internalEdges U, _) + (∑ e ∈ boundaryEdges U, _) =
    ∑ e ∈ prescribedEdges U, _ at hsplit
  have htotal : (∑ i ∈ U, ∑ j : Fin n, M.kernel (x i) (x j)) =
      (∑ i ∈ U, ∑ j ∈ U, M.kernel (x i) (x j)) +
        ∑ i ∈ U, ∑ j ∈ Uᶜ, M.kernel (x i) (x j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (Finset.sum_add_sum_compl U (fun j ↦ M.kernel (x i) (x j))).symm
  have hi := selected_pair_sum_eq_twice_internal_add_diagonal M x U
  have hb := boundary_pair_sum_eq M x U
  unfold isolationBudget
  rw [exposureBudget_eq_vertex_sum, selectedQuadratic_eq_vertex_sum,
    selectedDiagonal_eq_vertex_sum]
  linarith

/-- Exact paper isolation exponent for the actual finite graph law. -/
theorem sum_prescribed_hazard_eq (M : FiniteIrreducibleModel S) (t : ℝ)
    {n : ℕ} (x : Fin n → S) (U : Finset (Fin n)) :
    (∑ e ∈ prescribedEdges U, hazard M t x e) =
      t / (n : ℝ) * isolationBudget M x U := by
  have he (e : Edge n) : hazard M t x e =
      t / (n : ℝ) * pairKernel M x e.val := by
    unfold FiniteIrreducibleTypedGraphLaw.hazard
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, sum_prescribed_pairKernel_eq_isolationBudget]

/-- Degree against the true empirical type probabilities. -/
def empiricalDegree (M : FiniteIrreducibleModel S) {n : ℕ}
    (x : Fin n → S) (a : S) : ℝ :=
  ∑ b : S, M.kernel a b * ((fiberCount x b : ℝ) / (n : ℝ))

theorem exposureBudget_eq_empiricalDegree (M : FiniteIrreducibleModel S)
    {n : ℕ} (hn : 0 < n) (x : Fin n → S) (U : Finset (Fin n)) :
    exposureBudget M x U =
      (n : ℝ) * ∑ a : S, (selectedCount x U a : ℝ) * empiricalDegree M x a := by
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  unfold exposureBudget empiricalDegree
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  field_simp

/-- The exact displayed B_n(K) in the deterministic finite component formula. -/
theorem isolationBudget_eq_empiricalDegree (M : FiniteIrreducibleModel S)
    {n : ℕ} (hn : 0 < n) (x : Fin n → S) (U : Finset (Fin n)) :
    isolationBudget M x U =
      (n : ℝ) * (∑ a : S, (selectedCount x U a : ℝ) * empiricalDegree M x a) -
        (∑ a : S, ∑ b : S,
          (selectedCount x U a : ℝ) * M.kernel a b * (selectedCount x U b : ℝ)) / 2 -
        (∑ a : S, (selectedCount x U a : ℝ) * M.kernel a a) / 2 := by
  unfold isolationBudget selectedQuadratic selectedDiagonal
  rw [exposureBudget_eq_empiricalDegree M hn]

end PerronWright.FiniteIrreducibleSelectedIsolationExponent

