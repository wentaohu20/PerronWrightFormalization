import PerronWright.Probability.FreshTypeCumulantExpansion
import PerronWright.Probability.ProjectiveKernelClosure
import Mathlib.Algebra.BigOperators.Sym

/-!
# Fresh exposure moments and the actual empirical residual kernel

These are exact deterministic identities for sampled types, connecting the
literal Laplace moments to the canonical residual kernel used by the proved
projective-quadratic concentration theorem.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FreshTypeEmpiricalIdentities

open FreshTypeAveraging FreshTypeCumulantExpansion ProjectiveKernelClosure
  AnnealedResidualFixedBlock AnnealedGraph SelectedConfiguration

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def pairKernelSum {I : Type*} [Fintype I] (M : CompactBJRModel S) (x : I → S) : ℝ :=
  ∑ i : I, ∑ j : I, M.kernel (x i) (x j)

def residualKernelSum {I : Type*} [Fintype I] (M : CompactBJRModel S) (x : I → S) : ℝ :=
  ∑ i : I, ∑ j : I, residualKernel M (x i,x j)

/-- The actual second fresh-exposure moment is the double sum of the
iterated model kernel; integrability follows from compact continuity. -/
theorem exposureMoment_two_eq_iteratedKernelSum {I : Type*} [Fintype I]
    (M : CompactBJRModel S) (x : I → S) :
    exposureMoment M x 2 = ∑ i : I, ∑ j : I, M.iteratedKernelMap 1 (x i,x j) := by
  have hc (i j : I) : Integrable (fun y ↦ M.kernel (x i) y * M.kernel (x j) y) M.mu :=
    (by fun_prop : Continuous (fun y ↦ M.kernel (x i) y * M.kernel (x j) y)).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have he (y : S) : exposure M x y ^ 2 = ∑ i : I, ∑ j : I,
      M.kernel (x i) y * M.kernel (x j) y := by
    unfold exposure
    rw [pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  unfold exposureMoment
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hc i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hc i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [M.iteratedKernelMap_apply 1]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    change M.kernel (x i) y * M.kernel (x j) y = M.kernel (x i) y * M.kernel y (x j)
    rw [M.kernel.symmetric (x j) y])

/-- Exact canonical-kernel form of the raw second cumulant. -/
theorem residualKernelSum_eq {I : Type*} [Fintype I]
    (M : CompactBJRModel S) (x : I → S) :
    residualKernelSum M x = exposureMoment M x 2 - pairKernelSum M x -
      (totalDegree M x - (Fintype.card I : ℝ)) ^ 2 := by
  have hpoint (i j : I) : residualKernel M (x i,x j) =
      M.iteratedKernelMap 1 (x i,x j) - M.kernel (x i) (x j) -
        (M.degreeFunction (x i)-1) * (M.degreeFunction (x j)-1) := rfl
  unfold residualKernelSum
  simp_rw [hpoint,Finset.sum_sub_distrib]
  rw [← exposureMoment_two_eq_iteratedKernelSum]
  change exposureMoment M x 2 - pairKernelSum M x -
    (∑ i : I, ∑ j : I, (M.degreeFunction (x i)-1)*(M.degreeFunction (x j)-1)) = _
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  unfold totalDegree
  ring

theorem residualKernelSum_variance_identity {I : Type*} [Fintype I]
    (M : CompactBJRModel S) (x : I → S) :
    ((Fintype.card I : ℝ) ^ 2 - 2 * (Fintype.card I : ℝ) * totalDegree M x +
      pairKernelSum M x - exposureVariance M x) = -residualKernelSum M x := by
  rw [residualKernelSum_eq]
  unfold exposureVariance
  ring

def diagonalKernelSum {I : Type*} [Fintype I] (M : CompactBJRModel S) (x : I → S) : ℝ :=
  ∑ i : I, M.kernel (x i) (x i)

def upperPairSum {I : Type*} [Fintype I] [LinearOrder I]
    (M : CompactBJRModel S) (x : I → S) : ℝ :=
  ∑ i : I, ∑ j : I, if i < j then M.kernel (x i) (x j) else 0

/-- Repeated sampled types are allowed: the diagonal refers to vertex
labels, not to distinct type values. -/
theorem pairKernelSum_eq_twice_upperPairSum_add_diagonal {I : Type*} [Fintype I] [LinearOrder I]
    (M : CompactBJRModel S) (x : I → S) :
    pairKernelSum M x = 2 * upperPairSum M x + diagonalKernelSum M x := by
  have hpoint (i j : I) : M.kernel (x i) (x j) =
      (if i < j then M.kernel (x i) (x j) else 0) +
        (if j < i then M.kernel (x i) (x j) else 0) +
          (if i = j then M.kernel (x i) (x j) else 0) := by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · simp only [if_pos hlt,if_neg (not_lt_of_ge hlt.le),if_neg (ne_of_lt hlt),add_zero]
    · subst j
      simp only [lt_self_iff_false,if_false,if_true,zero_add]
    · simp only [if_pos hgt,if_neg (not_lt_of_ge hgt.le),if_neg (ne_of_gt hgt),zero_add,add_zero]
  have hswap : (∑ i : I, ∑ j : I, if j < i then M.kernel (x i) (x j) else 0) = upperPairSum M x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [M.kernel.symmetric (x i) (x j)]
  have he : pairKernelSum M x = ∑ i : I, ∑ j : I,
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
  rw [hswap]
  have hdiag : (∑ i : I, ∑ j : I, if i = j then M.kernel (x i) (x j) else 0) = diagonalKernelSum M x := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ,if_true]
  rw [hdiag]
  unfold upperPairSum diagonalKernelSum
  ring

theorem mem_sym2_iff_both {n : ℕ} (B : Finset (Fin n)) (e : Sym2 (Fin n)) :
    e ∈ B.sym2 ↔ both B e := by
  induction e using Sym2.inductionOn with
  | _ i j => exact Finset.mk_mem_sym2_iff

/-- The actual internal-edge index set, rather than an assumed labelled
graph reduction, is the off-diagonal symmetric square of selected labels. -/
theorem sum_internalEdges_eq_sym2 {n : ℕ} (B : Finset (Fin n)) (F : Sym2 (Fin n) → ℝ) :
    (∑ e ∈ internalEdges B, F e.val) = ∑ e ∈ B.sym2.filter (fun e ↦ ¬e.IsDiag), F e := by
  apply Finset.sum_bij (fun e _ ↦ e.val)
  · intro e he
    exact Finset.mem_filter.mpr ⟨(mem_sym2_iff_both B e.val).mpr ((mem_internalEdges B e).mp he).2,e.property⟩
  · intro e _ e' _ heq
    exact Subtype.ext heq
  · intro e he
    have hmem := Finset.mem_filter.mp he
    refine ⟨⟨e,hmem.2⟩,?_,rfl⟩
    rw [mem_internalEdges]
    have hb := (mem_sym2_iff_both B e).mp hmem.1
    refine ⟨?_,hb⟩
    induction e using Sym2.inductionOn with
    | _ i j => exact Or.inl hb.1
  · intro e _
    rfl

/-- Exact conversion of the literal internal-pair hazard into a sum over
unordered selected labels. -/
theorem internalPairWeightOn_eq_upperPairSum {n : ℕ}
    (M : CompactBJRModel S) (B : Finset (Fin n)) (u : ↥B → S) (s₀ : S) :
    internalPairWeightOn M B u s₀ = upperPairSum M u := by
  let x := combineTypes B u (fun _ ↦ s₀)
  have hu : upperPairSum M u = ∑ i ∈ B, ∑ j ∈ B,
      if i < j then M.kernel (x i) (x j) else 0 := by
    unfold upperPairSum
    have he : (∑ i : ↥B, ∑ j : ↥B, if i < j then M.kernel (u i) (u j) else 0) =
        ∑ i : ↥B, ∑ j : ↥B, if i.val < j.val then M.kernel (x i.val) (x j.val) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change (if i.val < j.val then M.kernel (u i) (u j) else 0) = _
      simp only [x,combineTypes_inside]
    rw [he]
    calc
      _ = ∑ i : ↥B, ∑ j ∈ B, if i.val < j then M.kernel (x i.val) (x j) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_coe_sort B (fun j ↦ if i.val < j then M.kernel (x i.val) (x j) else 0)
      _ = _ := Finset.sum_coe_sort B (fun i ↦ ∑ j ∈ B, if i < j then M.kernel (x i) (x j) else 0)
  have hs : B.offDiag.filter (fun p ↦ p.1 < p.2) =
      (B ×ˢ B).filter (fun p ↦ p.1 < p.2) := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_offDiag,Finset.mem_product]
    constructor
    · rintro ⟨⟨hi,hj,_⟩,hp⟩
      exact ⟨⟨hi,hj⟩,hp⟩
    · rintro ⟨⟨hi,hj⟩,hp⟩
      exact ⟨⟨hi,hj,ne_of_lt hp⟩,hp⟩
  unfold internalPairWeightOn
  rw [sum_internalEdges_eq_sym2,Finset.sum_sym2_filter_not_isDiag,hs]
  simp only [CompactBJRModel.edgeFactor_mk,one_mul]
  rw [Finset.sum_filter,Finset.sum_product,hu]

theorem pairKernelSum_eq_internalPairWeightOn {n : ℕ}
    (M : CompactBJRModel S) (B : Finset (Fin n)) (u : ↥B → S) (s₀ : S) :
    pairKernelSum M u = 2 * internalPairWeightOn M B u s₀ + diagonalKernelSum M u := by
  rw [internalPairWeightOn_eq_upperPairSum]
  exact pairKernelSum_eq_twice_upperPairSum_add_diagonal M u

/-- The critical quadratic part of the actual selected residual, including
its genuine diagonal correction, is the canonical residual-kernel sum. -/
theorem critical_quadratic_internalPair_identity {n : ℕ}
    (M : CompactBJRModel S) (B : Finset (Fin n)) (u : ↥B → S) (s₀ : S) :
    (B.card : ℝ) * totalDegree M u - internalPairWeightOn M B u s₀ +
      exposureVariance M u / 2 - (B.card : ℝ)^2 / 2 =
        residualKernelSum M u / 2 + diagonalKernelSum M u / 2 := by
  have hR := residualKernelSum_variance_identity M u
  have hP := pairKernelSum_eq_internalPairWeightOn M B u s₀
  simp only [Fintype.card_coe] at hR
  linarith

end PerronWright.FreshTypeEmpiricalIdentities
