import PerronWright.Probability.ProjectiveKernel
import PerronWright.Model.PerronQuantities
import Mathlib.Logic.Equiv.Nat
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! # Proved closure properties of the paper's symmetric projective class -/

open MeasureTheory
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.ProjectiveKernel

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- A single actual feature square is in the projective class. -/
theorem hasRepresentation_square (f : C(S, ℝ)) : HasRepresentation (square f) := by
  refine ⟨fun n ↦ if n = 0 then 1 else 0, fun _ ↦ f, ?_, ?_⟩
  · apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  · simp

theorem HasRepresentation.smul {H : C(S × S, ℝ)} (h : HasRepresentation H) (c : ℝ) :
    HasRepresentation (c • H) := by
  obtain ⟨a, f, hs, he⟩ := h
  refine ⟨fun j ↦ c * a j, f, ?_, ?_⟩
  · simpa only [abs_mul, mul_assoc] using hs.mul_left |c|
  · rw [he, ← tsum_const_smul'']
    congr 1
    funext j
    exact smul_smul c (a j) (square (f j))

theorem HasRepresentation.neg {H : C(S × S, ℝ)} (h : HasRepresentation H) :
    HasRepresentation (-H) := by
  simpa only [neg_one_smul] using h.smul (-1)

/-- Addition preserves actual summable feature representations, via a
literal disjoint union reindexing of their feature sequences. -/
theorem HasRepresentation.add {H K : C(S × S, ℝ)}
    (hH : HasRepresentation H) (hK : HasRepresentation K) : HasRepresentation (H + K) := by
  obtain ⟨a, f, ha, hHe⟩ := hH
  obtain ⟨b, g, hb, hKe⟩ := hK
  let c : ℕ ⊕ ℕ → ℝ := Sum.elim a b
  let F : ℕ ⊕ ℕ → C(S, ℝ) := Sum.elim f g
  have hs : Summable (fun j ↦ |c j| * ‖F j‖ ^ 2) :=
    Summable.sum _ ha hb
  let e := Equiv.natSumNatEquivNat.symm
  refine ⟨c ∘ e, F ∘ e, e.summable_iff.mpr hs, ?_⟩
  have ht : HasSum (fun j ↦ c j • square (F j)) (H + K) := by
    apply HasSum.sum
    · simpa only [c, F, Function.comp_apply, Sum.elim_inl] using
        (hHe.symm ▸ (summable_terms ha).hasSum)
    · simpa only [c, F, Function.comp_apply, Sum.elim_inr] using
        (hKe.symm ▸ (summable_terms hb).hasSum)
  exact ((e.hasSum_iff).mpr ht).tsum_eq.symm

theorem HasRepresentation.sub {H K : C(S × S, ℝ)}
    (hH : HasRepresentation H) (hK : HasRepresentation K) : HasRepresentation (H - K) := by
  simpa only [sub_eq_add_neg] using hH.add hK.neg

end PerronWright.ProjectiveKernel

namespace PerronWright.ProjectiveKernelClosure

open ProjectiveKernel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Left composition by the actual model kernel is a linear map on
continuous two-variable kernels. -/
def leftCompLinearMap (M : CompactBJRModel S) : C(S × S, ℝ) →ₗ[ℝ] C(S × S, ℝ) where
  toFun H := KernelMap.comp M.mu M.kernel.toContinuousMap H
  map_add' H K := by
    ext ⟨x, y⟩
    simp only [KernelMap.comp_apply, ContinuousMap.add_apply, mul_add]
    rw [integral_add]
    · exact (show Continuous (fun z ↦ M.kernel.toContinuousMap (x, z) * H (z, y)) by fun_prop).integrable_of_hasCompactSupport
        isClosed_closure.isCompact
    · exact (show Continuous (fun z ↦ M.kernel.toContinuousMap (x, z) * K (z, y)) by fun_prop).integrable_of_hasCompactSupport
        isClosed_closure.isCompact
  map_smul' c H := by
    ext ⟨x, y⟩
    simp only [KernelMap.comp_apply, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z ↦ by ring)

theorem norm_leftComp_le (M : CompactBJRModel S) (H : C(S × S, ℝ)) :
    ‖leftCompLinearMap M H‖ ≤ ‖M.kernel.toContinuousMap‖ * ‖H‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro ⟨x, y⟩
  change ‖KernelMap.comp M.mu M.kernel.toContinuousMap H (x, y)‖ ≤ _
  rw [KernelMap.comp_apply]
  have hbound (z : S) : ‖M.kernel.toContinuousMap (x, z) * H (z, y)‖ ≤
      ‖M.kernel.toContinuousMap‖ * ‖H‖ := by
    rw [norm_mul]
    exact mul_le_mul (M.kernel.toContinuousMap.norm_coe_le_norm (x, z))
      (H.norm_coe_le_norm (z, y)) (norm_nonneg _) (norm_nonneg _)
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := M.mu) (Filter.Eventually.of_forall hbound)

def leftCompCLM (M : CompactBJRModel S) : C(S × S, ℝ) →L[ℝ] C(S × S, ℝ) :=
  (leftCompLinearMap M).mkContinuous ‖M.kernel.toContinuousMap‖ (norm_leftComp_le M)

theorem leftCompCLM_apply (M : CompactBJRModel S) (H : C(S × S, ℝ)) :
    leftCompCLM M H = KernelMap.comp M.mu M.kernel.toContinuousMap H := rfl

/-- Symmetrized composition, which sends each square feature to its
polarized pairing with the actual kernel action. -/
def symCompCLM (M : CompactBJRModel S) : C(S × S, ℝ) →L[ℝ] C(S × S, ℝ) :=
  (1 / 2 : ℝ) • (leftCompCLM M +
    (ContinuousMap.compCLM ℝ ℝ (ContinuousMap.prodSwap : C(S × S, S × S))).comp (leftCompCLM M))

theorem symCompCLM_square (M : CompactBJRModel S) (f : C(S, ℝ)) :
    symCompCLM M (square f) = (1 / 2 : ℝ) •
      (square (f + M.kernel.action M.mu f) - square f - square (M.kernel.action M.mu f)) := by
  ext ⟨x, y⟩
  simp only [symCompCLM, smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousMap.compCLM_apply,
    leftCompCLM_apply, ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply,
    ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
    square_apply, KernelMap.comp_apply, smul_eq_mul]
  simp_rw [← mul_assoc]
  rw [integral_mul_const, integral_mul_const, ← ContinuousKernel.action_apply,
    ← ContinuousKernel.action_apply]
  ring

theorem symCompCLM_kernel (M : CompactBJRModel S) :
    symCompCLM M M.kernel.toContinuousMap = M.iteratedKernelMap 1 := by
  ext ⟨x, y⟩
  simp only [symCompCLM, smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousMap.compCLM_apply, leftCompCLM_apply,
    ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply, ContinuousMap.smul_apply,
    ContinuousMap.add_apply, smul_eq_mul, CompactBJRModel.iteratedKernelMap_succ,
    CompactBJRModel.iteratedKernelMap_zero, KernelMap.comp_apply]
  have he : (∫ z, M.kernel.toContinuousMap (y, z) * M.kernel.toContinuousMap (z, x) ∂M.mu) =
      ∫ z, M.kernel.toContinuousMap (x, z) * M.kernel.toContinuousMap (z, y) ∂M.mu := by
    apply integral_congr_ae
    filter_upwards [] with z
    change M.kernel y z * M.kernel z x = M.kernel x z * M.kernel z y
    rw [M.kernel.symmetric y z, M.kernel.symmetric z x, mul_comm]
  rw [he]
  ring

/-- Kernel composition preserves the actual symmetric projective
representation in the special square `κ₂ = κ ∘ κ` needed by the paper.
The proof transports the original convergent series through a bounded
linear composition map, then uses polarization of its feature images. -/
theorem kernelSquare_hasRepresentation (M : CompactBJRModel S) (hQP : M.QP) :
    HasRepresentation (M.iteratedKernelMap 1) := by
  obtain ⟨a, f, hs, hEq⟩ := hQP
  let T : C(S, ℝ) → C(S, ℝ) := M.kernel.action M.mu
  let C : ℝ := ‖M.kernel.toContinuousMap‖
  have hC : 0 ≤ C := norm_nonneg _
  have hT (j : ℕ) : ‖T (f j)‖ ≤ C * ‖f j‖ := M.kernel.norm_action_le M.mu (f j)
  have hplus (j : ℕ) : ‖f j + T (f j)‖ ≤ (1 + C) * ‖f j‖ := by
    calc
      _ ≤ ‖f j‖ + ‖T (f j)‖ := norm_add_le _ _
      _ ≤ ‖f j‖ + C * ‖f j‖ := add_le_add (le_refl _) (hT j)
      _ = _ := by ring
  have hsplus : Summable (fun j ↦ |a j| * ‖f j + T (f j)‖ ^ 2) := by
    apply (hs.mul_left ((1 + C) ^ 2)).of_nonneg_of_le
      (fun j ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _))
    intro j
    calc
      _ ≤ |a j| * ((1 + C) * ‖f j‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hplus j) 2) (abs_nonneg _)
      _ = _ := by ring
  have hsT : Summable (fun j ↦ |a j| * ‖T (f j)‖ ^ 2) := by
    apply (hs.mul_left (C ^ 2)).of_nonneg_of_le
      (fun j ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _))
    intro j
    calc
      _ ≤ |a j| * (C * ‖f j‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hT j) 2) (abs_nonneg _)
      _ = _ := by ring
  let Hplus : C(S × S, ℝ) := ∑' j, a j • square (f j + T (f j))
  let HT : C(S × S, ℝ) := ∑' j, a j • square (T (f j))
  have hplusRep : HasRepresentation Hplus := ⟨a, fun j ↦ f j + T (f j), hsplus, rfl⟩
  have hTRep : HasRepresentation HT := ⟨a, fun j ↦ T (f j), hsT, rfl⟩
  have hkernelRep : HasRepresentation M.kernel.toContinuousMap := ⟨a, f, hs, hEq⟩
  have hmap : HasSum (fun j ↦ a j • symCompCLM M (square (f j))) (M.iteratedKernelMap 1) := by
    have hm := (symCompCLM M).hasSum (summable_terms hs).hasSum
    simpa only [map_smul, ← hEq, symCompCLM_kernel] using hm
  have hseries : HasSum
      (fun j ↦ (1 / 2 : ℝ) • (a j • square (f j + T (f j)) - a j • square (f j) -
        a j • square (T (f j))))
      ((1 / 2 : ℝ) • (Hplus - M.kernel.toContinuousMap - HT)) := by
    have hbase := (((summable_terms hsplus).hasSum.sub
      (hEq.symm ▸ (summable_terms hs).hasSum)).sub (summable_terms hsT).hasSum).const_smul (1 / 2 : ℝ)
    exact hbase
  have hterms (j : ℕ) : a j • symCompCLM M (square (f j)) =
      (1 / 2 : ℝ) • (a j • square (f j + T (f j)) - a j • square (f j) -
        a j • square (T (f j))) := by
    rw [symCompCLM_square]
    ext p
    simp only [T, ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul]
    ring
  simp_rw [← hterms] at hseries
  have hkernelEq := hmap.unique hseries
  rw [hkernelEq]
  exact ((hplusRep.sub hkernelRep).sub hTRep).smul (1 / 2 : ℝ)

/-- The literal centered residual kernel from the compact BJR statement.
Its degree terms are exactly `-square (d-1)`. -/
def residualKernel (M : CompactBJRModel S) : C(S × S, ℝ) :=
  M.iteratedKernelMap 1 - M.kernel.toContinuousMap - square (M.degreeFunction - 1)

theorem residualKernel_apply (M : CompactBJRModel S) (x y : S) :
    residualKernel M (x, y) = (∫ z, M.kernel x z * M.kernel z y ∂M.mu) - M.kernel x y -
      M.degreeFunction x * M.degreeFunction y + M.degreeFunction x + M.degreeFunction y - 1 := by
  change M.iteratedKernelMap 1 (x, y) - M.kernel x y -
    (M.degreeFunction x - 1) * (M.degreeFunction y - 1) = _
  rw [M.iteratedKernelMap_apply 1]
  change (∫ z, M.kernel x z * M.kernel z y ∂M.mu) - M.kernel x y -
    (M.degreeFunction x - 1) * (M.degreeFunction y - 1) = _
  ring

/-- Assumption QP alone implies the genuine projective representation of
the actual BJR residual kernel; no moment or representation interface is
postulated for the residual. -/
theorem residualKernel_hasRepresentation (M : CompactBJRModel S) (hQP : M.QP) :
    HasRepresentation (residualKernel M) :=
  ((kernelSquare_hasRepresentation M hQP).sub hQP).sub
    (hasRepresentation_square (M.degreeFunction - 1))

end PerronWright.ProjectiveKernelClosure
