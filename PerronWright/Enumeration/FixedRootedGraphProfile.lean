import PerronWright.Enumeration.TreeRootBlockRelabel
import PerronWright.Enumeration.TreeCoefficientContinuous

/-!
# A fixed rooted graph as a type-resolved kernel profile

For one genuine labelled graph, fix the type at one distinguished vertex
and integrate all other vertex types against the product type law.  The
resulting continuous function is its concrete zero-field rooted profile.
The parent-kernel-weighted full graph integral is then exactly the kernel
action on this profile.

The final corollary applies this identity to the actual relabelled tree block
appearing in `tree_rootBlock_integral_relabel`.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The concrete type-resolved zero-field weight of one fixed labelled graph,
rooted at `v`.  The remaining `n` type variables are integrated out. -/
def CompactBJRModel.fixedRootedGraphProfile
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) (x : S) : ℝ :=
  ∫ z : Fin n → S,
    M.fieldGraphWeightIntegrand 0 H (Fin.insertNth v x z)
      ∂Measure.pi (fun _ : Fin n => M.mu)

theorem CompactBJRModel.fixedRootedGraphProfile_continuous
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    Continuous (M.fixedRootedGraphProfile H v) := by
  have hins : Continuous
      (fun p : S × (Fin n → S) ↦
        (Fin.insertNth (α := fun _ ↦ S) v p.1 p.2 : Fin (n + 1) → S)) := by
    apply continuous_pi
    intro j
    by_cases hj : j = v
    · subst j
      simpa only [Fin.insertNth_apply_same] using
        (continuous_fst : Continuous (fun p : S × (Fin n → S) ↦ p.1))
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      simpa only [Fin.insertNth_apply_succAbove] using
        (show Continuous (fun p : S × (Fin n → S) ↦ p.2 k) by fun_prop)
  have hjoint : Continuous
      (fun p : S × (Fin n → S) ↦
        M.fieldGraphWeightIntegrand 0 H (Fin.insertNth v p.1 p.2)) :=
    (M.fieldGraphWeightIntegrand_continuous 0 H).comp hins
  have hc := continuous_parametric_integral_of_continuous
    (μ := Measure.pi (fun _ : Fin n => M.mu))
    (f := fun x : S => fun z : Fin n → S ↦
      M.fieldGraphWeightIntegrand 0 H (Fin.insertNth v x z))
    hjoint isCompact_univ
  change Continuous (fun x : S => ∫ z : Fin n → S,
    M.fieldGraphWeightIntegrand 0 H (Fin.insertNth v x z)
      ∂Measure.pi (fun _ : Fin n => M.mu))
  simpa only [setIntegral_univ] using hc

/-- The fixed rooted-graph profile as a continuous function of the
parent-facing root type. -/
def CompactBJRModel.fixedRootedGraphProfileMap
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) : C(S, ℝ) :=
  ⟨M.fixedRootedGraphProfile H v,
    M.fixedRootedGraphProfile_continuous H v⟩

@[simp] theorem CompactBJRModel.fixedRootedGraphProfileMap_apply
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) (x : S) :
    M.fixedRootedGraphProfileMap H v x =
      M.fixedRootedGraphProfile H v x := rfl

/-- Integrating a parent-kernel factor against the genuine zero-field weight
of one fixed rooted graph is exactly the kernel action on its concrete
type-resolved profile. -/
theorem CompactBJRModel.parentKernelWeightedGraphIntegral_eq_action
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) (root : S) :
    (∫ x : Fin (n + 1) → S,
        M.kernel root (x v) * M.fieldGraphWeightIntegrand 0 H x
        ∂Measure.pi (fun _ : Fin (n + 1) => M.mu)) =
      M.kernel.action M.mu (M.fixedRootedGraphProfileMap H v) root := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ S) v
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => M.mu))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => M.mu) v
  have hcont : Continuous
      (fun x : Fin (n + 1) → S ↦
        M.kernel root (x v) * M.fieldGraphWeightIntegrand 0 H x) := by
    exact (M.kernel.toContinuousMap.continuous.comp
      (continuous_const.prodMk (continuous_apply v))).mul
        (M.fieldGraphWeightIntegrand_continuous 0 H)
  have hf : Integrable
      (fun x : Fin (n + 1) → S ↦
        M.kernel root (x v) * M.fieldGraphWeightIntegrand 0 H x)
      (Measure.pi (fun _ : Fin (n + 1) => M.mu)) :=
    hcont.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hprod : Integrable
      (fun p : S × (Fin n → S) ↦
        M.kernel root ((e.symm p) v) *
          M.fieldGraphWeightIntegrand 0 H (e.symm p))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  rw [M.kernel.action_apply]
  calc
    _ = ∫ p : S × (Fin n → S),
          M.kernel root ((e.symm p) v) *
            M.fieldGraphWeightIntegrand 0 H (e.symm p)
          ∂M.mu.prod (Measure.pi (fun _ : Fin n => M.mu)) := by
      exact (hmp.symm.integral_comp'
        (fun x : Fin (n + 1) → S ↦
          M.kernel root (x v) * M.fieldGraphWeightIntegrand 0 H x)).symm
    _ = ∫ y : S, ∫ z : Fin n → S,
          M.kernel root y *
            M.fieldGraphWeightIntegrand 0 H (Fin.insertNth v y z)
          ∂Measure.pi (fun _ : Fin n => M.mu) ∂M.mu := by
      rw [integral_prod _ hprod]
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same]
    _ = ∫ y : S,
          M.kernel root y * M.fixedRootedGraphProfileMap H v y ∂M.mu := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [CompactBJRModel.fixedRootedGraphProfileMap_apply,
        CompactBJRModel.fixedRootedGraphProfile]
      exact integral_const_mul _ _

/-- The same concrete profile, stated for a graph on an arbitrary nonempty
`Fin k`.  Its distinguished vertex supplies the proof that the zero case is
impossible; in the successor case this is exactly
`fixedRootedGraphProfileMap`. -/
def CompactBJRModel.fixedRootedFinGraphProfileMap
    (M : CompactBJRModel S) {k : ℕ}
    (H : SimpleGraph (Fin k)) (v : Fin k) : C(S, ℝ) := by
  cases k with
  | zero => exact Fin.elim0 v
  | succ n => exact M.fixedRootedGraphProfileMap H v

theorem CompactBJRModel.parentKernelWeightedFinGraphIntegral_eq_action
    (M : CompactBJRModel S) {k : ℕ}
    (H : SimpleGraph (Fin k)) (v : Fin k) (root : S) :
    (∫ x : Fin k → S,
        M.kernel root (x v) * M.fieldGraphWeightIntegrand 0 H x
        ∂Measure.pi (fun _ : Fin k => M.mu)) =
      M.kernel.action M.mu (M.fixedRootedFinGraphProfileMap H v) root := by
  cases k with
  | zero => exact Fin.elim0 v
  | succ n =>
      simpa only [CompactBJRModel.fixedRootedFinGraphProfileMap] using
        M.parentKernelWeightedGraphIntegral_eq_action H v root

/-- The concrete type-resolved zero-field profile of the relabelled
root-deleted block tree containing `i`, rooted at its unique vertex adjacent
to the deleted parent. -/
def CompactBJRModel.relabelledRootBlockTreeProfileMap
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (i : Fin n) : C(S, ℝ) :=
  M.fixedRootedFinGraphProfileMap
    (finRootlessBlockTreeGraph n H i)
    (((finRootlessPartition n H).part i).equivFin
      ⟨i, (finRootlessPartition n H).mem_part_self.mpr
        (Finset.mem_univ i)⟩)

/-- The genuine integral of one root-deleted block is exactly the parent
kernel acting on the concrete zero-field rooted profile of its relabelled
block tree. -/
theorem CompactBJRModel.tree_rootBlock_integral_eq_kernel_action
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (i : Fin n) (hi : H.Adj 0 i.succ) (root : S) :
    (∫ y : ((finRootlessPartition n H).part i) → S,
      M.rootBlockWeightIntegrand H ((finRootlessPartition n H).part i)
        (Fin.cons root
          (extendBlock ((finRootlessPartition n H).part i) root y))
        ∂Measure.pi
          (fun _ : ((finRootlessPartition n H).part i) => M.mu)) =
      M.kernel.action M.mu
        (M.relabelledRootBlockTreeProfileMap H i) root := by
  rw [M.tree_rootBlock_integral_relabel H hT i hi root]
  simpa only [CompactBJRModel.relabelledRootBlockTreeProfileMap] using
    M.parentKernelWeightedFinGraphIntegral_eq_action
      (finRootlessBlockTreeGraph n H i)
      (((finRootlessPartition n H).part i).equivFin
        ⟨i, (finRootlessPartition n H).mem_part_self.mpr
          (Finset.mem_univ i)⟩) root

end PerronWright
