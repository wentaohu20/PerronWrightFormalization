import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Order.Partition.Finpartition

/-!
# Product measures and integrals over finite partition blocks

An equivalence rearranges coordinates indexed by a finite set into vectors
indexed by the blocks of a `Finpartition`. It preserves the corresponding
product measures, so an integrand factored by blocks has a factored integral.
This lemma is independent of the graph and applies to the root-deleted tree
partition in the finite rooted-tree expansion.
-/

open MeasureTheory
open scoped Classical

namespace PerronWright

theorem measurePreserving_piCurry_symm
    {ι : Type*} {κ : ι → Type*} [Fintype ι] [∀ i, Fintype (κ i)]
    {X : (i : ι) → κ i → Type*} [∀ i j, MeasurableSpace (X i j)]
    (μ : (p : Σ i, κ i) → Measure (X p.1 p.2))
    [∀ p, SigmaFinite (μ p)] :
    MeasurePreserving (MeasurableEquiv.piCurry X).symm
      (Measure.pi (fun i => Measure.pi (fun j => μ ⟨i, j⟩)))
      (Measure.pi μ) := by
  let e := (MeasurableEquiv.piCurry X).symm
  refine ⟨e.measurable, (Measure.pi_eq fun s _ => ?_).symm⟩
  have hpre : e ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s ⟨i, j⟩)) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro hf i j
      exact hf ⟨i, j⟩
    · intro hf ⟨i, j⟩
      exact hf i j
  rw [e.map_apply, hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_sigma (fun p => μ p (s p))).symm

noncomputable def finpartitionCoordEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι)) :
    ι ≃ Σ B : P.parts, B.1 :=
  (Equiv.subtypeUnivEquiv (fun i : ι => Finset.mem_univ i)).symm.trans
    P.equivSigmaParts

noncomputable def finpartitionPiMeasurableEquiv
    {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]
    (P : Finpartition (Finset.univ : Finset ι)) :
    (ι → S) ≃ᵐ ((B : P.parts) → B.1 → S) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : Σ B : P.parts, B.1 => S) (finpartitionCoordEquiv P)).trans
      (MeasurableEquiv.piCurry (fun (B : P.parts) (_ : B.1) => S))

theorem finpartitionPiMeasurableEquiv_apply
    {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]
    (P : Finpartition (Finset.univ : Finset ι))
    (z : ι → S) (B : P.parts) (i : B.1) :
    finpartitionPiMeasurableEquiv P z B i = z i.1 := by
  change (MeasurableEquiv.piCongrLeft
    (fun _ : Σ B : P.parts, B.1 => S) (finpartitionCoordEquiv P) z) ⟨B, i⟩ = z i.1
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  simp only [eq_rec_constant]
  rfl

theorem measurePreserving_finpartitionPi
    {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]
    (P : Finpartition (Finset.univ : Finset ι))
    (μ : Measure S) [SigmaFinite μ] :
    MeasurePreserving (finpartitionPiMeasurableEquiv P)
      (Measure.pi (fun _ : ι => μ))
      (Measure.pi (fun B : P.parts => Measure.pi (fun _ : B.1 => μ))) := by
  have hcur : MeasurePreserving
      (MeasurableEquiv.piCurry (fun (B : P.parts) (_ : B.1) => S))
      (Measure.pi (fun _ : Σ B : P.parts, B.1 => μ))
      (Measure.pi (fun B : P.parts => Measure.pi (fun _ : B.1 => μ))) :=
    (measurePreserving_piCurry_symm
      (X := fun (B : P.parts) (_ : B.1) => S)
      (fun _ : Σ B : P.parts, B.1 => μ)).symm
  have hcongr : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Σ B : P.parts, B.1 => S) (finpartitionCoordEquiv P))
      (Measure.pi (fun _ : ι => μ))
      (Measure.pi (fun _ : Σ B : P.parts, B.1 => μ)) :=
    measurePreserving_piCongrLeft
      (fun _ : Σ B : P.parts, B.1 => μ) (finpartitionCoordEquiv P)
  exact hcur.comp hcongr

theorem integral_finpartition_prod_eq_prod
    {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]
    (P : Finpartition (Finset.univ : Finset ι))
    (μ : Measure S) [SigmaFinite μ]
    (F : (B : P.parts) → (B.1 → S) → ℝ) :
    (∫ z : ι → S, ∏ B : P.parts, F B (fun i => z i.1)
      ∂Measure.pi (fun _ : ι => μ)) =
      ∏ B : P.parts, ∫ y : B.1 → S, F B y
        ∂Measure.pi (fun _ : B.1 => μ) := by
  calc
    _ = ∫ u : (B : P.parts) → B.1 → S, ∏ B : P.parts, F B (u B)
        ∂Measure.pi (fun B : P.parts => Measure.pi (fun _ : B.1 => μ)) := by
      rw [← (measurePreserving_finpartitionPi P μ).integral_comp']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        apply Finset.prod_congr rfl
        intro B _
        congr 1
        funext i
        exact (finpartitionPiMeasurableEquiv_apply P z B i).symm)
    _ = _ := integral_fintype_prod_eq_prod F

end PerronWright
