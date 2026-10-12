import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod

/-! # Proved Haar product factorization of invariant finite joint laws

For each measurable second-coordinate event, its restricted first
marginal is a genuine finite invariant measure. Haar uniqueness and
total-mass normalization identify it, and measurable rectangles identify
the joint measure. This is a proved theorem, not a probability interface.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped Classical ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.InvariantHaarJointProduct

variable {G Y : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace Y]

theorem invariant_joint_eq_haar_prod (H : Measure G) [IsAddHaarMeasure H] [IsProbabilityMeasure H]
    (ν : Measure (G × Y)) [IsFiniteMeasure ν]
    (hinv : ∀ g : G, ν.map (fun p ↦ (g+p.1,p.2)) = ν) :
    ν = H.prod (ν.map Prod.snd) := by
  apply Measure.ext_prod
  intro A B hA hB
  let ρ : Measure G := (ν.restrict (Prod.snd ⁻¹' B)).map Prod.fst
  have hρ (C : Set G) (hC : MeasurableSet C) : ρ C = ν (C ×ˢ B) := by
    rw [Measure.map_apply measurable_fst hC,Measure.restrict_apply (measurable_fst hC)]
    congr 1
  let : IsAddLeftInvariant ρ := ⟨fun g ↦ by
    ext C hC
    rw [Measure.map_apply (by fun_prop) hC,hρ _ (hC.preimage (by fun_prop)),hρ C hC]
    have he := congrArg (fun m : Measure (G × Y) ↦ m (C ×ˢ B)) (hinv g)
    rw [Measure.map_apply (by fun_prop) (hC.prod hB)] at he
    have hset : (fun p : G × Y ↦ (g+p.1,p.2)) ⁻¹' (C ×ˢ B) = ((fun x ↦ g+x) ⁻¹' C) ×ˢ B := by
      ext p
      rfl
    rw [hset] at he
    exact he⟩
  have hscale := Measure.isAddLeftInvariant_eq_smul ρ H
  have hmass := congrArg (fun m : Measure G ↦ m univ) hscale
  simp only [Measure.coe_nnreal_smul_apply,measure_univ,mul_one] at hmass
  have hvalue := congrArg (fun m : Measure G ↦ m A) hscale
  simp only [Measure.coe_nnreal_smul_apply] at hvalue
  rw [Measure.prod_prod,Measure.map_apply measurable_snd hB]
  rw [← hρ A hA,hvalue,← hmass,hρ univ MeasurableSet.univ]
  have hset : (univ : Set G) ×ˢ B = (Prod.snd : G × Y → Y) ⁻¹' B := by
    ext p
    simp only [mem_prod,mem_univ,true_and,mem_preimage]
  rw [hset,mul_comm]

end PerronWright.InvariantHaarJointProduct
