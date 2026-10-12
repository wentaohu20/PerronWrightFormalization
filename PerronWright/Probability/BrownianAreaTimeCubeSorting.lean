import PerronWright.Probability.BrownianPositiveBridgeAreaOrderedTimes
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Data.Fintype.Perm

/-! # Actual time-cube sorting and its factorial Jacobian

Distinct-coordinate chambers partition the actual area time cube almost
everywhere. Coordinate permutations preserve its product measure, so
integration of sorted time tuples is exactly factorial times integration
over the strictly ordered chamber. No ordered-integral identity is assumed.
-/

open MeasureTheory Filter Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianAreaTimeCubeSorting

open BrownianPositiveBridgeAreaTimeMoments BrownianPositiveBridgeAreaOrderedTimes

theorem measurableSet_strictMono (d : ℕ) :
    MeasurableSet {τ : Fin d → ℝ | StrictMono τ} := by
  have he : {τ : Fin d → ℝ | StrictMono τ} =
      ⋂ i : Fin d, ⋂ j : Fin d, {τ | i < j → τ i < τ j} := by
    ext τ
    simp only [mem_ofPred_eq,mem_iInter,StrictMono]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i < j
  · simpa only [hij,true_implies] using
      (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j))
  · simp only [hij,false_implies,ofPred_true,MeasurableSet.univ]

theorem timeCube_perm_preserving (d : ℕ) (T : ℝ≥0) (σ : Equiv.Perm (Fin d)) :
    MeasurePreserving (fun τ : Fin d → ℝ ↦ τ ∘ σ) (timeCube T d) (timeCube T d) := by
  convert! (measurePreserving_piCongrLeft
    (fun _ : Fin d ↦ volume.restrict (Ioc (0 : ℝ) (T : ℝ))) σ.symm) using 1
  ext τ i
  simpa only [Equiv.symm_apply_apply,Function.comp_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin d ↦ ℝ) σ.symm τ (σ i)).symm

theorem strictMono_sort_of_injective {d : ℕ} (τ : Fin d → ℝ)
    (hτ : Function.Injective τ) : StrictMono (τ ∘ Tuple.sort τ) :=
  (Tuple.monotone_sort τ).strictMono_iff_injective.mpr
    (hτ.comp (Tuple.sort τ).injective)

theorem perm_eq_sort_of_strictMono {d : ℕ} (τ : Fin d → ℝ)
    (hτ : Function.Injective τ) (σ : Equiv.Perm (Fin d))
    (hσ : StrictMono (τ ∘ σ)) : σ = Tuple.sort τ := by
  have he := Tuple.unique_monotone hσ.monotone (Tuple.monotone_sort τ)
  apply Equiv.ext
  intro i
  exact hτ (congrFun he i)

theorem sorted_test_eq_chamber_sum {d : ℕ} (τ : Fin d → ℝ)
    (hτ : Function.Injective τ) (F : (Fin d → ℝ) → ℝ≥0∞) :
    F (τ ∘ Tuple.sort τ) = ∑ σ : Equiv.Perm (Fin d),
      {r : Fin d → ℝ | StrictMono r}.indicator F (τ ∘ σ) := by
  symm
  rw [Finset.sum_eq_single (Tuple.sort τ)]
  · exact indicator_of_mem (strictMono_sort_of_injective τ hτ) F
  · intro σ _ hσ
    apply indicator_of_notMem
    intro hs
    exact hσ (perm_eq_sort_of_strictMono τ hτ σ hs)
  · simp

theorem lintegral_sorted_timeCube (d : ℕ) (T : ℝ≥0)
    (F : (Fin d → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ τ : Fin d → ℝ, F (τ ∘ Tuple.sort τ) ∂timeCube T d) =
      (d.factorial : ℝ≥0∞)*∫⁻ τ : Fin d → ℝ,
        {r : Fin d → ℝ | StrictMono r}.indicator F τ ∂timeCube T d := by
  have hm : Measurable ({r : Fin d → ℝ | StrictMono r}.indicator F) :=
    hF.indicator (measurableSet_strictMono d)
  calc
    _ = ∫⁻ τ : Fin d → ℝ, ∑ σ : Equiv.Perm (Fin d),
        {r : Fin d → ℝ | StrictMono r}.indicator F (τ ∘ σ) ∂timeCube T d := by
      apply lintegral_congr_ae
      filter_upwards [ae_timeCube_injective T d] with τ hτ
      exact sorted_test_eq_chamber_sum τ hτ F
    _ = ∑ σ : Equiv.Perm (Fin d), ∫⁻ τ : Fin d → ℝ,
        {r : Fin d → ℝ | StrictMono r}.indicator F (τ ∘ σ) ∂timeCube T d :=
      lintegral_finsetSum _ (fun σ _ ↦ hm.comp (timeCube_perm_preserving d T σ).measurable)
    _ = _ := by
      simp_rw [(timeCube_perm_preserving d T _).lintegral_comp hm]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,
        nsmul_eq_mul]

end PerronWright.BrownianAreaTimeCubeSorting
