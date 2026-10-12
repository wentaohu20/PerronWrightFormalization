import PerronWright.Probability.CountableVariationMarks
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Algebra.Module.Basic

/-! # The genuine total-variation mark space is Polish

The encoding of literal countable probability measures is exactly the
closed positive unit simplex of real ell-one. Completeness and a countable
dense linear span are proved here, rather than supplied as mark-space
interfaces. The metric remains the full atomic absolute variation metric.
-/

open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators Classical NNReal ENNReal
noncomputable section

namespace PerronWright.CountableVariationMarks

theorem isometry_encoding : Isometry encoding := fun _ _ ↦ rfl

theorem norm_encoding (p : VariationMark) : ‖encoding p‖ = 1 := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [encoding, ENNReal.toReal_one, Real.rpow_one, one_div_one,
    massVector_apply, Real.norm_of_nonneg measureReal_nonneg]
  exact (CountableKernel.probability_atomMass_hasSum (p.val : Measure ℕ)).tsum_eq

theorem range_encoding : Set.range encoding =
    {f : lp (fun _ : ℕ ↦ ℝ) 1 | (∀ a, 0 ≤ f a) ∧ ‖f‖ = 1} := by
  ext f
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨fun _ ↦ measureReal_nonneg, norm_encoding p⟩
  · rintro ⟨hf, hnorm⟩
    have hs : HasSum (fun a : ℕ ↦ f a) 1 := by
      have h := lp.hasSum_norm (by norm_num : 0 < (1 : ℝ≥0∞).toReal) f
      simpa only [ENNReal.toReal_one, Real.rpow_one, hnorm,
        Real.norm_of_nonneg (hf _)] using h
    let μ : Measure ℕ := Measure.sum (fun a ↦ ENNReal.ofReal (f a) • Measure.dirac a)
    have hμ : IsProbabilityMeasure μ := hs.isProbabilityMeasure_sum_dirac hf
    refine ⟨ofProbability ⟨μ, hμ⟩, ?_⟩
    apply lp.ext
    funext a
    change μ.real {a} = f a
    rw [measureReal_def, Measure.sum_smul_dirac_singleton, ENNReal.toReal_ofReal (hf a)]

theorem isClosed_range_encoding : IsClosed (Set.range encoding) := by
  rw [range_encoding]
  have hc : IsClosed {f : lp (fun _ : ℕ ↦ ℝ) 1 | ∀ a, 0 ≤ f a} := by
    have he : {f : lp (fun _ : ℕ ↦ ℝ) 1 | ∀ a, 0 ≤ f a} =
        ⋂ a : ℕ, {f | 0 ≤ f a} := by ext f; simp
    rw [he]
    exact isClosed_iInter (fun a ↦ isClosed_le continuous_const
      (lp.evalCLM ℝ (fun _ : ℕ ↦ ℝ) (1 : ℝ≥0∞) a).continuous)
  exact hc.inter (isClosed_eq continuous_norm continuous_const)

instance variationMarkComplete : CompleteSpace VariationMark := by
  rw [completeSpace_iff_isComplete_range isometry_encoding.isUniformInducing]
  exact isClosed_range_encoding.isComplete

private theorem ellOne_separable : SeparableSpace (lp (fun _ : ℕ ↦ ℝ) 1) := by
  let dirs : Set (lp (fun _ : ℕ ↦ ℝ) 1) :=
    Set.range (fun a : ℕ ↦ lp.single (E := fun _ : ℕ ↦ ℝ) (1 : ℝ≥0∞) a (1 : ℝ))
  have hs : IsSeparable (Submodule.span ℝ dirs : Set (lp (fun _ : ℕ ↦ ℝ) 1)) :=
    (Set.countable_range (fun a : ℕ ↦
      lp.single (E := fun _ : ℕ ↦ ℝ) (1 : ℝ≥0∞) a (1 : ℝ))).isSeparable.span
  apply isSeparable_univ_iff.mp
  apply hs.closure.mono
  intro f _
  apply mem_closure_of_tendsto (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) f)
  filter_upwards [] with s
  apply Submodule.sum_mem
  intro a _
  have he : lp.single (E := fun _ : ℕ ↦ ℝ) (1 : ℝ≥0∞) a (f a) =
      (f a) • lp.single (E := fun _ : ℕ ↦ ℝ) (1 : ℝ≥0∞) a (1 : ℝ) := by
    rw [← lp.single_smul]
    simp
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

instance variationMarkSecondCountable : SecondCountableTopology VariationMark := by
  let : SeparableSpace (lp (fun _ : ℕ ↦ ℝ) 1) := ellOne_separable
  exact isometry_encoding.isEmbedding.secondCountableTopology

instance variationMarkPolish : PolishSpace VariationMark := by infer_instance

theorem continuous_atom_mass (a : ℕ) :
    Continuous (fun p : VariationMark ↦ (p.val : Measure ℕ).real {a}) :=
  (lp.evalCLM ℝ (fun _ : ℕ ↦ ℝ) (1 : ℝ≥0∞) a).continuous.comp
    isometry_encoding.continuous

end PerronWright.CountableVariationMarks
