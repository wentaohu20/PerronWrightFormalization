import PerronWright.Probability.AnnealedProfileFunctionalExponent
import PerronWright.Probability.BoundedConcentrationTransfer
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Genuine bounded L1 concentration for annealed profile functionals

The time parameter may vary and the connected product sampling spaces
change with the sizes.  Compactness supplies the bound and the literal
pooled weak concentration supplies the event probabilities.  Neither an
integrability interface nor a random-moment limit is assumed.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedProfileFunctionalL1

open AnnealedProfileFunctionalContinuous AnnealedProfileFunctionalExponent
  EmpiricalTypeMarks EmpiricalMarkConcentration EmpiricalMarkWeakConcentration
  ProjectiveFiniteCollection ProfileFiniteCollection BoundedConcentrationTransfer
  AnnealedTupleResidualCounting

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]
variable {T : Type*} [TopologicalSpace T]

theorem pooled_jointContinuousFunctional_measurable {q : ℕ} (hq : 0 < q)
    (k : Fin q → ℕ) (hk : ∀ i, 0 < k i) (t : T)
    (F : T → ProbabilityMeasure S → ℝ)
    (hF : Continuous (fun z : T × ProbabilityMeasure S ↦ F z.1 z.2)) :
    Measurable (fun p : StateFamily (S := S) k ↦ F t (pooledMark hq k hk p)) := by
  have hc : Continuous (fun x : Fin (Fintype.card (SelectedVertices k)) → S ↦
      F t (typesMark (pooled_card_pos hq k hk) x)) :=
    hF.comp (continuous_const.prodMk (typesMark_continuous (pooled_card_pos hq k hk)))
  exact hc.measurable.comp (pooledTypes_measurable k)

/-- A convergent deterministic time sequence has compact closure.  On
its product with the actual weak probability-measure space every joint
continuous observable is uniformly bounded. -/
theorem jointContinuousFunctional_bound (t : ℕ → T) {t₀ : T}
    (ht : Tendsto t atTop (𝓝 t₀)) (ν₀ : ProbabilityMeasure S)
    (F : T → ProbabilityMeasure S → ℝ)
    (hF : Continuous (fun z : T × ProbabilityMeasure S ↦ F z.1 z.2)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n ν, |F (t n) ν - F t₀ ν₀| ≤ B := by
  have hc : IsCompact (insert t₀ (Set.range t)) := ht.isCompact_insert_range
  have hp := hc.prod (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure S)))
  obtain ⟨B,hB,hbound⟩ := (hp.image_of_continuousOn hF.continuousOn).isBounded.exists_pos_norm_le
  refine ⟨B + |F t₀ ν₀|,by positivity,?_⟩
  intro n ν
  have hn : (t n,ν) ∈ insert t₀ (Set.range t) ×ˢ (Set.univ : Set (ProbabilityMeasure S)) :=
    ⟨Set.mem_insert_of_mem _ (Set.mem_range_self n),Set.mem_univ ν⟩
  have hb := hbound _ (Set.mem_image_of_mem _ hn)
  have hb' : |F (t n) ν| ≤ B := by simpa only [Real.norm_eq_abs] using hb
  exact (abs_sub (F (t n) ν) (F t₀ ν₀)).trans (by linarith only [hb'])

/-- Literal probability concentration for a jointly continuous
observable, with an actual deterministic parameter tending to its limit. -/
theorem pooled_jointContinuousFunctional_probability_tendsto_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (R q : ℕ) (hq : 0 < q) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (g : ℕ → Fin q → C(S,ℝ))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i))
    (hKTop : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i : ℝ) * ‖g n i‖ ≤ L)
    (t : ℕ → T) {t₀ : T} (ht : Tendsto t atTop (𝓝 t₀))
    (F : T → ProbabilityMeasure S → ℝ)
    (hF : Continuous (fun z : T × ProbabilityMeasure S ↦ F z.1 z.2))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (productLaw M (k n) (r n) (g n) (hC n)).real
      {p | ε ≤ |F (t n) (pooledMark hq (k n) (hk n) p) - F t₀ (perronMark M hM)|})
      atTop (𝓝 0) := by
  let W := {z : T × ProbabilityMeasure S | |F z.1 z.2 - F t₀ (perronMark M hM)| < ε}
  have hW : W ∈ 𝓝 (t₀,perronMark M hM) := by
    apply (isOpen_lt (hF.sub continuous_const |>.abs) continuous_const).mem_nhds
    change |F t₀ (perronMark M hM) - F t₀ (perronMark M hM)| < ε
    simpa only [sub_self,abs_zero] using hε
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp hW
  have hp := pooledMark_probability_outside_weak_nhds_tendsto_zero
    M hM R q hq L hL k r hk g hC hKTop hr hg V hV
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hp
  filter_upwards [ht.eventually hU] with n hn
  apply measureReal_mono _ (measure_ne_top _ _)
  intro p hp
  by_contra hnot
  have hv : pooledMark hq (k n) (hk n) p ∈ V := by simpa using hnot
  have hh := hUV (show (t n,pooledMark hq (k n) (hk n) p) ∈ U ×ˢ V from ⟨hn,hv⟩)
  change |F (t n) (pooledMark hq (k n) (hk n) p) - F t₀ (perronMark M hM)| < ε at hh
  exact (not_lt_of_ge hp) hh

/-- Terminal L1 bridge under the actual product connected law.  All
boundedness, measurability, and probability hypotheses are proved above. -/
theorem pooled_jointContinuousFunctional_l1_tendsto_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (R q : ℕ) (hq : 0 < q) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (g : ℕ → Fin q → C(S,ℝ))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i))
    (hKTop : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i : ℝ) * ‖g n i‖ ≤ L)
    (t : ℕ → T) {t₀ : T} (ht : Tendsto t atTop (𝓝 t₀))
    (F : T → ProbabilityMeasure S → ℝ)
    (hF : Continuous (fun z : T × ProbabilityMeasure S ↦ F z.1 z.2)) :
    Tendsto (fun n ↦ ∫ p,
      |F (t n) (pooledMark hq (k n) (hk n) p) - F t₀ (perronMark M hM)|
        ∂productLaw M (k n) (r n) (g n) (hC n)) atTop (𝓝 0) := by
  obtain ⟨B,hB,hbound⟩ := jointContinuousFunctional_bound t ht (perronMark M hM) F hF
  exact integral_abs_tendsto_zero
    (fun n ↦ productLaw M (k n) (r n) (g n) (hC n))
    (fun n p ↦ F (t n) (pooledMark hq (k n) (hk n) p) - F t₀ (perronMark M hM))
    (fun n ↦ (pooled_jointContinuousFunctional_measurable hq (k n) (hk n) (t n) F hF).sub
      measurable_const) B hB (fun n p ↦ hbound n _)
    (pooled_jointContinuousFunctional_probability_tendsto_zero
      M hM R q hq L hL k r hk g hC hKTop hr hg t ht F hF)

end PerronWright.AnnealedProfileFunctionalL1
