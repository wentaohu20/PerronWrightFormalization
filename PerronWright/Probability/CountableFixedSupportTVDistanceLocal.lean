import PerronWright.Probability.CountableTVDistanceTests
import PerronWright.Probability.CountableFixedSupportTVLocal
import PerronWright.Probability.CountableFixedSupportVaryingLocal
import PerronWright.Probability.CountableFixedSupportSequentialParameter

/-! # Actual fixed-support TV-distance errors uniformly in the parameter

The bounded distance test vanishes on the genuine retained Perron mark.
The actual varying-parameter finite theorem and exact graph-law identity
therefore give a uniform zero limit, including bounded parameter intervals.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open CountableVariationMarks FiniteProbabilityVariationEmbedding

def fixedSupportDistanceLocalExpectation (M : CountableKernel) (m : ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (n : ℕ) (y : Fin 1 → ℝ) (r : Fin 1 → ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
    ∫ G, CountableVariationComponentCounts.markedCount
      (CountableTypeRealization.vertexTypes M m (n + 1)) G
      (fun i ↦ CriticalScaling.size (y i) (n + 1)) r
      (distanceTest (M.fixedSupportPerronMark m hlower hlo))
      ∂M.empiricalNormalizedGraphLaw (fun _ ↦ m) lambda hlower hlo n

theorem fixedSupportDistanceLocalExpectation_nonneg
    (M : CountableKernel) (m : ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (n : ℕ) (y : Fin 1 → ℝ) (r : Fin 1 → ℕ) :
    0 ≤ M.fixedSupportDistanceLocalExpectation m lambda hlower hlo n y r := by
  apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
  exact integral_nonneg (fun _ ↦ CountableVariationComponentCounts.markedCount_distance_nonneg _ _ _ _ _)

theorem fixedSupport_varying_distance_local_zero
    (M : CountableKernel) (m R : ℕ) (ell : ℕ → ℝ) (lambda a b : ℝ)
    (hl : Tendsto ell atTop (𝓝 lambda)) (ha : 0 < a) (hb : 0 ≤ b)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      M.fixedSupportDistanceLocalExpectation m (ell n) hlower hlo n y r < ε := by
  let F := M.fixedSupportModel m hlower hlo
  let hF : F.IsCritical := M.fixedSupportModel_isCritical m hlower hlo
  let f : Finset.range (m + 1) → ℕ := fun s ↦ s.val
  let c : ℕ → (Finset.range (m + 1)) → ℕ := fun N ↦
    FiniteIrreducibleTypePlacementMultiplicity.fiberCount (M.fixedSupportVertexTypes m N)
  let Ψ := distanceTest (M.fixedSupportPerronMark m hlower hlo)
  have hround : ∀ᶠ N in atTop, ∀ s, |(c N s : ℝ) - (N : ℝ) * F.weight s| ≤ 2 * (m + 1 : ℝ) :=
    Eventually.of_forall (fun N s ↦ M.fixedSupportVertexTypes_rounding_bound m N hlower hlo s)
  have h := FiniteIrreducibleVaryingMarkedLocalMain.eventually_uniform_floor_marked_factorial_density
    F hF 1 R (by norm_num) (M.fixedSupportVaryingEffectiveParameter m ell) lambda a b
    (M.fixedSupportVaryingEffectiveParameter_tendsto m ell lambda hl hlower hlo) ha hb c
    (2 * (m + 1 : ℝ)) (by positivity) hround
    (fun ν ↦ Ψ (fun i ↦ embed f (ν i)))
    (continuous_coupled_test f Ψ (continuous_distanceTest _)) hε
  filter_upwards [(tendsto_add_atTop_nat 1).eventually h] with n hn
  intro y r hya hyb hr
  have he := hn (M.fixedSupportVertexTypes m (n + 1)) (fun _ ↦ rfl) y r hya hyb hr
  unfold FiniteIrreducibleMarkedLocalMain.scaledMarkedFactorialExpectation at he
  simp only [FiniteIrreducibleNativeMarkConcentration.perronMarks] at he
  have hz : Ψ (fun _ ↦ embed f (FiniteIrreducibleConnectedTypeLaw.perronLaw F hF)) = 0 := by
    exact distanceTest_self _
  rw [hz, mul_zero, sub_zero] at he
  norm_num only [Nat.cast_one, mul_one] at he
  change |((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
    (∫ G, AnnealedMarkedFactorialCounting.markedCount (M.fixedSupportVertexTypes m (n + 1)) G
      (fun i ↦ CriticalScaling.size (y i) (n + 1)) r
      (fun ν ↦ Ψ (fun i ↦ embed f (ν i)))
      ∂FiniteIrreducibleComponentProcess.graphLaw F
        (M.fixedSupportVaryingEffectiveParameter m ell (n + 1)) (n + 1)
        (M.fixedSupportVertexTypes m (n + 1)))| < ε at he
  have hp : M.fixedSupportVaryingEffectiveParameter m ell (n + 1) =
      M.fixedSupportEffectiveParameter m (ell n) (n + 1) := by
    simp only [fixedSupportVaryingEffectiveParameter, Nat.add_sub_cancel, fixedSupportEffectiveParameter]
  rw [hp, M.fixedSupportModel_graphLaw_eq_actual m n (ell n) hlower hlo] at he
  simp only [← CountableVariationComponentCounts.markedCount_map_types] at he
  have hnz := M.fixedSupportDistanceLocalExpectation_nonneg m (ell n) hlower hlo n y r
  change |M.fixedSupportDistanceLocalExpectation m (ell n) hlower hlo n y r| < ε at he
  rwa [abs_of_nonneg hnz] at he

theorem fixedSupport_eventually_uniform_parameter_distance_local_zero
    (M : CountableKernel) (m R : ℕ) (a b L : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      M.fixedSupportDistanceLocalExpectation m lambda hlower hlo n y r < ε := by
  have h := CountableFixedSupportSequentialParameter.eventually_forall_compact_parameters
    (K := Set.Icc (-L) L) isCompact_Icc
    (fun n lambda ↦ ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      M.fixedSupportDistanceLocalExpectation m lambda hlower hlo n y r < ε)
    (fun ell lambda _ hl ↦ M.fixedSupport_varying_distance_local_zero
      m R ell lambda a b hl ha hb hlower hlo hε)
  filter_upwards [h] with n hn lambda hl
  exact hn lambda (abs_le.mp hl)

end PerronWright.CountableKernel
