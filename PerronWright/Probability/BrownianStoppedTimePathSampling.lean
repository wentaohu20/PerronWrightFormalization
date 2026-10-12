import PerronWright.Probability.BrownianMinimumSplitSampling

/-! # Finite tests determine a whole path tagged by its stopping time

This is a consequence of the proved rational-evaluation Borel embedding
for the actual continuous path space. A dummy second tagged path allows
reuse of the full minimum-split uniqueness proof; mapping back the first
coordinate proves equality of the genuine tagged-path measures.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianStoppedTimePathSampling

open BrownianPathLaw

def sample {n : ℕ} (σ : Fin n → ℝ≥0) (q : ℝ≥0 × Path) : ℝ≥0 × (Fin n → ℝ) :=
  (q.1,fun i ↦ q.2 (σ i))

theorem continuous_sample {n : ℕ} (σ : Fin n → ℝ≥0) : Continuous (sample σ) :=
  continuous_fst.prodMk (continuous_pi (fun i ↦ (continuous_eval (σ i)).comp continuous_snd))

theorem ext_of_finite_sample_tests (μ ν : Measure (ℝ≥0 × Path))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (n : ℕ) (σ : Fin n → ℝ≥0) (Ψ : (ℝ≥0 × (Fin n → ℝ)) →ᵇ ℝ≥0),
      (∫⁻ q, Ψ (sample σ q) ∂μ) = ∫⁻ q, Ψ (sample σ q) ∂ν) : μ = ν := by
  let z : Path := ⟨fun _ ↦ 0,continuous_const⟩
  let J : (ℝ≥0 × Path) → (ℝ≥0 × Path) × (ℝ × Path) :=
    fun q ↦ (q,(0,z))
  have hJ : Measurable J := measurable_id.prodMk measurable_const
  have he : μ.map J = ν.map J := by
    apply BrownianMinimumSplitSampling.ext_of_finite_sample_tests
    intro m n σ τ Ψ
    let C : C(ℝ≥0 × (Fin m → ℝ),
        (ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) :=
      ⟨fun x ↦ (x,(0,fun _ ↦ 0)),continuous_id.prodMk continuous_const⟩
    have hm := Ψ.continuous.measurable.coe_nnreal_ennreal.comp
      (BrownianMinimumSplitSampling.continuous_sample σ τ).measurable
    change (∫⁻ x, ((fun u ↦ (Ψ u : ℝ≥0∞)) ∘
      BrownianMinimumSplitSampling.sample σ τ) x ∂μ.map J) =
      ∫⁻ x, ((fun u ↦ (Ψ u : ℝ≥0∞)) ∘
        BrownianMinimumSplitSampling.sample σ τ) x ∂ν.map J
    rw [lintegral_map hm hJ,lintegral_map hm hJ]
    change (∫⁻ q, (Ψ ((q.1,fun i ↦ q.2 (σ i)),(0,fun _ ↦ 0)) : ℝ≥0∞) ∂μ) =
      ∫⁻ q, (Ψ ((q.1,fun i ↦ q.2 (σ i)),(0,fun _ ↦ 0)) : ℝ≥0∞) ∂ν
    simpa only [sample,BoundedContinuousFunction.compContinuous_apply,C,ContinuousMap.coe_mk] using
      h m σ (Ψ.compContinuous C)
  have hf := congrArg (Measure.map (Prod.fst : ((ℝ≥0 × Path) × (ℝ × Path)) → ℝ≥0 × Path)) he
  rw [Measure.map_map measurable_fst hJ,Measure.map_map measurable_fst hJ] at hf
  change μ.map id = ν.map id at hf
  simpa only [Measure.map_id] using hf

end PerronWright.BrownianStoppedTimePathSampling
