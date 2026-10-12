import PerronWright.Probability.BrownianPathLaw
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! # Full minimum-split law is determined by literal finite samples

The stopped time and minimum level are retained in every test. Both actual
continuous paths embed through their rational evaluations. Finite bounded
continuous tests first determine their finite Borel laws, and projective
uniqueness then determines the whole tagged path law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumSplitSampling

open BrownianPathLaw BrownianGaussianSkeleton

def sample {m n : ℕ} (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
    (x : (ℝ≥0 × Path) × (ℝ × Path)) :
    (ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ)) :=
  ((x.1.1,fun i ↦ x.1.2 (σ i)),(x.2.1,fun j ↦ x.2.2 (τ j)))

theorem continuous_sample {m n : ℕ} (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0) :
    Continuous (sample σ τ) :=
  (continuous_fst.fst.prodMk (continuous_pi (fun i ↦
    (continuous_eval (σ i)).comp continuous_fst.snd))).prodMk
    (continuous_snd.fst.prodMk (continuous_pi (fun j ↦
      (continuous_eval (τ j)).comp continuous_snd.snd)))

private def LeftState : Option RationalTime → Type
  | none => ℝ≥0
  | some _ => ℝ

private def RightState : Option RationalTime → Type := fun _ ↦ ℝ

private instance leftMeasurable (i : Option RationalTime) : MeasurableSpace (LeftState i) := by
  cases i <;> dsimp [LeftState] <;> infer_instance

private instance rightMeasurable (i : Option RationalTime) : MeasurableSpace (RightState i) :=
  inferInstanceAs (MeasurableSpace ℝ)

private abbrev Index := Option RationalTime ⊕ Option RationalTime
private abbrev State : Index → Type := Sum.elim LeftState RightState

private instance stateMeasurable (i : Index) : MeasurableSpace (State i) := by
  cases i with
  | inl q => exact leftMeasurable q
  | inr q => exact rightMeasurable q

private def optionEquiv (α : Option RationalTime → Type)
    [∀ i, MeasurableSpace (α i)] :
    ((i : Option RationalTime) → α i) ≃ᵐ (α none × ((q : RationalTime) → α (some q))) where
  toEquiv := Equiv.piOptionEquivProd
  measurable_toFun := (measurable_pi_apply none).prodMk
    (measurable_pi_lambda _ (fun q ↦ measurable_pi_apply (some q)))
  measurable_invFun := by
    rw [measurable_pi_iff]
    intro q
    cases q with
    | none => exact measurable_fst
    | some q => exact (measurable_pi_apply q).comp measurable_snd

private def packedEquiv : ((i : Index) → State i) ≃ᵐ
    ((ℝ≥0 × (RationalTime → ℝ)) × (ℝ × (RationalTime → ℝ))) :=
  (MeasurableEquiv.sumPiEquivProdPi State).trans
    ((optionEquiv LeftState).prodCongr (optionEquiv RightState))

private def encoded (x : (ℝ≥0 × Path) × (ℝ × Path)) : (i : Index) → State i :=
  packedEquiv.symm ((x.1.1,rationalEval x.1.2),(x.2.1,rationalEval x.2.2))

private theorem encoded_embedding : MeasurableEmbedding encoded :=
  packedEquiv.symm.measurableEmbedding.comp
    ((MeasurableEmbedding.id.prodMap rationalEval_measurableEmbedding).prodMap
      (MeasurableEmbedding.id.prodMap rationalEval_measurableEmbedding))

private def coordTime : Index → ℝ≥0
  | Sum.inl none => 0
  | Sum.inl (some q) => rationalTimeReal q
  | Sum.inr none => 0
  | Sum.inr (some q) => rationalTimeReal q

private def decodeCoord {k : ℕ} (i : Index) (j : Fin k)
    (u : (ℝ≥0 × (Fin k → ℝ)) × (ℝ × (Fin k → ℝ))) : State i := by
  cases i with
  | inl q =>
    cases q with
    | none => exact u.1.1
    | some _ => exact u.1.2 j
  | inr q =>
    cases q with
    | none => exact u.2.1
    | some _ => exact u.2.2 j

private theorem measurable_decodeCoord {k : ℕ} (i : Index) (j : Fin k) :
    Measurable (decodeCoord i j) := by
  cases i with
  | inl q =>
    cases q with
    | none => exact measurable_fst.fst
    | some _ => exact (measurable_pi_apply j).comp measurable_fst.snd
  | inr q =>
    cases q with
    | none => exact measurable_snd.fst
    | some _ => exact (measurable_pi_apply j).comp measurable_snd.snd

private theorem decode_sample (i : Index) {k : ℕ} (σ : Fin k → ℝ≥0) (j : Fin k)
    (hj : σ j = coordTime i) (x : (ℝ≥0 × Path) × (ℝ × Path)) :
    decodeCoord i j (sample σ σ x) = encoded x i := by
  cases i with
  | inl q =>
    cases q with
    | none => rfl
    | some q =>
      change x.1.2 (σ j) = x.1.2 (rationalTimeReal q)
      exact congrArg x.1.2 hj
  | inr q =>
    cases q with
    | none => rfl
    | some q =>
      change x.2.2 (σ j) = x.2.2 (rationalTimeReal q)
      exact congrArg x.2.2 hj

theorem ext_of_finite_sample_tests
    (μ ν : Measure ((ℝ≥0 × Path) × (ℝ × Path))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (m n : ℕ) (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0)
      (Ψ : ((ℝ≥0 × (Fin m → ℝ)) × (ℝ × (Fin n → ℝ))) →ᵇ ℝ≥0),
      (∫⁻ x, Ψ (sample σ τ x) ∂μ) = ∫⁻ x, Ψ (sample σ τ x) ∂ν) : μ = ν := by
  have hsample (m n : ℕ) (σ : Fin m → ℝ≥0) (τ : Fin n → ℝ≥0) :
      μ.map (sample σ τ) = ν.map (sample σ τ) := by
    apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
    intro Ψ
    rw [lintegral_map Ψ.continuous.measurable.coe_nnreal_ennreal
        (continuous_sample σ τ).measurable,
      lintegral_map Ψ.continuous.measurable.coe_nnreal_ennreal
        (continuous_sample σ τ).measurable]
    exact h m n σ τ Ψ
  have hfinite (I : Finset Index) :
      μ.map (fun x ↦ I.restrict (encoded x)) = ν.map (fun x ↦ I.restrict (encoded x)) := by
    let k := Fintype.card I
    let σ : Fin k → ℝ≥0 := fun j ↦ coordTime ((Fintype.equivFin I).symm j)
    let R : ((ℝ≥0 × (Fin k → ℝ)) × (ℝ × (Fin k → ℝ))) →
        ((i : I) → State i) := fun u i ↦ decodeCoord i (Fintype.equivFin I i) u
    have hR : Measurable R := measurable_pi_lambda _
      (fun i ↦ measurable_decodeCoord i (Fintype.equivFin I i))
    have he : R ∘ sample σ σ = fun x ↦ I.restrict (encoded x) := by
      funext x i
      apply decode_sample
      simp only [σ,Equiv.symm_apply_apply]
    have ht := congrArg (Measure.map R) (hsample k k σ σ)
    rw [Measure.map_map hR (continuous_sample σ σ).measurable,
      Measure.map_map hR (continuous_sample σ σ).measurable,he] at ht
    exact ht
  have hm : Measurable encoded := encoded_embedding.measurable
  have hp := isProjectiveLimit_map (P := μ) hm.aemeasurable
  simp_rw [hfinite] at hp
  exact encoded_embedding.map_injective (hp.unique (isProjectiveLimit_map (P := ν) hm.aemeasurable))

end PerronWright.BrownianMinimumSplitSampling
