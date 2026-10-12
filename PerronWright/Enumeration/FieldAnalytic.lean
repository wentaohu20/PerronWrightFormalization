import PerronWright.Enumeration.FieldWeight
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory
open scoped Classical

noncomputable section

namespace PerronWright.CompactBJRModel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem continuous_integrable {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X, ℂ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact

private def continuousIntegralCLM {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] :
    C(X, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := by
        intro f g
        change ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ
        exact integral_add (continuous_integrable μ f) (continuous_integrable μ g)
      map_smul' := by
        intro c f
        change ∫ x, c • f x ∂μ = c • ∫ x, f x ∂μ
        exact integral_smul c (fun x => f x) }
    (μ.real Set.univ) (by
      intro f
      calc
        ‖∫ x, f x ∂μ‖ ≤ ‖f‖ * μ.real Set.univ := by
          apply norm_integral_le_of_norm_le_const
          filter_upwards [] with x
          exact f.norm_coe_le_norm x
        _ = μ.real Set.univ * ‖f‖ := by ring)

private def vertexPullbackCLM (k : ℕ) (i : Fin k) :
    C(S, ℂ) →L[ℂ] C(Fin k → S, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun g => g.comp
        ⟨fun x : Fin k → S => x i, continuous_apply i⟩
      map_add' := by
        intro f g
        ext x
        simp
      map_smul' := by
        intro c f
        ext x
        simp }
    1 (by
      intro g
      apply (ContinuousMap.norm_le _ (by positivity)).2
      intro x
      simpa [ContinuousMap.comp_apply] using g.norm_coe_le_norm (x i))

private def degreePullback (M : CompactBJRModel S) (k : ℕ) (i : Fin k) :
    C(Fin k → S, ℂ) :=
  ⟨fun x => (M.degreeFunction (x i) : ℂ),
    Complex.continuous_ofReal.comp
      (M.degreeFunction.continuous.comp (continuous_apply i))⟩

private def edgeProductC (M : CompactBJRModel S) {k : ℕ}
    (H : SimpleGraph (Fin k)) : C(Fin k → S, ℂ) := by
  classical
  exact ⟨fun x => ∏ e ∈ H.edgeFinset, (M.edgeFactor 1 x e : ℂ), by
    apply continuous_finsetProd
    intro e _
    exact Complex.continuous_ofReal.comp (M.edgeFactor_continuous 1 e)⟩

private theorem continuousMap_exp_apply {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : C(X, ℂ)) (x : X) : NormedSpace.exp f x = Complex.exp (f x) := by
  simpa only [ContinuousMap.evalAlgHom_apply, ← Complex.exp_eq_exp_ℂ] using
    NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x)
      (ContinuousMap.evalCLM ℂ x).continuous f

/-- Complexified fixed-graph field integrand, packaged as a continuous function of types. -/
def complexFieldGraphIntegrand (M : CompactBJRModel S) (g : C(S, ℂ)) {k : ℕ}
    (H : SimpleGraph (Fin k)) : C(Fin k → S, ℂ) := by
  classical
  exact (∏ i : Fin k,
    NormedSpace.exp (vertexPullbackCLM k i g - degreePullback M k i)) * edgeProductC M H

/-- Complexified fixed-graph field weight. -/
def complexFieldGraphWeight (M : CompactBJRModel S) (g : C(S, ℂ)) {k : ℕ}
    (H : SimpleGraph (Fin k)) : ℂ :=
  continuousIntegralCLM (Measure.pi (fun _ : Fin k => M.mu))
    (M.complexFieldGraphIntegrand g H)

/-- Complexified connected fixed-size, fixed-surplus weight. -/
def complexFieldConnectedWeight (M : CompactBJRModel S) (g : C(S, ℂ))
    (k r : ℕ) : ℂ := by
  classical
  exact ∑ H : SimpleGraph (Fin k),
    if H.Connected ∧ H.edgeFinset.card = k + r - 1
    then M.complexFieldGraphWeight g H else 0

/-- The canonical complexification of a real continuous field. -/
def complexifyField (g : C(S, ℝ)) : C(S, ℂ) :=
  ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem complexifyField_apply (g : C(S, ℝ)) (x : S) :
    complexifyField g x = (g x : ℂ) := rfl

omit [MeasurableSpace S] [BorelSpace S] in
private theorem vertexPullbackCLM_apply {k : ℕ} (i : Fin k)
    (g : C(S, ℂ)) (x : Fin k → S) :
    vertexPullbackCLM k i g x = g (x i) := rfl

private theorem degreePullback_apply (M : CompactBJRModel S) {k : ℕ} (i : Fin k)
    (x : Fin k → S) : degreePullback M k i x = (M.degreeFunction (x i) : ℂ) := rfl

private theorem edgeProductC_apply (M : CompactBJRModel S) {k : ℕ}
    (H : SimpleGraph (Fin k)) (x : Fin k → S) :
    edgeProductC M H x = (∏ e ∈ H.edgeFinset, M.edgeFactor 1 x e : ℂ) := rfl

theorem complexFieldGraphIntegrand_complexifyField (M : CompactBJRModel S)
    (g : C(S, ℝ)) {k : ℕ} (H : SimpleGraph (Fin k)) (x : Fin k → S) :
    M.complexFieldGraphIntegrand (complexifyField g) H x =
      (M.fieldGraphWeightIntegrand g H x : ℂ) := by
  classical
  unfold complexFieldGraphIntegrand fieldGraphWeightIntegrand
  simp only [ContinuousMap.coe_mul, Pi.mul_apply]
  change (Finset.univ.prod fun i : Fin k =>
      NormedSpace.exp (vertexPullbackCLM k i (complexifyField g) -
        degreePullback M k i)) x * edgeProductC M H x = _
  rw [ContinuousMap.prod_apply]
  simp_rw [continuousMap_exp_apply]
  simp_rw [ContinuousMap.sub_apply]
  simp_rw [vertexPullbackCLM_apply, degreePullback_apply, complexifyField_apply]
  change (∏ i : Fin k, Complex.exp ((g (x i) : ℂ) -
      (M.degreeFunction (x i) : ℂ))) *
      (∏ e ∈ H.edgeFinset, (M.edgeFactor 1 x e : ℂ)) = _
  simp_rw [← Complex.ofReal_sub, ← Complex.ofReal_exp]
  rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_mul]

private theorem analyticAt_vertexFactor (M : CompactBJRModel S) {k : ℕ}
  (i : Fin k) (g : C(S, ℂ)) :
    AnalyticAt ℂ (fun h : C(S, ℂ) =>
      NormedSpace.exp (vertexPullbackCLM k i h - degreePullback M k i)) g := by
  simpa [Function.comp_def] using
    (NormedSpace.exp_analytic _).comp
      (((vertexPullbackCLM k i).analyticAt g).sub analyticAt_const)

private theorem analyticAt_vertexProduct (M : CompactBJRModel S) {k : ℕ}
    (g : C(S, ℂ)) :
    AnalyticAt ℂ (fun h : C(S, ℂ) => ∏ i : Fin k,
      NormedSpace.exp (vertexPullbackCLM k i h - degreePullback M k i)) g := by
  classical
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : C(S, ℂ) => (1 : C(Fin k → S, ℂ))) g)
  | insert i s hi ih =>
      have hfun :
          (fun h : C(S, ℂ) => ∏ j ∈ insert i s,
            NormedSpace.exp (vertexPullbackCLM k j h - degreePullback M k j)) =
          (fun h : C(S, ℂ) =>
            NormedSpace.exp (vertexPullbackCLM k i h - degreePullback M k i)) *
            (fun h : C(S, ℂ) => ∏ j ∈ s,
              NormedSpace.exp (vertexPullbackCLM k j h - degreePullback M k j)) := by
        funext h
        rw [Finset.prod_insert hi]
        rfl
      rw [hfun]
      exact (analyticAt_vertexFactor M i g).mul ih

theorem analyticAt_complexFieldGraphIntegrand (M : CompactBJRModel S) {k : ℕ}
    (H : SimpleGraph (Fin k)) (g : C(S, ℂ)) :
    AnalyticAt ℂ (fun h : C(S, ℂ) => M.complexFieldGraphIntegrand h H) g := by
  unfold complexFieldGraphIntegrand
  exact (analyticAt_vertexProduct M g).mul analyticAt_const

theorem analyticAt_complexFieldGraphWeight (M : CompactBJRModel S) {k : ℕ}
    (H : SimpleGraph (Fin k)) (g : C(S, ℂ)) :
    AnalyticAt ℂ (fun h : C(S, ℂ) => M.complexFieldGraphWeight h H) g := by
  unfold complexFieldGraphWeight
  let F : C(S, ℂ) → C(Fin k → S, ℂ) :=
    fun h => M.complexFieldGraphIntegrand h H
  have hInt : AnalyticAt ℂ (continuousIntegralCLM (Measure.pi (fun _ : Fin k => M.mu)) :
      C(Fin k → S, ℂ) → ℂ) (M.complexFieldGraphIntegrand g H) :=
    (continuousIntegralCLM (Measure.pi (fun _ : Fin k => M.mu))).analyticAt _
  have hF : AnalyticAt ℂ F g := M.analyticAt_complexFieldGraphIntegrand H g
  exact AnalyticAt.comp hInt hF

theorem analyticAt_complexFieldConnectedWeight (M : CompactBJRModel S)
    (k r : ℕ) (g : C(S, ℂ)) :
    AnalyticAt ℂ (fun h : C(S, ℂ) => M.complexFieldConnectedWeight h k r) g := by
  classical
  unfold complexFieldConnectedWeight
  let F : SimpleGraph (Fin k) → C(S, ℂ) → ℂ := fun H h =>
    if H.Connected ∧ H.edgeFinset.card = k + r - 1
    then M.complexFieldGraphWeight h H else 0
  change AnalyticAt ℂ (fun h : C(S, ℂ) => ∑ H, F H h) g
  have hsum : AnalyticAt ℂ (∑ H, F H) g := by
    apply Finset.analyticAt_sum Finset.univ
    intro H _
    dsimp [F]
    split
    · exact M.analyticAt_complexFieldGraphWeight H g
    · exact analyticAt_const
  have hfun : (∑ H, F H) = (fun h : C(S, ℂ) => ∑ H, F H h) := by
    funext h
    exact Fintype.sum_apply h F
  rw [← hfun]
  exact hsum

theorem complexFieldGraphWeight_complexifyField (M : CompactBJRModel S)
    (g : C(S, ℝ)) {k : ℕ} (H : SimpleGraph (Fin k)) :
    M.complexFieldGraphWeight (complexifyField g) H =
      (M.fieldGraphWeight g H : ℂ) := by
  unfold complexFieldGraphWeight fieldGraphWeight continuousIntegralCLM
  dsimp
  calc
    (∫ x : Fin k → S, M.complexFieldGraphIntegrand (complexifyField g) H x
      ∂Measure.pi (fun _ : Fin k => M.mu)) =
      ∫ x : Fin k → S, (M.fieldGraphWeightIntegrand g H x : ℂ)
      ∂Measure.pi (fun _ : Fin k => M.mu) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact M.complexFieldGraphIntegrand_complexifyField g H x
    _ = (∫ x : Fin k → S, M.fieldGraphWeightIntegrand g H x
      ∂Measure.pi (fun _ : Fin k => M.mu) : ℝ) := integral_ofReal

theorem complexFieldConnectedWeight_complexifyField (M : CompactBJRModel S)
    (g : C(S, ℝ)) (k r : ℕ) :
    M.complexFieldConnectedWeight (complexifyField g) k r =
      (M.fieldConnectedWeight g k r : ℂ) := by
  classical
  unfold complexFieldConnectedWeight fieldConnectedWeight
  simp_rw [M.complexFieldGraphWeight_complexifyField]
  calc
    (∑ H : SimpleGraph (Fin k),
        if H.Connected ∧ H.edgeFinset.card = k + r - 1
        then (M.fieldGraphWeight g H : ℂ) else 0) =
      ∑ H : SimpleGraph (Fin k),
        ((if H.Connected ∧ H.edgeFinset.card = k + r - 1
        then M.fieldGraphWeight g H else 0 : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro H _
          split <;> simp
    _ = ((∑ H : SimpleGraph (Fin k),
        if H.Connected ∧ H.edgeFinset.card = k + r - 1
        then M.fieldGraphWeight g H else 0 : ℝ) : ℂ) := by
          exact (Complex.ofReal_sum Finset.univ fun H : SimpleGraph (Fin k) =>
            if H.Connected ∧ H.edgeFinset.card = k + r - 1
            then M.fieldGraphWeight g H else 0).symm

end PerronWright.CompactBJRModel

end
