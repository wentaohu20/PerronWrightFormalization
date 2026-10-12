import PerronWright.Enumeration.ConnectedWeight

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright.CompactBJRModel
variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem edgeFactor_nonneg (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t)
    {k : ℕ} (x : Fin k → S) (e : Sym2 (Fin k)) : 0 ≤ M.edgeFactor t x e := by
  induction e using Sym2.inductionOn with
  | _ i j => exact mul_nonneg ht (M.kernel.nonneg (x i) (x j))

theorem edgeFactor_continuous (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} (e : Sym2 (Fin k)) : Continuous (fun x : Fin k → S => M.edgeFactor t x e) := by
  induction e using Sym2.inductionOn with
  | _ i j =>
      simp only [edgeFactor_mk]
      exact continuous_const.mul
        (M.kernel.toContinuousMap.continuous.comp ((continuous_apply i).prodMk (continuous_apply j)))

theorem graphWeightIntegrand_nonneg (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t)
    {k : ℕ} (H : SimpleGraph (Fin k)) (x : Fin k → S) :
    0 ≤ M.graphWeightIntegrand t H x := by
  classical
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)
  · exact Finset.prod_nonneg (fun e _ => M.edgeFactor_nonneg t ht x e)

theorem graphWeightIntegrand_continuous (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} (H : SimpleGraph (Fin k)) : Continuous (M.graphWeightIntegrand t H) := by
  classical
  unfold graphWeightIntegrand
  apply Continuous.mul
  · apply continuous_finsetProd
    intro i _
    exact (continuous_const.mul (M.degreeFunction.continuous.comp (continuous_apply i))).rexp
  · apply continuous_finsetProd
    intro e _
    exact M.edgeFactor_continuous t e

theorem graphWeightIntegrand_integrable (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} (H : SimpleGraph (Fin k)) :
    Integrable (M.graphWeightIntegrand t H) (Measure.pi (fun _ : Fin k => M.mu)) :=
  (M.graphWeightIntegrand_continuous t H).integrable_of_hasCompactSupport
    isClosed_closure.isCompact

theorem graphWeight_nonneg (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t)
    {k : ℕ} (H : SimpleGraph (Fin k)) : 0 ≤ M.graphWeight t H :=
  integral_nonneg (M.graphWeightIntegrand_nonneg t ht H)

theorem connectedWeight_nonneg (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t)
    (k r : ℕ) : 0 ≤ M.connectedWeight t k r := by
  classical
  unfold connectedWeight
  apply Finset.sum_nonneg
  intro H _
  split
  · exact M.graphWeight_nonneg t ht H
  · exact le_rfl

theorem edgeFactor_scale (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} (x : Fin k → S) (e : Sym2 (Fin k)) :
    M.edgeFactor t x e = t * M.edgeFactor 1 x e := by
  induction e using Sym2.inductionOn with
  | _ i j => simp only [edgeFactor_mk, one_mul]

theorem graphWeightIntegrand_edgePower (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} (H : SimpleGraph (Fin k)) (x : Fin k → S) :
    M.graphWeightIntegrand t H x = t ^ H.edgeFinset.card *
      ((∏ i : Fin k, Real.exp (-t * M.degreeFunction (x i))) *
        ∏ e ∈ H.edgeFinset, M.edgeFactor 1 x e) := by
  classical
  unfold graphWeightIntegrand
  simp_rw [M.edgeFactor_scale t]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  ring

def scalarField (M : CompactBJRModel S) (t : ℝ) : C(S, ℝ) :=
  ⟨fun x => Real.log t - (t - 1) * M.degreeFunction x, by fun_prop⟩

@[simp] theorem scalarField_apply (M : CompactBJRModel S) (t : ℝ) (x : S) :
    M.scalarField t x = Real.log t - (t - 1) * M.degreeFunction x := rfl

def fieldGraphWeightIntegrand (M : CompactBJRModel S) (g : C(S, ℝ)) {k : ℕ}
    (H : SimpleGraph (Fin k)) (x : Fin k → S) : ℝ :=
  (∏ i : Fin k, Real.exp (g (x i) - M.degreeFunction (x i))) *
    ∏ e ∈ H.edgeFinset, M.edgeFactor 1 x e

def fieldGraphWeight (M : CompactBJRModel S) (g : C(S, ℝ)) {k : ℕ}
    (H : SimpleGraph (Fin k)) : ℝ :=
  ∫ x : Fin k → S, M.fieldGraphWeightIntegrand g H x
    ∂Measure.pi (fun _ : Fin k => M.mu)

def fieldConnectedWeight (M : CompactBJRModel S) (g : C(S, ℝ)) (k r : ℕ) : ℝ :=
  ∑ H : SimpleGraph (Fin k),
    if H.Connected ∧ H.edgeFinset.card = k + r - 1
    then M.fieldGraphWeight g H else 0

theorem scalarField_vertexFactor (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t) (x : S) :
    Real.exp (M.scalarField t x - M.degreeFunction x) =
      t * Real.exp (-t * M.degreeFunction x) := by
  have he : M.scalarField t x - M.degreeFunction x =
      Real.log t + (-t * M.degreeFunction x) := by
    simp only [scalarField_apply]
    ring
  rw [he, Real.exp_add, Real.exp_log ht]

theorem fieldGraphWeightIntegrand_scalarField (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t)
    {k : ℕ} (H : SimpleGraph (Fin k)) (x : Fin k → S) :
    M.fieldGraphWeightIntegrand (M.scalarField t) H x = t ^ k *
      ((∏ i : Fin k, Real.exp (-t * M.degreeFunction (x i))) *
        ∏ e ∈ H.edgeFinset, M.edgeFactor 1 x e) := by
  unfold fieldGraphWeightIntegrand
  simp_rw [M.scalarField_vertexFactor t ht]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem graphWeightIntegrand_field_cross_identity (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 < t) {k : ℕ} (H : SimpleGraph (Fin k)) (x : Fin k → S) :
    t ^ k * M.graphWeightIntegrand t H x =
      t ^ H.edgeFinset.card * M.fieldGraphWeightIntegrand (M.scalarField t) H x := by
  rw [M.graphWeightIntegrand_edgePower, M.fieldGraphWeightIntegrand_scalarField t ht]
  ring

theorem graphWeight_field_cross_identity (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 < t) {k : ℕ} (H : SimpleGraph (Fin k)) :
    t ^ k * M.graphWeight t H =
      t ^ H.edgeFinset.card * M.fieldGraphWeight (M.scalarField t) H := by
  unfold graphWeight fieldGraphWeight
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  exact M.graphWeightIntegrand_field_cross_identity t ht H x

theorem fieldGraphWeightIntegrand_nonneg (M : CompactBJRModel S) (g : C(S, ℝ))
    {k : ℕ} (H : SimpleGraph (Fin k)) (x : Fin k → S) :
    0 ≤ M.fieldGraphWeightIntegrand g H x := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)
  · exact Finset.prod_nonneg (fun e _ => M.edgeFactor_nonneg 1 zero_le_one x e)

theorem fieldGraphWeightIntegrand_continuous (M : CompactBJRModel S) (g : C(S, ℝ))
    {k : ℕ} (H : SimpleGraph (Fin k)) : Continuous (M.fieldGraphWeightIntegrand g H) := by
  unfold fieldGraphWeightIntegrand
  apply Continuous.mul
  · apply continuous_finsetProd
    intro i _
    exact ((g.continuous.comp (continuous_apply i)).sub
      (M.degreeFunction.continuous.comp (continuous_apply i))).rexp
  · apply continuous_finsetProd
    intro e _
    exact M.edgeFactor_continuous 1 e

theorem fieldGraphWeightIntegrand_integrable (M : CompactBJRModel S) (g : C(S, ℝ))
    {k : ℕ} (H : SimpleGraph (Fin k)) :
    Integrable (M.fieldGraphWeightIntegrand g H) (Measure.pi (fun _ : Fin k => M.mu)) :=
  (M.fieldGraphWeightIntegrand_continuous g H).integrable_of_hasCompactSupport
    isClosed_closure.isCompact

theorem fieldGraphWeight_nonneg (M : CompactBJRModel S) (g : C(S, ℝ))
    {k : ℕ} (H : SimpleGraph (Fin k)) : 0 ≤ M.fieldGraphWeight g H :=
  integral_nonneg (M.fieldGraphWeightIntegrand_nonneg g H)

theorem fieldConnectedWeight_nonneg (M : CompactBJRModel S) (g : C(S, ℝ))
    (k r : ℕ) : 0 ≤ M.fieldConnectedWeight g k r := by
  unfold fieldConnectedWeight
  apply Finset.sum_nonneg
  intro H _
  split
  · exact M.fieldGraphWeight_nonneg g H
  · exact le_rfl

theorem graphWeight_scalarField_of_edge_card (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 < t) {k r : ℕ} (hk : 0 < k) (H : SimpleGraph (Fin k))
    (hcard : H.edgeFinset.card = k + r - 1) :
    M.graphWeight t H = t ^ ((r : ℤ) - 1) * M.fieldGraphWeight (M.scalarField t) H := by
  have hpower : t ^ (k + r - 1) = t ^ ((r : ℤ) - 1) * t ^ k := by
    rw [← zpow_natCast t (k + r - 1), ← zpow_natCast t k, ← zpow_add₀ ht.ne']
    congr 1
    omega
  have heq := M.graphWeight_field_cross_identity t ht H
  rw [hcard, hpower] at heq
  have heq' : t ^ k * M.graphWeight t H =
      t ^ k * (t ^ ((r : ℤ) - 1) * M.fieldGraphWeight (M.scalarField t) H) := by
    calc
      _ = (t ^ ((r : ℤ) - 1) * t ^ k) * M.fieldGraphWeight (M.scalarField t) H := heq
      _ = _ := by ring
  exact mul_left_cancel₀ (pow_ne_zero k ht.ne') heq'

theorem connectedWeight_scalarField (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t)
    (k r : ℕ) :
    M.connectedWeight t k r =
      t ^ ((r : ℤ) - 1) * M.fieldConnectedWeight (M.scalarField t) k r := by
  unfold connectedWeight fieldConnectedWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  by_cases hH : H.Connected ∧ H.edgeFinset.card = k + r - 1
  · simp only [if_pos hH]
    have hk : 0 < k := by
      obtain ⟨v⟩ := hH.1.nonempty
      exact Nat.zero_lt_of_lt v.isLt
    exact M.graphWeight_scalarField_of_edge_card t ht hk H hH.2
  · simp only [if_neg hH, mul_zero]








end PerronWright.CompactBJRModel

