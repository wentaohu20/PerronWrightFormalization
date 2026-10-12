import PerronWright.Probability.FiniteIrreducibleDeterministicResidualWeights
import PerronWright.Probability.FreshTypeCumulantExpansion

/-!
# Uniform zero-safe odds bounds for literal finite connected graphs

The finite sum of the literal nonnegative matrix entries is a proved
global kernel bound. Eligibility supplies the true edge count. Every
type vector is covered; zero kernel entries use normalizedOdds 0 = 1.
-/

open Filter Topology
open scoped BigOperators Classical Topology Real
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleOddsCorrectionBounds

open AnnealedTupleResidualConnectedLawProduct FiniteIrreducibleDeterministicResidualWeights
open FreshTypeAveraging FreshTypeCumulantExpansion

variable {S : Type*} [Fintype S] [DecidableEq S]

def kernelBudget (M : FiniteIrreducibleModel S) : ℝ := ∑ a, ∑ b, M.kernel a b

theorem kernelBudget_nonneg (M : FiniteIrreducibleModel S) : 0 ≤ kernelBudget M :=
  Finset.sum_nonneg (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ M.kernel_nonneg a b))

theorem kernel_le_kernelBudget (M : FiniteIrreducibleModel S) (a b : S) :
    M.kernel a b ≤ kernelBudget M :=
  (Finset.single_le_sum (fun c _ ↦ M.kernel_nonneg a c) (Finset.mem_univ b)).trans
    (Finset.single_le_sum (fun c _ ↦ Finset.sum_nonneg (fun d _ ↦ M.kernel_nonneg c d))
      (Finset.mem_univ a))

def totalEdges {q : ℕ} {k : Fin q → ℕ} (p : TupleState S k) : ℕ :=
  ∑ i, (p i).2.edgeFinset.card

omit [Fintype S] [DecidableEq S] in
theorem totalEdges_eq_surplus {q : ℕ} (k r : Fin q → ℕ) (p : TupleState S k)
    (hp : ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2) :
    totalEdges p = ∑ i, (k i + r i - 1) := by
  unfold totalEdges
  exact Finset.sum_congr rfl (fun i _ ↦ (hp i).2)

omit [Fintype S] [DecidableEq S] in
theorem totalEdges_le_size_cutoff {q : ℕ} (k r : Fin q → ℕ) (R : ℕ)
    (p : TupleState S k) (hp : ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2)
    (hr : ∀ i, r i ≤ R) :
    totalEdges p ≤ (∑ i, k i) + q * R := by
  rw [totalEdges_eq_surplus k r p hp]
  calc
    _ ≤ ∑ i, (k i + R) := Finset.sum_le_sum (fun i _ ↦ by have := hr i; omega)
    _ = _ := by rw [Finset.sum_add_distrib]; simp

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem pairKernel_le_kernelBudget (M : FiniteIrreducibleModel S)
    {k : ℕ} (y : Fin k → S) (e : Sym2 (Fin k)) :
    FiniteIrreducibleTypedGraphLaw.pairKernel M y e ≤ kernelBudget M := by
  induction e using Sym2.inductionOn with
  | _ i j => exact kernel_le_kernelBudget M (y i) (y j)

theorem one_le_oddsCorrection (M : FiniteIrreducibleModel S) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) {q : ℕ} {k : Fin q → ℕ} (p : TupleState S k) :
    1 ≤ oddsCorrection M t n p := by
  apply Finset.one_le_prod
  intro i _
  apply Finset.one_le_prod
  intro e _
  exact (normalizedOdds_bounds (div_nonneg
    (M.bjrModel.edgeFactor_nonneg t ht (p i).1 e) (Nat.cast_nonneg n))).1

theorem oddsCorrection_le_exp_totalEdges (M : FiniteIrreducibleModel S)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (n : ℕ)
    {q : ℕ} {k : Fin q → ℕ} (p : TupleState S k) :
    oddsCorrection M t n p ≤
      Real.exp (T * kernelBudget M / (n : ℝ) * (totalEdges p : ℝ)) := by
  have hfactor (i : Fin q) (e : Sym2 (Fin (k i))) :
      normalizedOdds (M.bjrModel.edgeFactor t (p i).1 e / (n : ℝ)) ≤
        Real.exp (T * kernelBudget M / (n : ℝ)) := by
    have hz : 0 ≤ M.bjrModel.edgeFactor t (p i).1 e / (n : ℝ) :=
      div_nonneg (M.bjrModel.edgeFactor_nonneg t ht (p i).1 e) (Nat.cast_nonneg n)
    refine (normalizedOdds_bounds hz).2.trans (Real.exp_le_exp.mpr ?_)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    rw [edgeFactor_eq_pairKernel]
    exact (mul_le_mul_of_nonneg_left (pairKernel_le_kernelBudget M (p i).1 e) ht).trans
      (mul_le_mul_of_nonneg_right htT (kernelBudget_nonneg M))
  calc
    oddsCorrection M t n p ≤ ∏ i, ∏ e ∈ (p i).2.edgeFinset,
        Real.exp (T * kernelBudget M / (n : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Finset.prod_nonneg (fun e _ ↦
          (normalizedOdds_pos (div_nonneg
            (M.bjrModel.edgeFactor_nonneg t ht (p i).1 e) (Nat.cast_nonneg n))).le)
      · intro i _
        exact Finset.prod_le_prod
          (fun e _ ↦ (normalizedOdds_pos (div_nonneg
            (M.bjrModel.edgeFactor_nonneg t ht (p i).1 e) (Nat.cast_nonneg n))).le)
          (fun e _ ↦ hfactor i e)
    _ = _ := by
      simp_rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_const, nsmul_eq_mul, totalEdges, Nat.cast_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem oddsCorrection_sub_one_bound (M : FiniteIrreducibleModel S)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (n : ℕ)
    {q : ℕ} (k r : Fin q → ℕ) (R : ℕ) (p : TupleState S k)
    (hp : ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2) (hr : ∀ i, r i ≤ R) :
    |oddsCorrection M t n p - 1| ≤
      Real.exp (T * kernelBudget M / (n : ℝ) *
        ((∑ i, k i : ℕ) + q * R : ℕ)) - 1 := by
  rw [abs_of_nonneg (sub_nonneg.mpr (one_le_oddsCorrection M ht n p))]
  have hT : 0 ≤ T := ht.trans htT
  have hcount : (totalEdges p : ℝ) ≤ ((∑ i, k i) + q * R : ℕ) := by
    exact_mod_cast totalEdges_le_size_cutoff k r R p hp hr
  exact sub_le_sub_right ((oddsCorrection_le_exp_totalEdges M ht htT n p).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcount
      (div_nonneg (mul_nonneg hT (kernelBudget_nonneg M)) (Nat.cast_nonneg n))))) 1

theorem log_oddsCorrection_bounds (M : FiniteIrreducibleModel S)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (n : ℕ)
    {q : ℕ} {k : Fin q → ℕ} (p : TupleState S k) :
    0 ≤ Real.log (oddsCorrection M t n p) ∧
      Real.log (oddsCorrection M t n p) ≤
        T * kernelBudget M / (n : ℝ) * (totalEdges p : ℝ) := by
  refine ⟨Real.log_nonneg (one_le_oddsCorrection M ht n p), ?_⟩
  have h := Real.log_le_log (oddsCorrection_pos M ht n p)
    (oddsCorrection_le_exp_totalEdges M ht htT n p)
  simpa only [Real.log_exp] using h

def criticalOddsEnvelope (M : FiniteIrreducibleModel S) (T C : ℝ)
    (q R n : ℕ) : ℝ :=
  Real.exp (T * kernelBudget M *
    (C * (n : ℝ)^(-(1/3 : ℝ)) + ((q * R : ℕ) : ℝ) / (n : ℝ))) - 1

def criticalLogOddsEnvelope (M : FiniteIrreducibleModel S) (T C : ℝ)
    (q R n : ℕ) : ℝ :=
  T * kernelBudget M *
    (C * (n : ℝ)^(-(1/3 : ℝ)) + ((q * R : ℕ) : ℝ) / (n : ℝ))

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem criticalLogOddsEnvelope_nonneg (M : FiniteIrreducibleModel S)
    {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (q R n : ℕ) :
    0 ≤ criticalLogOddsEnvelope M T C q R n :=
  mul_nonneg (mul_nonneg hT (kernelBudget_nonneg M))
    (add_nonneg (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg n)))

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem criticalOddsEnvelope_nonneg (M : FiniteIrreducibleModel S)
    {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (q R n : ℕ) :
    0 ≤ criticalOddsEnvelope M T C q R n := by
  apply sub_nonneg.mpr
  apply Real.one_le_exp
  exact mul_nonneg (mul_nonneg hT (kernelBudget_nonneg M))
    (add_nonneg (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg n)))

theorem oddsCorrection_critical_window_bound (M : FiniteIrreducibleModel S)
    {t T C : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) {n : ℕ} (hn : 0 < n)
    {q : ℕ} (k r : Fin q → ℕ) (R : ℕ) (p : TupleState S k)
    (hp : ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2) (hr : ∀ i, r i ≤ R)
    (hsize : ((∑ i, k i : ℕ) : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ)) :
    |oddsCorrection M t n p - 1| ≤ criticalOddsEnvelope M T C q R n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hT : 0 ≤ T := ht.trans htT
  have hpow : (n : ℝ)^(2/3 : ℝ) / (n : ℝ) = (n : ℝ)^(-(1/3 : ℝ)) := by
    calc
      _ = (n : ℝ)^(2/3 : ℝ) / (n : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ)^((2/3 : ℝ)-1) := (Real.rpow_sub hnR _ _).symm
      _ = _ := by congr 1; ring
  unfold criticalOddsEnvelope
  refine (oddsCorrection_sub_one_bound M ht htT n k r R p hp hr).trans ?_
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have hs := div_le_div_of_nonneg_right hsize hnR.le
  rw [mul_div_assoc, hpow] at hs
  have hb := mul_le_mul_of_nonneg_left
    (add_le_add_right hs (((q * R : ℕ) : ℝ) / (n : ℝ)))
    (mul_nonneg hT (kernelBudget_nonneg M))
  calc
    _ = T * kernelBudget M *
        (((∑ i, k i : ℕ) : ℝ) / (n : ℝ) + ((q * R : ℕ) : ℝ) / (n : ℝ)) := by
      push_cast
      ring
    _ ≤ _ := by simpa only [add_comm] using hb

theorem log_oddsCorrection_critical_window_bound (M : FiniteIrreducibleModel S)
    {t T C : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) {n : ℕ} (hn : 0 < n)
    {q : ℕ} (k r : Fin q → ℕ) (R : ℕ) (p : TupleState S k)
    (hp : ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2) (hr : ∀ i, r i ≤ R)
    (hsize : ((∑ i, k i : ℕ) : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ)) :
    0 ≤ Real.log (oddsCorrection M t n p) ∧
      Real.log (oddsCorrection M t n p) ≤ T * kernelBudget M *
        (C * (n : ℝ)^(-(1/3 : ℝ)) + ((q * R : ℕ) : ℝ) / (n : ℝ)) := by
  refine ⟨Real.log_nonneg (one_le_oddsCorrection M ht n p), ?_⟩
  have hbound := oddsCorrection_critical_window_bound M ht htT hn k r R p hp hr hsize
  unfold criticalOddsEnvelope at hbound
  have habs := le_abs_self (oddsCorrection M t n p - 1)
  have hup : oddsCorrection M t n p ≤ Real.exp (T * kernelBudget M *
      (C * (n : ℝ)^(-(1/3 : ℝ)) + ((q * R : ℕ) : ℝ) / (n : ℝ))) := by linarith
  have h := Real.log_le_log (oddsCorrection_pos M ht n p) hup
  simpa only [Real.log_exp] using h

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem criticalLogOddsEnvelope_tendsto_zero (M : FiniteIrreducibleModel S)
    (T C : ℝ) (q R : ℕ) :
    Tendsto (criticalLogOddsEnvelope M T C q R) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ ↦ (n : ℝ)^(-(1/3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/3)).comp tendsto_natCast_atTop_atTop
  have hd := tendsto_const_div_atTop_nhds_zero_nat (((q*R : ℕ) : ℝ))
  unfold criticalLogOddsEnvelope
  simpa only [mul_zero, add_zero] using
    ((hp.const_mul C).add hd).const_mul (T * kernelBudget M)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem criticalOddsEnvelope_tendsto_zero (M : FiniteIrreducibleModel S)
    (T C : ℝ) (q R : ℕ) :
    Tendsto (criticalOddsEnvelope M T C q R) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ ↦ (n : ℝ)^(-(1/3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/3)).comp tendsto_natCast_atTop_atTop
  have hd := tendsto_const_div_atTop_nhds_zero_nat (((q*R : ℕ) : ℝ))
  have hh := (hp.const_mul C).add hd
  have hz : Tendsto (fun n : ℕ ↦ T * kernelBudget M *
      (C * (n : ℝ)^(-(1/3 : ℝ)) + ((q*R : ℕ) : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hh.const_mul (T * kernelBudget M)
  have hE := (Real.continuous_exp.tendsto 0).comp hz
  unfold criticalOddsEnvelope
  simpa only [mul_zero, add_zero, Real.exp_zero,
    Function.comp_def, sub_self] using hE.sub_const 1

end PerronWright.FiniteIrreducibleOddsCorrectionBounds

