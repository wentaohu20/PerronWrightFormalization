import PerronWright.Enumeration.ProfileSimpleCyclePowerSeries
import PerronWright.Analysis.FiniteIrreducibleJointSimpleCycleEGF

/-!
# Finite profile simple-cycle analyticity on the full unit ball

The homogeneous coefficients are the existing literal data-only cycle
multilinear maps on M.bjrModel. Their uniform bound is proved with the actual
positive finite Perron gauge, not with a primitivity assumption.
-/

open MeasureTheory PerronWright
open scoped Topology RightActions BigOperators NNReal ENNReal
noncomputable section

namespace PerronWright.FiniteIrreducibleProfileSimpleCyclePowerSeries

open PerronWright.ProfileSimpleCyclePowerSeries

namespace JS
export PerronWright.JointSimpleCycleEGF
  (operatorCyclePairing operatorCyclePairingCLM
   operatorCyclePairingCLM_apply norm_operatorCyclePairing_le
   profileCycleTrace profileSimpleCycleTerm profileSimpleCycleSeries)
export PerronWright.FiniteIrreducibleJointSimpleCycleEGF
  (norm_profileSimpleCycleTerm_le)
end JS

namespace MPR
export PerronWright.FiniteIrreducibleMarkedPathResolvent (pathOperatorParameterCLM)
end MPR

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

omit [MeasurableSpace S] [BorelSpace S] in
private theorem perronFunction_uniform_pos
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ M.continuousPerronFunction hM x := by
  obtain ⟨m, hm, hmu⟩ := isCompact_univ.exists_forall_le'
    (M.continuousPerronFunction hM).continuous.continuousOn
    (fun x _ => M.perronFunction_pos hM x)
  exact ⟨m, hm, fun x => hmu x (Set.mem_univ x)⟩

private abbrev Profile (S : Type*) [TopologicalSpace S] := C(S, ℂ)

private abbrev PathEnd (S : Type*) [TopologicalSpace S] :=
  Profile S →L[ℂ] Profile S

local instance pathEndNormedRing : NormedRing (PathEnd S) := inferInstance
local instance pathEndSeminormedRing : SeminormedRing (PathEnd S) :=
  NormedRing.toSeminormedRing
@[reducible] local instance pathEndNormedAddCommGroup :
    NormedAddCommGroup (PathEnd S) :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance pathEndNormedAlgebra : NormedAlgebra ℂ (PathEnd S) := inferInstance
@[reducible] local instance pathEndNormedSpace : NormedSpace ℂ (PathEnd S) :=
  NormedAlgebra.toNormedSpace (PathEnd S)
local instance pathEndNormTopology : TopologicalSpace (PathEnd S) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- One paper-oriented path operator `K M_a` multiplies the Perron gauge by
at most `‖a‖`. -/
theorem pathOperatorParameter_perron_dominated
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (a f : Profile S) (c : ℝ)
    (hf : ∀ y, ‖f y‖ ≤ c * M.continuousPerronFunction hM y) (x : S) :
    ‖MPR.pathOperatorParameterCLM M a f x‖ ≤
      (‖a‖ * c) * M.continuousPerronFunction hM x := by
  have haf : ∀ y, ‖(a * f) y‖ ≤
      (‖a‖ * c) * M.continuousPerronFunction hM y := by
    intro y
    rw [ContinuousMap.mul_apply, norm_mul]
    calc
      ‖a y‖ * ‖f y‖ ≤ ‖a‖ * ‖f y‖ := by
        gcongr
        exact a.norm_coe_le_norm y
      _ ≤ ‖a‖ * (c * M.continuousPerronFunction hM y) := by
        gcongr
        exact hf y
      _ = (‖a‖ * c) * M.continuousPerronFunction hM y := by ring
  rw [FiniteIrreducibleJointSimpleCycleEGF.pathOperatorParameterCLM_eq_bjr,
    JointSimpleCycleEGF.pathOperatorParameterCLM_apply]
  change ‖M.complexOperator (a * f) x‖ ≤ _
  exact FiniteIrreducibleOuterNeumann.complexAction_perron_dominated
    M hM (‖a‖ * c) (a * f) haf x

/-- A mixed chain of profiles contracts the Perron gauge by the product of
their sup norms. -/
theorem mixedPathOperatorProduct_perron_dominated
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (as : List (Profile S)) (f : Profile S) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ y, ‖f y‖ ≤ c * M.continuousPerronFunction hM y) (x : S) :
    ‖mixedPathOperatorProduct M.bjrModel as f x‖ ≤
      ((as.map norm).prod * c) * M.continuousPerronFunction hM x := by
  induction as generalizing f c x with
  | nil =>
      simpa [mixedPathOperatorProduct] using hf x
  | cons a as ih =>
      have hprod : 0 ≤ (as.map norm).prod := by
        apply List.prod_nonneg
        intro b hb
        simp only [List.mem_map] at hb
        obtain ⟨a, -, rfl⟩ := hb
        exact norm_nonneg a
      have htail : ∀ y,
          ‖mixedPathOperatorProduct M.bjrModel as f y‖ ≤
            ((as.map norm).prod * c) * M.continuousPerronFunction hM y := by
        intro y
        exact ih f c hc hf y
      have hstep := pathOperatorParameter_perron_dominated
        M hM a (mixedPathOperatorProduct M.bjrModel as f)
        ((as.map norm).prod * c) htail x
      simpa only [FiniteIrreducibleJointSimpleCycleEGF.pathOperatorParameterCLM_eq_bjr,
        mixedPathOperatorProduct, List.map_cons, List.prod_cons,
        mul_apply_eq_comp, mul_assoc] using hstep

/-- The Perron gauge gives a mixed-chain operator norm bound with no
exponential loss in the chain length. -/
theorem norm_mixedPathOperatorProduct_le
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (as : List (Profile S)) (m : ℝ) (hm : 0 < m)
    (hmu : ∀ x, m ≤ M.continuousPerronFunction hM x) :
    ‖mixedPathOperatorProduct M.bjrModel as‖ ≤
      (‖M.continuousPerronFunction hM‖ / m) * (as.map norm).prod := by
  let P : ℝ := (as.map norm).prod
  have hP : 0 ≤ P := by
    dsimp [P]
    apply List.prod_nonneg
    intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨a, -, rfl⟩ := hb
    exact norm_nonneg a
  have hC : 0 ≤ (‖M.continuousPerronFunction hM‖ / m) * P := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  apply (ContinuousMap.norm_le _
    (mul_nonneg hC (norm_nonneg f))).2
  intro x
  have hf : ∀ y, ‖f y‖ ≤
      (‖f‖ / m) * M.continuousPerronFunction hM y := by
    intro y
    calc
      ‖f y‖ ≤ ‖f‖ := f.norm_coe_le_norm y
      _ = (‖f‖ / m) * m := by field_simp
      _ ≤ (‖f‖ / m) * M.continuousPerronFunction hM y :=
        mul_le_mul_of_nonneg_left (hmu y)
          (div_nonneg (norm_nonneg _) hm.le)
  have hu : M.continuousPerronFunction hM x ≤ ‖M.continuousPerronFunction hM‖ := by
    simpa only [Real.norm_eq_abs,
      abs_of_pos (show 0 < M.continuousPerronFunction hM x from
        M.perronFunction_pos hM x)] using
      (M.continuousPerronFunction hM).norm_coe_le_norm x
  have hchain := mixedPathOperatorProduct_perron_dominated
    M hM as f (‖f‖ / m) (div_nonneg (norm_nonneg _) hm.le) hf x
  calc
    ‖mixedPathOperatorProduct M.bjrModel as f x‖ ≤
        (P * (‖f‖ / m)) * M.continuousPerronFunction hM x := hchain
    _ ≤ (P * (‖f‖ / m)) * ‖M.continuousPerronFunction hM‖ :=
      mul_le_mul_of_nonneg_left hu
        (mul_nonneg hP (div_nonneg (norm_nonneg _) hm.le))
    _ = ((‖M.continuousPerronFunction hM‖ / m) * P) * ‖f‖ := by ring

private theorem cycleDenominator_norm_one_le (n : ℕ) :
    1 ≤ ‖(2 : ℂ) * ((n : ℂ) + 3)‖ := by
  rw [norm_mul]
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  have hrest : ‖(n : ℂ) + 3‖ = (n : ℝ) + 3 := by
    rw [show (n : ℂ) + 3 = (((n : ℝ) + 3 : ℝ) : ℂ) by norm_num,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [htwo, hrest]
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The operator norm of every homogeneous cycle coefficient is bounded by
one model-dependent constant, uniformly in the cycle length. -/
theorem norm_profileSimpleCycleCoeff_le
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (m : ℝ) (hm : 0 < m)
    (hmu : ∀ x, m ≤ M.continuousPerronFunction hM x) (n : ℕ) :
    ‖profileSimpleCycleCoeff M.bjrModel n‖ ≤
      (‖M.continuousPerronFunction hM‖ / m) * ‖M.bjrModel.kernel.toContinuousMap‖ := by
  let C : ℝ :=
    (‖M.continuousPerronFunction hM‖ / m) * ‖M.bjrModel.kernel.toContinuousMap‖
  have hC : 0 ≤ C := by positivity
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro a
  have hchain := norm_mixedPathOperatorProduct_le M hM
    (List.ofFn (fun i : Fin (n + 2) => a i.castSucc)) m hm hmu
  have hpair := JS.norm_operatorCyclePairing_le M.bjrModel
    (mixedPathOperatorProduct M.bjrModel
      (List.ofFn (fun i : Fin (n + 2) => a i.castSucc)))
    (a (Fin.last (n + 2)))
  have hden := cycleDenominator_norm_one_le n
  rw [profileSimpleCycleCoeff_apply, norm_div]
  calc
    ‖JS.operatorCyclePairing M.bjrModel
        (mixedPathOperatorProduct M.bjrModel
          (List.ofFn (fun i : Fin (n + 2) => a i.castSucc)))
        (a (Fin.last (n + 2)))‖ /
          ‖(2 : ℂ) * ((n : ℂ) + 3)‖ ≤
        ‖JS.operatorCyclePairing M.bjrModel
          (mixedPathOperatorProduct M.bjrModel
            (List.ofFn (fun i : Fin (n + 2) => a i.castSucc)))
          (a (Fin.last (n + 2)))‖ := by
      exact (div_le_iff₀ (by positivity)).2
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hden (norm_nonneg _))
    _ ≤ ‖mixedPathOperatorProduct M.bjrModel
          (List.ofFn (fun i : Fin (n + 2) => a i.castSucc))‖ *
          ‖M.bjrModel.kernel.toContinuousMap‖ * ‖a (Fin.last (n + 2))‖ := hpair
    _ ≤ ((‖M.continuousPerronFunction hM‖ / m) *
          ((List.ofFn (fun i : Fin (n + 2) =>
            a i.castSucc)).map norm).prod) *
          ‖M.bjrModel.kernel.toContinuousMap‖ * ‖a (Fin.last (n + 2))‖ := by
      gcongr
    _ = C * ∏ i, ‖a i‖ := by
      rw [List.map_ofFn, Fin.prod_ofFn]
      rw [show (∏ i : Fin (n + 3), ‖a i‖) =
          (∏ i : Fin (n + 2), ‖a i.castSucc‖) *
            ‖a (Fin.last (n + 2))‖ from
        Fin.prod_univ_castSucc (fun i : Fin (n + 3) => ‖a i‖)]
      dsimp [C]
      ring

/-- The homogeneous coefficients of the formal series have one uniform
model-dependent bound. -/
theorem norm_profileSimpleCycleFMS_le
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (m : ℝ) (hm : 0 < m)
    (hmu : ∀ x, m ≤ M.continuousPerronFunction hM x) (k : ℕ) :
    ‖profileSimpleCycleFMS M.bjrModel k‖ ≤
      (‖M.continuousPerronFunction hM‖ / m) * ‖M.bjrModel.kernel.toContinuousMap‖ := by
  have hC : 0 ≤
      (‖M.continuousPerronFunction hM‖ / m) * ‖M.bjrModel.kernel.toContinuousMap‖ := by
    positivity
  cases k with
  | zero => simpa using hC
  | succ k =>
      cases k with
      | zero => simpa using hC
      | succ k =>
          cases k with
          | zero => simpa using hC
          | succ n =>
              simpa [profileSimpleCycleFMS]
                using norm_profileSimpleCycleCoeff_le M hM m hm hmu n

/-- The origin-centred profile cycle series has convergence radius at least
one in the profile sup norm. -/
theorem profileSimpleCycleFMS_one_le_radius
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    (1 : ℝ≥0∞) ≤ (profileSimpleCycleFMS M.bjrModel).radius := by
  obtain ⟨m, hm, hmu⟩ := perronFunction_uniform_pos M hM
  let C : ℝ :=
    (‖M.continuousPerronFunction hM‖ / m) * ‖M.bjrModel.kernel.toContinuousMap‖
  apply (profileSimpleCycleFMS M.bjrModel).le_radius_of_bound C
    (r := (1 : ℝ≥0))
  intro k
  simpa only [NNReal.coe_one, one_pow, mul_one] using
    norm_profileSimpleCycleFMS_le M hM m hm hmu k

/-! ## Identification of the formal sum with the existing cycle series -/

private theorem summable_profileSimpleCycleTerm_of_norm_lt_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : Profile S) (htau : ‖tau‖ < 1) :
    Summable (fun n : ℕ => JS.profileSimpleCycleTerm M.bjrModel tau n) := by
  obtain ⟨m, hm, hmu⟩ := perronFunction_uniform_pos M hM
  let D : ℝ := ‖M.bjrModel.kernel.toContinuousMap‖ *
    ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
    (‖M.continuousPerronFunction hM‖ / m) * ‖tau‖ ^ 3
  have hgeom : Summable (fun n : ℕ => ‖tau‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg tau) htau
  have hmajor : Summable (fun n : ℕ => D * ‖tau‖ ^ n) :=
    hgeom.mul_left D
  apply Summable.of_norm_bounded hmajor
  intro n
  simpa only [D] using
    JS.norm_profileSimpleCycleTerm_le M hM tau ‖tau‖ m
      (norm_nonneg tau) (fun x => tau.norm_coe_le_norm x) hm hmu n

/-- On the open unit profile ball, the shifted formal series sums to the
already-defined profile simple-cycle series. -/
theorem profileSimpleCycleFMS_hasSum_of_norm_lt_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : Profile S) (htau : ‖tau‖ < 1) :
    HasSum (fun k : ℕ => profileSimpleCycleFMS M.bjrModel k (fun _ => tau))
      (JS.profileSimpleCycleSeries M.bjrModel tau) := by
  have hterms :=
    summable_profileSimpleCycleTerm_of_norm_lt_one M hM tau htau
  have hshift :
      HasSum (fun k : ℕ => profileSimpleCycleFMS M.bjrModel k (fun _ => tau))
        (profileSimpleCycleFMS M.bjrModel 0 (fun _ => tau) +
          (profileSimpleCycleFMS M.bjrModel 1 (fun _ => tau) +
            (profileSimpleCycleFMS M.bjrModel 2 (fun _ => tau) +
              JS.profileSimpleCycleSeries M.bjrModel tau))) := by
    apply HasSum.zero_add
    apply HasSum.zero_add
    apply HasSum.zero_add
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
      profileSimpleCycleFMS_apply_diag_add_three,
      JS.profileSimpleCycleSeries] using hterms.hasSum
  simpa [profileSimpleCycleFMS] using hshift

/-- At every point of the open unit profile ball, the formal sum agrees
with the existing direct cycle series. -/
theorem profileSimpleCycleFMS_sum_eq_of_norm_lt_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : Profile S) (htau : ‖tau‖ < 1) :
    (profileSimpleCycleFMS M.bjrModel).sum tau =
      JS.profileSimpleCycleSeries M.bjrModel tau := by
  exact (profileSimpleCycleFMS_hasSum_of_norm_lt_one
    M hM tau htau).tsum_eq

/-- The existing profile simple-cycle series has the explicit formal
multilinear series above on the full unit ball centred at zero. -/
theorem profileSimpleCycleSeries_hasFPowerSeriesOnBall_unit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    HasFPowerSeriesOnBall (JS.profileSimpleCycleSeries M.bjrModel)
      (profileSimpleCycleFMS M.bjrModel) 0 (1 : ℝ≥0∞) where
  r_le := profileSimpleCycleFMS_one_le_radius M hM
  r_pos := by norm_num
  hasSum := by
    intro tau htau
    have htau' : ‖tau‖ < 1 := by
      rw [← ENNReal.coe_one, Metric.eball_coe] at htau
      simpa only [NNReal.coe_one, Metric.mem_ball, dist_zero_right] using htau
    simpa only [zero_add] using
      profileSimpleCycleFMS_hasSum_of_norm_lt_one M hM tau htau'

/-- The direct profile simple-cycle series is complex analytic throughout
the open unit ball of the Banach space `C(S, ℂ)`. -/
theorem profileSimpleCycleSeries_analyticOnNhd_unitBall
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    AnalyticOnNhd ℂ (JS.profileSimpleCycleSeries M.bjrModel)
      (Metric.ball (0 : Profile S) 1) := by
  have h :=
    (profileSimpleCycleSeries_hasFPowerSeriesOnBall_unit M hM).analyticOnNhd
  rw [← ENNReal.coe_one, Metric.eball_coe] at h
  simpa only [NNReal.coe_one] using h


end PerronWright.FiniteIrreducibleProfileSimpleCyclePowerSeries
