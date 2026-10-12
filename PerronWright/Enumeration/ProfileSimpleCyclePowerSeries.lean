import PerronWright.Enumeration.JointSimpleCycleEGF
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Power series of the profile simple-cycle functional

This file packages the length-`n + 3` cycle functional as a continuous
`(n + 3)`-linear map.  The norm estimate is obtained directly from the
Perron gauge and is uniform in `n`; in particular it does not lose the unit
profile ball through the ambient operator norm of `tau ↦ K M_tau`.
-/

open MeasureTheory PerronWright
open scoped Topology RightActions BigOperators NNReal ENNReal

noncomputable section

namespace PerronWright.ProfileSimpleCyclePowerSeries

namespace JS

export PerronWright.JointSimpleCycleEGF
  (operatorCyclePairing operatorCyclePairingCLM
   operatorCyclePairingCLM_apply norm_operatorCyclePairing_le
   profileCycleTrace profileSimpleCycleTerm profileSimpleCycleSeries
   norm_profileSimpleCycleTerm_le)

end JS

namespace MPR

export PerronWright.MarkedPathResolvent (pathOperatorParameterCLM)

end MPR

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

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

/-! ## Mixed-profile Perron bounds -/

/-- One paper-oriented path operator `K M_a` multiplies the Perron gauge by
at most `‖a‖`. -/
theorem pathOperatorParameter_perron_dominated
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (a f : Profile S) (c : ℝ)
    (hf : ∀ y, ‖f y‖ ≤ c * M.perronFunction hM y) (x : S) :
    ‖MPR.pathOperatorParameterCLM M a f x‖ ≤
      (‖a‖ * c) * M.perronFunction hM x := by
  have haf : ∀ y, ‖(a * f) y‖ ≤
      (‖a‖ * c) * M.perronFunction hM y := by
    intro y
    rw [ContinuousMap.mul_apply, norm_mul]
    calc
      ‖a y‖ * ‖f y‖ ≤ ‖a‖ * ‖f y‖ := by
        gcongr
        exact a.norm_coe_le_norm y
      _ ≤ ‖a‖ * (c * M.perronFunction hM y) := by
        gcongr
        exact hf y
      _ = (‖a‖ * c) * M.perronFunction hM y := by ring
  rw [JointSimpleCycleEGF.pathOperatorParameterCLM_apply]
  simpa only [ContinuousKernel.complexActionCLM_apply] using
    TreeOuterNeumann.complexAction_perron_dominated
      M hM (‖a‖ * c) (a * f) haf x

/-- Ordered product of paper-oriented path operators.  The list order agrees
with operator multiplication, so its action is nested from right to left. -/
def mixedPathOperatorProduct (M : CompactBJRModel S)
    (as : List (Profile S)) : PathEnd S :=
  (as.map (MPR.pathOperatorParameterCLM M)).prod

/-- A mixed chain of profiles contracts the Perron gauge by the product of
their sup norms. -/
theorem mixedPathOperatorProduct_perron_dominated
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (as : List (Profile S)) (f : Profile S) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ y, ‖f y‖ ≤ c * M.perronFunction hM y) (x : S) :
    ‖mixedPathOperatorProduct M as f x‖ ≤
      ((as.map norm).prod * c) * M.perronFunction hM x := by
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
          ‖mixedPathOperatorProduct M as f y‖ ≤
            ((as.map norm).prod * c) * M.perronFunction hM y := by
        intro y
        exact ih f c hc hf y
      have hstep := pathOperatorParameter_perron_dominated
        M hM a (mixedPathOperatorProduct M as f)
        ((as.map norm).prod * c) htail x
      simpa only [mixedPathOperatorProduct, List.map_cons, List.prod_cons,
        mul_apply_eq_comp, mul_assoc] using hstep

/-- The Perron gauge gives a mixed-chain operator norm bound with no
exponential loss in the chain length. -/
theorem norm_mixedPathOperatorProduct_le
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (as : List (Profile S)) (m : ℝ) (hm : 0 < m)
    (hmu : ∀ x, m ≤ M.perronFunction hM x) :
    ‖mixedPathOperatorProduct M as‖ ≤
      (‖M.perronFunction hM‖ / m) * (as.map norm).prod := by
  let P : ℝ := (as.map norm).prod
  have hP : 0 ≤ P := by
    dsimp [P]
    apply List.prod_nonneg
    intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨a, -, rfl⟩ := hb
    exact norm_nonneg a
  have hC : 0 ≤ (‖M.perronFunction hM‖ / m) * P := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  apply (ContinuousMap.norm_le _
    (mul_nonneg hC (norm_nonneg f))).2
  intro x
  have hf : ∀ y, ‖f y‖ ≤
      (‖f‖ / m) * M.perronFunction hM y := by
    intro y
    calc
      ‖f y‖ ≤ ‖f‖ := f.norm_coe_le_norm y
      _ = (‖f‖ / m) * m := by field_simp
      _ ≤ (‖f‖ / m) * M.perronFunction hM y :=
        mul_le_mul_of_nonneg_left (hmu y)
          (div_nonneg (norm_nonneg _) hm.le)
  have hu : M.perronFunction hM x ≤ ‖M.perronFunction hM‖ := by
    simpa only [Real.norm_eq_abs,
      abs_of_pos (M.perronFunction_pos hM x)] using
      (M.perronFunction hM).norm_coe_le_norm x
  have hchain := mixedPathOperatorProduct_perron_dominated
    M hM as f (‖f‖ / m) (div_nonneg (norm_nonneg _) hm.le) hf x
  calc
    ‖mixedPathOperatorProduct M as f x‖ ≤
        (P * (‖f‖ / m)) * M.perronFunction hM x := hchain
    _ ≤ (P * (‖f‖ / m)) * ‖M.perronFunction hM‖ :=
      mul_le_mul_of_nonneg_left hu
        (mul_nonneg hP (div_nonneg (norm_nonneg _) hm.le))
    _ = ((‖M.perronFunction hM‖ / m) * P) * ‖f‖ := by ring

/-! ## Homogeneous cycle coefficients -/

/-- The ordered product of `n` path operators as an `n`-linear map of the
individual profiles. -/
def pathOperatorProductCMM (M : CompactBJRModel S) (n : ℕ) :
    Profile S [×n]→L[ℂ] PathEnd S :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n (PathEnd S)).compContinuousLinearMap
    (fun _ => MPR.pathOperatorParameterCLM M)

@[simp] theorem pathOperatorProductCMM_apply
    (M : CompactBJRModel S) (n : ℕ) (a : Fin n → Profile S) :
    pathOperatorProductCMM M n a =
      mixedPathOperatorProduct M (List.ofFn a) := by
  change (List.ofFn (fun i : Fin n =>
    MPR.pathOperatorParameterCLM M (a i))).prod =
      ((List.ofFn a).map (MPR.pathOperatorParameterCLM M)).prod
  rw [List.ofFn_comp']

/-- The unnormalised `(n + 3)`-linear cycle coefficient: the first `n + 2`
profiles decorate the path operators and the final profile closes the cycle. -/
def profileSimpleCycleCoeffRaw (M : CompactBJRModel S) (n : ℕ) :
    Profile S [×(n + 3)]→L[ℂ] ℂ :=
  ((JS.operatorCyclePairingCLM M).compContinuousMultilinearMap
    (pathOperatorProductCMM M (n + 2))).uncurryRight

@[simp] theorem profileSimpleCycleCoeffRaw_apply
    (M : CompactBJRModel S) (n : ℕ)
    (a : Fin (n + 3) → Profile S) :
    profileSimpleCycleCoeffRaw M n a =
      JS.operatorCyclePairing M
        (mixedPathOperatorProduct M
          (List.ofFn (fun i : Fin (n + 2) => a i.castSucc)))
        (a (Fin.last (n + 2))) := by
  change JS.operatorCyclePairingCLM M
      (pathOperatorProductCMM M (n + 2)
        (fun i : Fin (n + 2) => a i.castSucc))
      (a (Fin.last (n + 2))) = _
  rw [JS.operatorCyclePairingCLM_apply, pathOperatorProductCMM_apply]

/-- The normalised homogeneous coefficient of the profile simple-cycle
series. -/
def profileSimpleCycleCoeff (M : CompactBJRModel S) (n : ℕ) :
    Profile S [×(n + 3)]→L[ℂ] ℂ :=
  (((2 : ℂ) * ((n : ℂ) + 3))⁻¹) • profileSimpleCycleCoeffRaw M n

@[simp] theorem profileSimpleCycleCoeff_apply
    (M : CompactBJRModel S) (n : ℕ)
    (a : Fin (n + 3) → Profile S) :
    profileSimpleCycleCoeff M n a =
      JS.operatorCyclePairing M
        (mixedPathOperatorProduct M
          (List.ofFn (fun i : Fin (n + 2) => a i.castSucc)))
        (a (Fin.last (n + 2))) /
          ((2 : ℂ) * ((n : ℂ) + 3)) := by
  simp only [profileSimpleCycleCoeff, smul_apply, profileSimpleCycleCoeffRaw_apply,
    smul_eq_mul, inv_mul_eq_div]

/-- On the diagonal the multilinear coefficient is exactly the existing
length-`n + 3` simple-cycle term. -/
theorem profileSimpleCycleCoeff_apply_diag
    (M : CompactBJRModel S) (n : ℕ) (tau : Profile S) :
    profileSimpleCycleCoeff M n (fun _ => tau) =
      JS.profileSimpleCycleTerm M tau n := by
  rw [profileSimpleCycleCoeff_apply]
  simp only [List.ofFn_const, List.map_replicate,
    mixedPathOperatorProduct, List.prod_replicate,
    JS.profileSimpleCycleTerm, JS.profileCycleTrace]

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
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (m : ℝ) (hm : 0 < m)
    (hmu : ∀ x, m ≤ M.perronFunction hM x) (n : ℕ) :
    ‖profileSimpleCycleCoeff M n‖ ≤
      (‖M.perronFunction hM‖ / m) * ‖M.kernel.toContinuousMap‖ := by
  let C : ℝ :=
    (‖M.perronFunction hM‖ / m) * ‖M.kernel.toContinuousMap‖
  have hC : 0 ≤ C := by positivity
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro a
  have hchain := norm_mixedPathOperatorProduct_le M hM
    (List.ofFn (fun i : Fin (n + 2) => a i.castSucc)) m hm hmu
  have hpair := JS.norm_operatorCyclePairing_le M
    (mixedPathOperatorProduct M
      (List.ofFn (fun i : Fin (n + 2) => a i.castSucc)))
    (a (Fin.last (n + 2)))
  have hden := cycleDenominator_norm_one_le n
  rw [profileSimpleCycleCoeff_apply, norm_div]
  calc
    ‖JS.operatorCyclePairing M
        (mixedPathOperatorProduct M
          (List.ofFn (fun i : Fin (n + 2) => a i.castSucc)))
        (a (Fin.last (n + 2)))‖ /
          ‖(2 : ℂ) * ((n : ℂ) + 3)‖ ≤
        ‖JS.operatorCyclePairing M
          (mixedPathOperatorProduct M
            (List.ofFn (fun i : Fin (n + 2) => a i.castSucc)))
          (a (Fin.last (n + 2)))‖ := by
      exact (div_le_iff₀ (by positivity)).2
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hden (norm_nonneg _))
    _ ≤ ‖mixedPathOperatorProduct M
          (List.ofFn (fun i : Fin (n + 2) => a i.castSucc))‖ *
          ‖M.kernel.toContinuousMap‖ * ‖a (Fin.last (n + 2))‖ := hpair
    _ ≤ ((‖M.perronFunction hM‖ / m) *
          ((List.ofFn (fun i : Fin (n + 2) =>
            a i.castSucc)).map norm).prod) *
          ‖M.kernel.toContinuousMap‖ * ‖a (Fin.last (n + 2))‖ := by
      gcongr
    _ = C * ∏ i, ‖a i‖ := by
      rw [List.map_ofFn, Fin.prod_ofFn]
      rw [show (∏ i : Fin (n + 3), ‖a i‖) =
          (∏ i : Fin (n + 2), ‖a i.castSucc‖) *
            ‖a (Fin.last (n + 2))‖ from
        Fin.prod_univ_castSucc (fun i : Fin (n + 3) => ‖a i‖)]
      dsimp [C]
      ring

/-! ## The origin-centred formal multilinear series -/

/-- The profile simple-cycle formal series.  The first three homogeneous
coefficients vanish, and degree `n + 3` is the length-`n + 3` cycle
functional constructed above. -/
def profileSimpleCycleFMS (M : CompactBJRModel S) :
    FormalMultilinearSeries ℂ (Profile S) ℂ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | n + 3 => profileSimpleCycleCoeff M n

@[simp] theorem profileSimpleCycleFMS_apply_zero
    (M : CompactBJRModel S) : profileSimpleCycleFMS M 0 = 0 := rfl

@[simp] theorem profileSimpleCycleFMS_apply_one
    (M : CompactBJRModel S) : profileSimpleCycleFMS M 1 = 0 := rfl

@[simp] theorem profileSimpleCycleFMS_apply_two
    (M : CompactBJRModel S) : profileSimpleCycleFMS M 2 = 0 := rfl

@[simp] theorem profileSimpleCycleFMS_apply_add_three
    (M : CompactBJRModel S) (n : ℕ) :
    profileSimpleCycleFMS M (n + 3) = profileSimpleCycleCoeff M n := rfl

@[simp] theorem profileSimpleCycleFMS_apply_diag_add_three
    (M : CompactBJRModel S) (n : ℕ) (tau : Profile S) :
    profileSimpleCycleFMS M (n + 3) (fun _ => tau) =
      JS.profileSimpleCycleTerm M tau n := by
  rw [profileSimpleCycleFMS_apply_add_three,
    profileSimpleCycleCoeff_apply_diag]

/-- The homogeneous coefficients of the formal series have one uniform
model-dependent bound. -/
theorem norm_profileSimpleCycleFMS_le
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (m : ℝ) (hm : 0 < m)
    (hmu : ∀ x, m ≤ M.perronFunction hM x) (k : ℕ) :
    ‖profileSimpleCycleFMS M k‖ ≤
      (‖M.perronFunction hM‖ / m) * ‖M.kernel.toContinuousMap‖ := by
  have hC : 0 ≤
      (‖M.perronFunction hM‖ / m) * ‖M.kernel.toContinuousMap‖ := by
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
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (1 : ℝ≥0∞) ≤ (profileSimpleCycleFMS M).radius := by
  obtain ⟨m, hm, hmu⟩ := M.perronFunction_uniform_pos hM
  let C : ℝ :=
    (‖M.perronFunction hM‖ / m) * ‖M.kernel.toContinuousMap‖
  apply (profileSimpleCycleFMS M).le_radius_of_bound C
    (r := (1 : ℝ≥0))
  intro k
  simpa only [NNReal.coe_one, one_pow, mul_one] using
    norm_profileSimpleCycleFMS_le M hM m hm hmu k

/-! ## Identification of the formal sum with the existing cycle series -/

private theorem summable_profileSimpleCycleTerm_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau : Profile S) (htau : ‖tau‖ < 1) :
    Summable (fun n : ℕ => JS.profileSimpleCycleTerm M tau n) := by
  obtain ⟨m, hm, hmu⟩ := M.perronFunction_uniform_pos hM
  let D : ℝ := ‖M.kernel.toContinuousMap‖ *
    ‖M.kernel.complexActionCLM M.mu‖ *
    (‖M.perronFunction hM‖ / m) * ‖tau‖ ^ 3
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
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau : Profile S) (htau : ‖tau‖ < 1) :
    HasSum (fun k : ℕ => profileSimpleCycleFMS M k (fun _ => tau))
      (JS.profileSimpleCycleSeries M tau) := by
  have hterms :=
    summable_profileSimpleCycleTerm_of_norm_lt_one M hM tau htau
  have hshift :
      HasSum (fun k : ℕ => profileSimpleCycleFMS M k (fun _ => tau))
        (profileSimpleCycleFMS M 0 (fun _ => tau) +
          (profileSimpleCycleFMS M 1 (fun _ => tau) +
            (profileSimpleCycleFMS M 2 (fun _ => tau) +
              JS.profileSimpleCycleSeries M tau))) := by
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
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau : Profile S) (htau : ‖tau‖ < 1) :
    (profileSimpleCycleFMS M).sum tau =
      JS.profileSimpleCycleSeries M tau := by
  exact (profileSimpleCycleFMS_hasSum_of_norm_lt_one
    M hM tau htau).tsum_eq

/-- The existing profile simple-cycle series has the explicit formal
multilinear series above on the full unit ball centred at zero. -/
theorem profileSimpleCycleSeries_hasFPowerSeriesOnBall_unit
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    HasFPowerSeriesOnBall (JS.profileSimpleCycleSeries M)
      (profileSimpleCycleFMS M) 0 (1 : ℝ≥0∞) where
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
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticOnNhd ℂ (JS.profileSimpleCycleSeries M)
      (Metric.ball (0 : Profile S) 1) := by
  have h :=
    (profileSimpleCycleSeries_hasFPowerSeriesOnBall_unit M hM).analyticOnNhd
  rw [← ENNReal.coe_one, Metric.eball_coe] at h
  simpa only [NNReal.coe_one] using h

end PerronWright.ProfileSimpleCyclePowerSeries
