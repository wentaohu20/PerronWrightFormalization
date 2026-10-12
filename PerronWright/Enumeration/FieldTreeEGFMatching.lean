import PerronWright.Enumeration.FieldTreeGlobalDissymmetry

/-!
# The complex-field unrooted-tree EGF

This file connects the genuine finite complex-field tree weights with the
jointly analytic dissymmetry continuation.  The coefficient bridge is proved
from the finite rooted profile: integrating a profile with one fixed labelled
root gives the corresponding unrooted graph weight, and the change from
`(k-1)!` to `k!` is exactly the usual rooting factor `k`.

No continuation or coefficient estimate is assumed here.
-/

open Filter Topology MeasureTheory Set
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.FieldTreeEGFMatching

namespace MPR

export PerronWright.MarkedPathResolvent
  (scalarIntegralCLM scalarIntegralCLM_apply)

end MPR

namespace Global

export PerronWright.FieldTreeGlobalDissymmetry
  (exists_normalizedFieldTree_global_dissymmetry_profile)

end Global

namespace GC

export PerronWright.ZeroFieldTreeGlobalContinuation
  (treeDissymmetryFunctional)

end GC

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The literal unrooted-tree EGF at an arbitrary complex field. -/
def complexFieldTreeEGF (M : CompactBJRModel S) (g : C(S, ℂ)) :
    PowerSeries ℂ :=
  PowerSeries.mk (fun k ↦ if k = 0 then 0 else
    M.complexFieldConnectedWeight g k 0 / (k.factorial : ℂ))

@[simp] theorem complexFieldTreeEGF_coeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) (k : ℕ) :
    PowerSeries.coeff k (complexFieldTreeEGF M g) =
      if k = 0 then 0 else
        M.complexFieldConnectedWeight g k 0 / (k.factorial : ℂ) := by
  simp [complexFieldTreeEGF]

/-- The one-variable formal multilinear series of the literal complex-field
unrooted-tree coefficients. -/
def fieldTreeFMS (M : CompactBJRModel S) (g : C(S, ℂ)) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  oneDimensionalFormalMultilinearSeries (complexFieldTreeEGF M g)

/-- Pullback of the literal unrooted-tree EGF by the genuine critical
activity `z = rho(g) w`. -/
def normalizedFieldTreeFMS (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (g : C(S, ℂ)) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (fieldTreeFMS M g).compContinuousLinearMap
    ((RadiusResponse.radius M hM g) • ContinuousLinearMap.id ℂ ℂ)

/-- Integrating a finite rooted graph profile over its distinguished root
recovers the full complex graph weight. -/
theorem scalarIntegral_fixedRootedGraphProfileMap
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    MPR.scalarIntegralCLM M
        (FieldRootedTree.fixedRootedGraphProfileMap M g H v) =
      M.complexFieldGraphWeight g H := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ S) v
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) ↦ M.mu))
      (M.mu.prod (Measure.pi (fun _ : Fin n ↦ M.mu))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ M.mu) v
  have hf : Integrable
      (fun x : Fin (n + 1) → S ↦ M.complexFieldGraphIntegrand g H x)
      (Measure.pi (fun _ : Fin (n + 1) ↦ M.mu)) :=
    (M.complexFieldGraphIntegrand g H).continuous
      |>.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hprod : Integrable
      (fun p : S × (Fin n → S) ↦
        M.complexFieldGraphIntegrand g H (e.symm p))
      (M.mu.prod (Measure.pi (fun _ : Fin n ↦ M.mu))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  rw [MPR.scalarIntegralCLM_apply]
  change (∫ y : S, ∫ z : Fin n → S,
      M.complexFieldGraphIntegrand g H (Fin.insertNth v y z)
        ∂Measure.pi (fun _ : Fin n ↦ M.mu) ∂M.mu) = _
  calc
    _ = ∫ p : S × (Fin n → S),
          M.complexFieldGraphIntegrand g H (e.symm p)
          ∂M.mu.prod (Measure.pi (fun _ : Fin n ↦ M.mu)) := by
      rw [integral_prod _ hprod]
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk]
    _ = M.complexFieldGraphWeight g H := by
      exact hmp.symm.integral_comp' _

/-- The integral of the fixed-root numerator is the literal unrooted tree
weight on the same label set. -/
theorem scalarIntegral_numerator_eq_complexFieldConnectedWeight
    (M : CompactBJRModel S) (g : C(S, ℂ)) (n : ℕ) :
    MPR.scalarIntegralCLM M (FieldRootedTree.numerator M g n) =
      M.complexFieldConnectedWeight g (n + 1) 0 := by
  classical
  unfold FieldRootedTree.numerator CompactBJRModel.complexFieldConnectedWeight
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro H _hH
  have htree :
      (H.Connected ∧ H.edgeFinset.card = (n + 1) + 0 - 1) ↔
        H.IsTree := by
    simpa only [add_zero] using
      CompactBJRModel.connected_zero_surplus_iff_tree
        (Nat.zero_lt_succ n) H
  by_cases hT : H.IsTree
  · rw [if_pos hT, if_pos (htree.mpr hT)]
    exact scalarIntegral_fixedRootedGraphProfileMap M g H 0
  · rw [if_neg hT, if_neg (htree.not.mpr hT), map_zero]

/-- The scalar integral of the type-rooted coefficient is `k` times the
literal unrooted coefficient.  This is the finite enumerative rooting
identity in the complex field. -/
theorem scalarIntegral_series_coeff_eq_card_mul_tree_coeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) (k : ℕ) :
    MPR.scalarIntegralCLM M
        (PowerSeries.coeff k (FieldRootedTree.series M g)) =
      (k : ℂ) * PowerSeries.coeff k (complexFieldTreeEGF M g) := by
  cases k with
  | zero =>
      simp [FieldRootedTree.series_coeff_zero, complexFieldTreeEGF]
  | succ n =>
      rw [FieldRootedTree.series_coeff_succ]
      rw [FieldRootedTree.coefficient, map_smul,
        scalarIntegral_numerator_eq_complexFieldConnectedWeight]
      rw [complexFieldTreeEGF_coeff]
      simp only [Nat.succ_ne_zero, if_false, Nat.factorial_succ,
        Nat.cast_mul]
      have hnfac : (n.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      have hsucc : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      field_simp [hnfac, hsucc]
      simp [hnfac]

/-- Diagonal coefficients after a scalar change of activity acquire the
expected homogeneous factor. -/
theorem comp_smul_id_coeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : FormalMultilinearSeries ℂ ℂ E) (rho : ℂ) (n : ℕ) :
    (p.compContinuousLinearMap
      (rho • ContinuousLinearMap.id ℂ ℂ)).coeff n =
        rho ^ n • p.coeff n := by
  calc
    (p.compContinuousLinearMap
        (rho • ContinuousLinearMap.id ℂ ℂ)).coeff n =
        p n (fun _ : Fin n ↦ rho) := by
      rw [FormalMultilinearSeries.coeff,
        FormalMultilinearSeries.compContinuousLinearMap_apply]
      apply congrArg (p n)
      funext i
      simp
    _ = rho ^ n • p.coeff n := by
      rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The normalized scalar rooted series is the rooted derivative of the
normalized literal unrooted-tree series. -/
theorem normalized_scalarRootedFMS_eq_X_derivative
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (g : C(S, ℂ)) :
    oneDimensionalPowerSeries
        ((MPR.scalarIntegralCLM M).compFormalMultilinearSeries
          (FieldRootedTree.normalizedFMS M hM g)) =
      PowerSeries.X * PowerSeries.derivative ℂ
        (oneDimensionalPowerSeries (normalizedFieldTreeFMS M hM g)) := by
  apply PowerSeries.ext
  intro n
  rw [oneDimensionalPowerSeries_compContinuousLinearMap_coeff]
  cases n with
  | zero =>
      simp [FieldRootedTree.normalizedFMS, normalizedFieldTreeFMS,
        comp_smul_id_coeff, FieldRootedTree.fms,
        oneDimensionalFormalMultilinearSeries_coeff,
        FieldRootedTree.series_coeff_zero]
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      simp only [oneDimensionalPowerSeries_coeff,
        FieldRootedTree.normalizedFMS, normalizedFieldTreeFMS]
      rw [comp_smul_id_coeff, comp_smul_id_coeff]
      simp only [FieldRootedTree.fms,
        oneDimensionalFormalMultilinearSeries_coeff,
        fieldTreeFMS, map_smul, smul_eq_mul]
      rw [scalarIntegral_series_coeff_eq_card_mul_tree_coeff]
      push_cast
      ring

private theorem ContinuousLinearMap.comp_hasFPowerSeriesAt_local
    {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (L : A →L[ℂ] B) {f : ℂ → A}
    {p : FormalMultilinearSeries ℂ ℂ A}
    (hp : HasFPowerSeriesAt f p 0) :
    HasFPowerSeriesAt (fun z ↦ L (f z))
      (L.compFormalMultilinearSeries p) 0 := by
  obtain ⟨r, hr⟩ := hp
  exact ⟨r, by
    simpa only [Function.comp_def] using L.comp_hasFPowerSeriesOnBall hr⟩

private theorem hasFPowerSeriesAt_factorial_nsmul_coeff
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [CompleteSpace A]
    {f : ℂ → A} {p : FormalMultilinearSeries ℂ ℂ A} {z : ℂ}
    (hp : HasFPowerSeriesAt f p z) (n : ℕ) :
    n.factorial • p.coeff n = iteratedDeriv n f z := by
  obtain ⟨r, hr⟩ := hp
  have h := hr.factorial_smul (1 : ℂ) n
  simpa only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] using h

private theorem hasFPowerSeriesAt_mul_oneDimensional
    {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A]
    {f g : ℂ → A}
    {p q : FormalMultilinearSeries ℂ ℂ A}
    (hp : HasFPowerSeriesAt f p 0)
    (hq : HasFPowerSeriesAt g q 0) :
    HasFPowerSeriesAt (fun z ↦ f z * g z)
      (oneDimensionalFormalMultilinearSeries
        (oneDimensionalPowerSeries p * oneDimensionalPowerSeries q)) 0 := by
  obtain ⟨r, hr⟩ := hp.analyticAt.mul hq.analyticAt
  have hfun : f * g = fun z ↦ f z * g z := by rfl
  rw [hfun] at hr
  have hrPower : oneDimensionalPowerSeries r =
      oneDimensionalPowerSeries p * oneDimensionalPowerSeries q := by
    apply PowerSeries.ext
    intro n
    have hfac : (n.factorial : ℂ) ≠ 0 := by
      exact_mod_cast n.factorial_ne_zero
    apply smul_right_injective (R := ℂ) A hfac
    simp only [Algebra.smul_def, map_natCast]
    calc
      (n.factorial : A) *
          PowerSeries.coeff n (oneDimensionalPowerSeries r) =
          iteratedDeriv n (fun z ↦ f z * g z) 0 := by
        rw [oneDimensionalPowerSeries_coeff]
        simpa only [nsmul_eq_mul] using
          hasFPowerSeriesAt_factorial_nsmul_coeff hr n
      _ = ∑ j ∈ Finset.range (n + 1),
          (Nat.choose n j : A) * iteratedDeriv j f 0 *
            iteratedDeriv (n - j) g 0 := by
        exact iteratedDeriv_mul
          (hp.analyticAt.contDiffAt.of_le le_top)
          (hq.analyticAt.contDiffAt.of_le le_top)
      _ = (n.factorial : A) * PowerSeries.coeff n
          (oneDimensionalPowerSeries p * oneDimensionalPowerSeries q) := by
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp only [oneDimensionalPowerSeries_coeff, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hchoose := Nat.choose_mul_factorial_mul_factorial hjle
        have hchooseA :
            (Nat.choose n j : A) * (j.factorial : A) *
                ((n - j).factorial : A) = (n.factorial : A) := by
          simpa only [Nat.cast_mul] using
            congrArg (fun m : ℕ ↦ (m : A)) hchoose
        have hpj := hasFPowerSeriesAt_factorial_nsmul_coeff hp j
        have hqj :=
          hasFPowerSeriesAt_factorial_nsmul_coeff hq (n - j)
        simp only [nsmul_eq_mul] at hpj hqj
        rw [← hpj, ← hqj, ← hchooseA]
        ring
  have hrSeries : r = oneDimensionalFormalMultilinearSeries
      (oneDimensionalPowerSeries p * oneDimensionalPowerSeries q) := by
    rw [← oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries r,
      hrPower]
  simpa only [hrSeries] using hr

private theorem id_hasFPowerSeriesAt_X :
    HasFPowerSeriesAt (id : ℂ → ℂ)
      (oneDimensionalFormalMultilinearSeries
        (PowerSeries.X : PowerSeries ℂ)) 0 := by
  let L : ℂ →L[ℂ] ℂ := ContinuousLinearMap.id ℂ ℂ
  have hL := L.hasFPowerSeriesAt 0
  have hpower : oneDimensionalPowerSeries (L.fpowerSeries 0) =
      (PowerSeries.X : PowerSeries ℂ) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [oneDimensionalPowerSeries_coeff,
        FormalMultilinearSeries.coeff, L]
    | succ n =>
        cases n with
        | zero => simp [oneDimensionalPowerSeries_coeff,
            FormalMultilinearSeries.coeff, L]
        | succ n => simp [oneDimensionalPowerSeries_coeff,
            FormalMultilinearSeries.coeff, L,
            ContinuousLinearMap.fpowerSeries_apply_add_two,
            PowerSeries.coeff_X]
  have hseries : L.fpowerSeries 0 =
      oneDimensionalFormalMultilinearSeries
        (PowerSeries.X : PowerSeries ℂ) := by
    rw [← oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries
        (L.fpowerSeries 0), hpower]
  rw [hseries] at hL
  convert hL using 1
  funext z
  rfl

private theorem deriv_hasFPowerSeriesAt
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p 0) :
    HasFPowerSeriesAt (deriv f)
      (oneDimensionalFormalMultilinearSeries
        (PowerSeries.derivative ℂ (oneDimensionalPowerSeries p))) 0 := by
  let L : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
  obtain ⟨rho, hrho⟩ := hp
  have hfd0 : HasFPowerSeriesAt (fderiv ℂ f)
      p.derivSeries 0 := ⟨rho, hrho.fderiv⟩
  have hfd := ContinuousLinearMap.comp_hasFPowerSeriesAt_local L hfd0
  have hpower : oneDimensionalPowerSeries
      (L.compFormalMultilinearSeries p.derivSeries) =
        PowerSeries.derivative ℂ (oneDimensionalPowerSeries p) := by
    apply PowerSeries.ext
    intro n
    rw [oneDimensionalPowerSeries_compContinuousLinearMap_coeff,
      oneDimensionalPowerSeries_coeff]
    simp only [L, ContinuousLinearMap.apply_apply,
      FormalMultilinearSeries.derivSeries_coeff_one,
      PowerSeries.coeff_derivative, nsmul_eq_mul,
      oneDimensionalPowerSeries_coeff]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  have hseries : L.compFormalMultilinearSeries p.derivSeries =
      oneDimensionalFormalMultilinearSeries
        (PowerSeries.derivative ℂ (oneDimensionalPowerSeries p)) := by
    rw [← oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries
        (L.compFormalMultilinearSeries p.derivSeries), hpower]
  rw [hseries] at hfd
  convert hfd using 1
  funext z
  rfl

private theorem X_mul_deriv_hasFPowerSeriesAt
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p 0) :
    HasFPowerSeriesAt (fun w ↦ w * deriv f w)
      (oneDimensionalFormalMultilinearSeries
        (PowerSeries.X *
          PowerSeries.derivative ℂ (oneDimensionalPowerSeries p))) 0 := by
  simpa only [id_eq,
    oneDimensionalPowerSeries_oneDimensionalFormalMultilinearSeries] using
    hasFPowerSeriesAt_mul_oneDimensional
      id_hasFPowerSeriesAt_X (deriv_hasFPowerSeriesAt hp)

/-- On any fixed field in the terminal field ball, the actual joint
dissymmetry continuation has precisely the `rho(g)`-normalized Taylor series
of the literal finite unrooted-tree weights. -/
theorem normalizedFieldTreeFMS_hasFPowerSeriesAt_of_global_profile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {eta s : ℝ}
    {Theta : ℂ × C(S, ℂ) → C(S, ℂ)}
    {G : ℂ × C(S, ℂ) → ℂ}
    (heta : 0 < eta) (hs : 0 < s)
    (hTheta : AnalyticOnNhd ℂ Theta
      (Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s))
    (hG : AnalyticOnNhd ℂ G
      (Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s))
    (hData : ∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s,
      RadiusResponse.radius M hM q.2 ≠ 0 ∧
        TreeCritical.residual M
          (TreeNormalizedFoldActivity.activityMap M hM q, Theta q) = 0)
    (hGdef : ∀ q : ℂ × C(S, ℂ),
      G q = GC.treeDissymmetryFunctional M (Theta q))
    (hderiv : ∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s,
      q.1 ≠ 0 →
        deriv (fun w : ℂ ↦ G (w, q.2)) q.1 =
          MPR.scalarIntegralCLM M (Theta q) / q.1)
    {g : C(S, ℂ)} (hg : g ∈ Metric.ball 0 s) :
    HasFPowerSeriesAt (fun w : ℂ ↦ G (w, g))
      (normalizedFieldTreeFMS M hM g) 0 := by
  have hzeroDelta : (0 : ℂ) ∈ Transfer.cartesianDelta eta 0 :=
    Transfer.unit_ball_subset_cartesianDelta heta
      (Metric.mem_ball_self zero_lt_one)
  have hq0 : ((0 : ℂ), g) ∈
      Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s := ⟨hzeroDelta, hg⟩
  have hpTheta : HasFPowerSeriesAt (fun w : ℂ ↦ Theta (w, g))
      (FieldRootedTree.normalizedFMS M hM g) 0 :=
    FieldRootedTree.normalizedFMS_hasFPowerSeriesAt_of_cartesianDelta_profile
      M hM heta hs hTheta hData hg
  have hpRoot : HasFPowerSeriesAt
      (fun w : ℂ ↦ MPR.scalarIntegralCLM M (Theta (w, g)))
      ((MPR.scalarIntegralCLM M).compFormalMultilinearSeries
        (FieldRootedTree.normalizedFMS M hM g)) 0 :=
    ContinuousLinearMap.comp_hasFPowerSeriesAt_local
      (MPR.scalarIntegralCLM M) hpTheta
  have hGslice : AnalyticAt ℂ (fun w : ℂ ↦ G (w, g)) 0 :=
    (hG (0, g) hq0).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  obtain ⟨pG, hpG⟩ := hGslice
  have hTheta0 : Theta (0, g) = 0 := by
    have hres := (hData (0, g) hq0).2
    change Theta (0, g) -
      (RadiusResponse.radius M hM g * 0) •
        NormedSpace.exp
          (g - TreeCritical.degree M +
            M.kernel.complexActionCLM M.mu (Theta (0, g))) = 0 at hres
    simpa only [mul_zero, zero_smul, sub_zero] using hres
  have hG0 : G (0, g) = 0 := by
    rw [hGdef (0, g), hTheta0]
    simp [GC.treeDissymmetryFunctional]
  have hrootEq : ∀ᶠ w : ℂ in nhds 0,
      w * deriv (fun z : ℂ ↦ G (z, g)) w =
        MPR.scalarIntegralCLM M (Theta (w, g)) := by
    have hopen : IsOpen
        (Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) :=
      (Transfer.isOpen_cartesianDelta eta 0).prod Metric.isOpen_ball
    have hline : Tendsto (fun w : ℂ ↦ (w, g))
        (nhds 0) (nhds (0, g)) :=
      (continuousAt_id.prodMk continuousAt_const).tendsto
    filter_upwards [hline.eventually (hopen.mem_nhds hq0)] with w hw
    by_cases hw0 : w = 0
    · subst w
      simp only [zero_mul, hTheta0, map_zero]
    · rw [hderiv (w, g) hw hw0]
      field_simp [hw0]
  have hpRootFromG := X_mul_deriv_hasFPowerSeriesAt hpG
  have hseriesEq :=
    hpRootFromG.eq_formalMultilinearSeries_of_eventually hpRoot hrootEq
  have hpowerEq := congrArg oneDimensionalPowerSeries hseriesEq
  simp only [oneDimensionalPowerSeries_oneDimensionalFormalMultilinearSeries]
    at hpowerEq
  rw [normalized_scalarRootedFMS_eq_X_derivative M hM g] at hpowerEq
  have hpG0 : pG.coeff 0 = 0 := by
    have h := hpG.coeff_zero (fun _ : Fin 0 ↦ (1 : ℂ))
    simpa only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const_one, one_smul, hG0] using h
  have htarget0 : (normalizedFieldTreeFMS M hM g).coeff 0 = 0 := by
    simp [normalizedFieldTreeFMS, comp_smul_id_coeff, fieldTreeFMS,
      complexFieldTreeEGF]
  have hpPower : oneDimensionalPowerSeries pG =
      oneDimensionalPowerSeries (normalizedFieldTreeFMS M hM g) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
        simp only [oneDimensionalPowerSeries_coeff, hpG0, htarget0]
    | succ n =>
        have hc := congrArg (PowerSeries.coeff (n + 1)) hpowerEq
        simp only [PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_derivative, oneDimensionalPowerSeries_coeff]
          at hc
        have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        simp only [oneDimensionalPowerSeries_coeff]
        apply mul_right_cancel₀ hn
        simpa only [Nat.cast_add, Nat.cast_one] using hc
  have hpEq : pG = normalizedFieldTreeFMS M hM g := by
    rw [← oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries pG,
      hpPower,
      oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries]
  simpa only [hpEq] using hpG

/-- The concrete global field-tree dissymmetry profile therefore carries the
literal normalized unrooted-tree Taylor series on every fixed field in its
uniform field ball. -/
theorem exists_normalizedFieldTree_global_profile_with_TaylorSeries
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (eta r s : ℝ)
      (Theta : ℂ × C(S, ℂ) → C(S, ℂ))
      (G : ℂ × C(S, ℂ) → ℂ),
      0 < eta ∧ 0 < r ∧ 0 < s ∧
      AnalyticOnNhd ℂ Theta
        (Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      AnalyticOnNhd ℂ G
        (Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        RadiusResponse.radius M hM q.2 ≠ 0 ∧
          TreeCritical.residual M
            (TreeNormalizedFoldActivity.activityMap M hM q, Theta q) = 0) ∧
      Set.EqOn Theta
        (TreeNormalizedFoldActivity.normalizedFoldProfile M hM)
        (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ q : ℂ × C(S, ℂ),
        G q = GC.treeDissymmetryFunctional M (Theta q)) ∧
      Set.EqOn G
        (fun q ↦ GC.treeDissymmetryFunctional M
          (TreeNormalizedFoldActivity.normalizedFoldProfile M hM q))
        (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      Set.EqOn (fun w : ℂ ↦ G (w, 0))
        (PerronWright.ZeroFieldTreeEGFMatching.zeroFieldTreeSeries M)
        (Metric.ball (0 : ℂ) 1) ∧
      (∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        q.1 ≠ 0 →
          deriv (fun w : ℂ ↦ G (w, q.2)) q.1 =
            MPR.scalarIntegralCLM M (Theta q) / q.1) ∧
      (∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        HasFPowerSeriesAt (fun w : ℂ ↦ G (w, g))
          (normalizedFieldTreeFMS M hM g) 0) := by
  obtain ⟨eta, r, s, Theta, G, heta, hr, hs, hTheta, hG,
      hData, hThetaFold, hGdef, hGfold, hGinside, hderiv⟩ :=
    Global.exists_normalizedFieldTree_global_dissymmetry_profile M hM
  refine ⟨eta, r, s, Theta, G, heta, hr, hs, hTheta, hG,
    hData, hThetaFold, hGdef, hGfold, hGinside, hderiv, ?_⟩
  intro g hg
  apply normalizedFieldTreeFMS_hasFPowerSeriesAt_of_global_profile
    M hM heta hs hTheta hG hData hGdef hderiv hg

end PerronWright.FieldTreeEGFMatching
