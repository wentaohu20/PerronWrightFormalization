import PerronWright.Analysis.FiniteIrreducibleJointPhysicalFold
import PerronWright.Analysis.FiniteIrreducibleTreeSeries
import PerronWright.Transfer.CartesianDeltaSqrt
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The genuine finite irreducible normalized activity and fold profile

The literal finite irreducible model is used without a primitive/B2 adapter.
The normalized activity variable is `w`, whereas the actual tree residual is
evaluated at activity `rho(g) * w`.  This file constructs that analytic base
change from the proved critical radius and composes the proved joint fold
chart with the canonical Cartesian-Delta coordinate `sqrt(1-w)`.

At zero field the normalized fold profile is identified with the actual
rooted-tree series on a genuine complex lens.  A joint-field overlap with the
unit-away continuation still requires an additional geometric shrinking.
-/

open Filter Topology
open scoped Classical ComplexOrder ENNReal NNReal

noncomputable section

namespace PerronWright.FiniteIrreducibleNormalizedFoldActivity

open PerronWright

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The actual activity/field pair corresponding to normalized coordinates
`(w,g)`: the activity is rescaled by the proved analytic critical radius. -/
def activityMap (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : ℂ × C(S, ℂ)) : ℂ × C(S, ℂ) :=
  (FiniteIrreducibleRadiusResponse.radius M hM q.2 * q.1, q.2)

@[simp] theorem activityMap_zeroField (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (w : ℂ) :
    activityMap M hM (w, 0) = (w, 0) := by
  simp only [activityMap, FiniteIrreducibleRadiusResponse.radius_base, one_mul]

/-- On a genuine field cylinder, the normalized-to-actual activity map is
analytic.  The same field ball keeps the critical radius nonzero; no
restriction on the normalized activity coordinate is needed. -/
theorem exists_activityMap_analytic_field_ball
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ ε : ℝ, 0 < ε ∧
      AnalyticOnNhd ℂ (activityMap M hM)
        (Set.univ ×ˢ Metric.ball (0 : C(S, ℂ)) ε) ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) ε,
        FiniteIrreducibleRadiusResponse.radius M hM g ≠ 0 := by
  have hρa := FiniteIrreducibleRadiusResponse.radius_analytic M hM
  have hρne : ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      FiniteIrreducibleRadiusResponse.radius M hM g ≠ 0 :=
    hρa.continuousAt.eventually_ne (by
      rw [FiniteIrreducibleRadiusResponse.radius_base]
      exact one_ne_zero)
  have hgood : ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      AnalyticAt ℂ (FiniteIrreducibleRadiusResponse.radius M hM) g ∧
        FiniteIrreducibleRadiusResponse.radius M hM g ≠ 0 :=
    hρa.eventually_analyticAt.and hρne
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨ε, hε, ?_, fun g hg => (hball hg).2⟩
  intro q hq
  have hρ : AnalyticAt ℂ
      (fun p : ℂ × C(S, ℂ) => FiniteIrreducibleRadiusResponse.radius M hM p.2) q :=
      (hball hq.2).1.comp_of_eq analyticAt_snd rfl
  exact (hρ.mul analyticAt_fst).prod analyticAt_snd

/-- A canonical choice of the genuine joint fold profile which retains both
the residual equation and its identification with the physical least branch
on the near-critical real slice. -/
def foldProfile (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    C(S, ℂ) × ℂ → C(S, ℂ) :=
  Classical.choose
    (FiniteIrreducibleJointPhysicalFold.least_fixed_on_new_joint_chart_near_one M hM)

theorem foldProfile_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (foldProfile M hM) (0, 0) :=
  (Classical.choose_spec
    (FiniteIrreducibleJointPhysicalFold.least_fixed_on_new_joint_chart_near_one M hM)).1

theorem foldProfile_base (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    foldProfile M hM (0, 0) = 1 :=
  (Classical.choose_spec
    (FiniteIrreducibleJointPhysicalFold.least_fixed_on_new_joint_chart_near_one M hM)).2.1

theorem foldProfile_vertical_deriv (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    deriv (fun X : ℂ => foldProfile M hM (0, X)) 0 =
      (-(FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ)) • M.complexPerronFunction hM :=
  (Classical.choose_spec
    (FiniteIrreducibleJointPhysicalFold.least_fixed_on_new_joint_chart_near_one M hM)).2.2.1

theorem foldProfile_critical_axis (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ g : C(S, ℂ) in nhds 0,
      foldProfile M hM (g, 0) = FiniteIrreducibleRadiusResponse.profile M hM g :=
  (Classical.choose_spec
    (FiniteIrreducibleJointPhysicalFold.least_fixed_on_new_joint_chart_near_one M hM)).2.2.2.1

/-- The chosen profile solves the genuine field-dependent tree residual at
the actual activity `rho(g) * (1-X^2)`. -/
theorem foldProfile_residual (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      M.treeResidual
        ((FiniteIrreducibleRadiusResponse.radius M hM q.1 * (1 - q.2 ^ 2), q.1),
          foldProfile M hM q) = 0 :=
  (Classical.choose_spec
    (FiniteIrreducibleJointPhysicalFold.least_fixed_on_new_joint_chart_near_one M hM)).2.2.2.2.1

/-- On a sufficiently near-critical real subinterval, the selected joint
fold profile is exactly the actual rooted-tree Taylor series. -/
theorem foldProfile_eq_rootedTreeSeries_real_near_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, 0 ≤ w → w < 1 → |w - 1| < δ →
      foldProfile M hM (0, (Real.sqrt (1 - w) : ℂ)) =
        M.bjrModel.rootedTreeSeries (w : ℂ) := by
  obtain ⟨δ, hδ, hphysical⟩ := (Classical.choose_spec
    (FiniteIrreducibleJointPhysicalFold.least_fixed_on_new_joint_chart_near_one M hM)).2.2.2.2.2
  refine ⟨δ, hδ, ?_⟩
  intro w hw hw1 hclose
  obtain ⟨V, hVlim, -, hfold⟩ := hphysical w hw hw1 hclose
  obtain ⟨W, hWlim, -, -, hseries⟩ :=
    M.rootedTreeSeries_eq_least_fixedPoint w hw hw1
  have hVW : V = W := tendsto_nhds_unique hVlim hWlim
  exact hfold.trans (by rw [hVW]; exact hseries.symm)

/-- The local part of the Cartesian Delta-domain on which the selected
square-root coordinate lies in the fold chart's radius-`r` input ball. -/
def localCartesianDelta (η m r : ℝ) : Set ℂ :=
  Transfer.cartesianDelta η m ∩
    Transfer.cartesianDeltaSqrt ⁻¹' Metric.ball (0 : ℂ) r

theorem isOpen_localCartesianDelta {η m r : ℝ} (hm : 0 ≤ m) :
    IsOpen (localCartesianDelta η m r) := by
  have hcont : ContinuousOn Transfer.cartesianDeltaSqrt
      (Transfer.cartesianDelta η m) := by
    intro w hw
    exact ((Transfer.analyticOnNhd_cartesianDeltaSqrt hm) w hw).continuousAt.continuousWithinAt
  exact hcont.isOpen_inter_preimage
    (Transfer.isOpen_cartesianDelta η m) Metric.isOpen_ball

/-- The joint fold profile expressed in normalized `(w,g)` coordinates. -/
def normalizedFoldProfile (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : ℂ × C(S, ℂ)) : C(S, ℂ) :=
  foldProfile M hM (q.2, Transfer.cartesianDeltaSqrt q.1)

/-- The normalized fold profile therefore meets the actual rooted-tree
series on the same near-critical real subinterval. -/
theorem normalizedFoldProfile_eq_rootedTreeSeries_real_near_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, 0 ≤ w → w < 1 → |w - 1| < δ →
      normalizedFoldProfile M hM ((w : ℂ), 0) =
        M.bjrModel.rootedTreeSeries (w : ℂ) := by
  obtain ⟨δ, hδ, hseed⟩ :=
    foldProfile_eq_rootedTreeSeries_real_near_one M hM
  refine ⟨δ, hδ, ?_⟩
  intro w hw hw1 hclose
  have hnonneg : 0 ≤ ((1 - w : ℝ) : ℂ) := by
    exact_mod_cast (sub_nonneg.mpr hw1.le)
  have hsqrt : Transfer.cartesianDeltaSqrt (w : ℂ) =
      (Real.sqrt (1 - w) : ℂ) := by
    rw [Transfer.cartesianDeltaSqrt]
    simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.ofReal_re] using
      (Complex.sqrt_of_nonneg hnonneg)
  simp only [normalizedFoldProfile, hsqrt]
  exact hseed w hw hw1 hclose

/-- On one genuine open product cut out by the proved fold germ, the
analytic critical-radius field ball, and the canonical Cartesian-Delta
square root, both the actual activity and normalized profile are jointly
analytic.  The critical radius is nonzero there, and the profile solves the
actual tree equation at activity `rho(g) * w`. -/
theorem exists_normalizedFoldProfile_cartesianDelta_product
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {η m : ℝ} (hm : 0 ≤ m) :
    ∃ r : ℝ, 0 < r ∧
      IsOpen (localCartesianDelta η m r ×ˢ
        Metric.ball (0 : C(S, ℂ)) r) ∧
      AnalyticOnNhd ℂ (activityMap M hM)
        (localCartesianDelta η m r ×ˢ
          Metric.ball (0 : C(S, ℂ)) r) ∧
      AnalyticOnNhd ℂ (normalizedFoldProfile M hM)
        (localCartesianDelta η m r ×ˢ
          Metric.ball (0 : C(S, ℂ)) r) ∧
      ∀ q ∈ localCartesianDelta η m r ×ˢ
          Metric.ball (0 : C(S, ℂ)) r,
        FiniteIrreducibleRadiusResponse.radius M hM q.2 ≠ 0 ∧
          M.treeResidual
            (activityMap M hM q, normalizedFoldProfile M hM q) = 0 ∧
          normalizedFoldProfile M hM q =
            (FiniteIrreducibleRadiusResponse.radius M hM q.2 * q.1) •
              NormedSpace.exp
                (q.2 - TreeCritical.degree M.bjrModel +
                  M.complexOperator
                    (normalizedFoldProfile M hM q)) := by
  have hgood : ∀ᶠ p : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      AnalyticAt ℂ (foldProfile M hM) p ∧
      M.treeResidual
        ((FiniteIrreducibleRadiusResponse.radius M hM p.1 * (1 - p.2 ^ 2), p.1),
          foldProfile M hM p) = 0 :=
    (foldProfile_analytic M hM).eventually_analyticAt.and
      (foldProfile_residual M hM)
  obtain ⟨rFold, hrFold, hball⟩ := Metric.mem_nhds_iff.mp hgood
  obtain ⟨rRadius, hrRadius, hActivity, hRadiusNe⟩ :=
    exists_activityMap_analytic_field_ball M hM
  let r : ℝ := min rFold rRadius
  have hr : 0 < r := lt_min hrFold hrRadius
  let D : Set (ℂ × C(S, ℂ)) :=
    localCartesianDelta η m r ×ˢ Metric.ball (0 : C(S, ℂ)) r
  have hDopen : IsOpen D :=
    (isOpen_localCartesianDelta hm).prod Metric.isOpen_ball
  refine ⟨r, hr, hDopen, ?_, ?_, ?_⟩
  · intro q hq
    exact hActivity q ⟨Set.mem_univ _,
      Metric.ball_subset_ball (min_le_right rFold rRadius) hq.2⟩
  · intro q hq
    have hX : AnalyticAt ℂ
        (fun p : ℂ × C(S, ℂ) => Transfer.cartesianDeltaSqrt p.1) q :=
      ((Transfer.analyticOnNhd_cartesianDeltaSqrt hm) q.1 hq.1.1).comp_of_eq
        analyticAt_fst rfl
    have hinput : (q.2, Transfer.cartesianDeltaSqrt q.1) ∈
        Metric.ball ((0 : C(S, ℂ)), (0 : ℂ)) rFold := by
      rw [← ball_prod_same]
      exact ⟨Metric.ball_subset_ball (min_le_left rFold rRadius) hq.2,
        Metric.ball_subset_ball (min_le_left rFold rRadius) hq.1.2⟩
    have hchart := (hball hinput).1
    exact hchart.comp_of_eq (analyticAt_snd.prod hX) rfl
  · intro q hq
    have hinput : (q.2, Transfer.cartesianDeltaSqrt q.1) ∈
        Metric.ball ((0 : C(S, ℂ)), (0 : ℂ)) rFold := by
      rw [← ball_prod_same]
      exact ⟨Metric.ball_subset_ball (min_le_left rFold rRadius) hq.2,
        Metric.ball_subset_ball (min_le_left rFold rRadius) hq.1.2⟩
    have hres := (hball hinput).2
    have hres' : M.treeResidual
        (activityMap M hM q, normalizedFoldProfile M hM q) = 0 := by
      simpa only [activityMap, normalizedFoldProfile,
        Transfer.cartesianDeltaSqrt_sq, sub_sub_cancel] using hres
    refine ⟨hRadiusNe q.2
      (Metric.ball_subset_ball (min_le_right rFold rRadius) hq.2), hres', ?_⟩
    change normalizedFoldProfile M hM q -
      (FiniteIrreducibleRadiusResponse.radius M hM q.2 * q.1) •
        NormedSpace.exp
          (q.2 - TreeCritical.degree M.bjrModel +
            M.complexOperator
              (normalizedFoldProfile M hM q)) = 0 at hres'
    exact sub_eq_zero.mp hres'

/-- The normalized fold profile agrees with the canonical rooted-tree series
on a genuine complex lens about the subcritical side of `w = 1`. -/
theorem exists_normalizedFoldProfile_eq_rootedTreeSeries_on_lens
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ r : ℝ, 0 < r ∧
      Set.EqOn
        (fun w : ℂ => normalizedFoldProfile M hM (w, 0))
        M.bjrModel.rootedTreeSeries
        (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (r ^ 2)) := by
  obtain ⟨r, hr, -, -, hfold, -⟩ :=
    exists_normalizedFoldProfile_cartesianDelta_product
      M hM (η := 1) (m := 0) (by norm_num)
  obtain ⟨δ, hδ, hrealSeed⟩ :=
    normalizedFoldProfile_eq_rootedTreeSeries_real_near_one M hM
  let U : Set ℂ :=
    Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (r ^ 2)
  let f : ℂ → C(S, ℂ) :=
    normalizedFoldProfile M hM ∘ fun w => (w, 0)
  let g : ℂ → C(S, ℂ) := M.bjrModel.rootedTreeSeries

  have hUlocal : U ⊆ localCartesianDelta 1 0 r := by
    intro w hw
    refine ⟨Transfer.unit_ball_subset_cartesianDelta (by norm_num) hw.1, ?_⟩
    have hnorm : ‖1 - w‖ < r ^ 2 := by
      have hw' := hw.2
      rw [Metric.mem_ball, Complex.dist_eq, norm_sub_rev] at hw'
      exact hw'
    have hsquare : ‖Transfer.cartesianDeltaSqrt w‖ ^ 2 = ‖1 - w‖ := by
      rw [← norm_pow, Transfer.cartesianDeltaSqrt_sq]
    have hsqrt : ‖Transfer.cartesianDeltaSqrt w‖ < r := by
      nlinarith [norm_nonneg (Transfer.cartesianDeltaSqrt w)]
    change Transfer.cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) r
    simpa only [Metric.mem_ball, dist_zero_right] using hsqrt

  have hf : AnalyticOnNhd ℂ f U := by
    intro w hw
    have hpair : (w, (0 : C(S, ℂ))) ∈
        localCartesianDelta 1 0 r ×ˢ Metric.ball (0 : C(S, ℂ)) r :=
      ⟨hUlocal hw, Metric.mem_ball_self hr⟩
    simpa only [f, id_eq] using
      (hfold (w, (0 : C(S, ℂ))) hpair).comp_of_eq
        (analyticAt_id.prod analyticAt_const) rfl

  have hg : AnalyticOnNhd ℂ g U := by
    intro w hw
    have hwUnit : w ∈ Metric.eball 0 (1 : ℝ≥0∞) := by
      rw [← ENNReal.coe_one, Metric.eball_coe]
      simpa only [NNReal.coe_one] using hw.1
    have hwRadius : w ∈
        Metric.eball 0 M.bjrModel.complexTypeRootedTreeFMS.radius :=
      Metric.eball_subset_eball
        M.bjrModel.one_le_complexTypeRootedTreeFMS_radius hwUnit
    simpa only [g] using
      M.bjrModel.rootedTreeSeries_analyticOnNhd w hwRadius

  have hUpre : IsPreconnected U := by
    exact ((convex_ball (0 : ℂ) 1).inter
      (convex_ball (1 : ℂ) (r ^ 2))).isPreconnected

  have hbound : 0 < min δ (min (r ^ 2) 1) :=
    lt_min hδ (lt_min (pow_pos hr 2) zero_lt_one)
  obtain ⟨a, ha0, habound⟩ := exists_between hbound
  have haδ : a < δ :=
    habound.trans_le (min_le_left δ (min (r ^ 2) 1))
  have har : a < r ^ 2 :=
    habound.trans_le
      ((min_le_right δ (min (r ^ 2) 1)).trans
        (min_le_left (r ^ 2) 1))
  have ha1 : a < 1 :=
    habound.trans_le
      ((min_le_right δ (min (r ^ 2) 1)).trans
        (min_le_right (r ^ 2) 1))
  let w₀ : ℝ := 1 - a
  have hw₀0 : 0 < w₀ := by
    dsimp only [w₀]
    linarith
  have hw₀1 : w₀ < 1 := by
    dsimp only [w₀]
    linarith
  have hw₀sub : w₀ - 1 = -a := by
    dsimp only [w₀]
    ring
  have hw₀U : (w₀ : ℂ) ∈ U := by
    have hdist0 : dist (w₀ : ℂ) 0 = w₀ := by
      rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hw₀0]
    have hdist1 : dist (w₀ : ℂ) 1 = a := by
      rw [Complex.dist_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, hw₀sub, abs_neg,
        abs_of_pos ha0]
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_ball, hdist0] using hw₀1
    · simpa only [Metric.mem_ball, hdist1] using har

  have hw₀δBall : w₀ ∈ Metric.ball (1 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [hw₀sub, abs_neg, abs_of_pos ha0] using haδ

  have hreal : ∃ᶠ x : ℝ in 𝓝[≠] w₀,
      f (x : ℂ) = g (x : ℂ) := by
    have hδevent : ∀ᶠ x : ℝ in 𝓝 w₀,
        x ∈ Metric.ball (1 : ℝ) δ :=
      Metric.isOpen_ball.mem_nhds hw₀δBall
    apply Filter.Eventually.frequently
    filter_upwards [
      (eventually_ge_nhds hw₀0).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hw₀1).filter_mono nhdsWithin_le_nhds,
      hδevent.filter_mono nhdsWithin_le_nhds
    ] with x hx0 hx1 hxδ
    have hclose : |x - 1| < δ := by
      change dist x 1 < δ at hxδ
      rw [Real.dist_eq] at hxδ
      exact hxδ
    simpa only [f, g, Function.comp_apply] using
      hrealSeed x hx0 hx1 hclose

  have hcomplex : ∃ᶠ z : ℂ in 𝓝[≠] (w₀ : ℂ), f z = g z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hxs_tendsto, hxs_eq⟩ := hreal
    refine ⟨fun n => (xs n : ℂ), ?_, fun n => hxs_eq n⟩
    rw [tendsto_nhdsWithin_iff] at hxs_tendsto ⊢
    constructor
    · rw [tendsto_ofReal_iff]
      exact hxs_tendsto.1
    · simpa using hxs_tendsto.2

  refine ⟨r, hr, ?_⟩
  change Set.EqOn f g U
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hUpre hw₀U hcomplex

end PerronWright.FiniteIrreducibleNormalizedFoldActivity
