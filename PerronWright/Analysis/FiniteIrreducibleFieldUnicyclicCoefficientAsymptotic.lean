import PerronWright.Analysis.AnalyticVerticalDivision
import PerronWright.Analysis.FiniteIrreducibleFieldUnicyclicGlobalContinuation
import PerronWright.Enumeration.ZeroFieldUnicyclicActivitySingularity
import PerronWright.Transfer.LogarithmicCoefficient
import PerronWright.Transfer.UniformCartesianTransfer

/-!
# Field-uniform unicyclic coefficient asymptotics

The joint unicyclic continuation has the local form

`-(1/2) log X + H(g,X) + C₀(g)`,  `X = sqrt (1-w)`,

with `H(g,0)=0`.  Analytic vertical division writes `H(g,X)=X Q(g,X)`
near `(0,0)`, and local boundedness of the genuine analytic quotient `Q`
gives one bound, uniform on a fixed complex field ball.  Away from `w=1`
we thicken only the compact zero-field spine; no compactness of the field
ball is used.

The family-uniform Cartesian transfer theorem then gives constants `K,N`
chosen before the field `g`.  Finally the Taylor coefficient is identified
with the literal normalized connected-graph weight, rather than with an
auxiliary analytic continuation.
-/

open Filter Topology Set
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.FiniteIrreducibleFieldUnicyclicCoefficientAsymptotic

namespace Global

export PerronWright.FiniteIrreducibleFieldUnicyclicGlobalContinuation
  (exists_normalizedFieldUnicyclic_cartesianDelta_continuation)

end Global

namespace Local

export PerronWright.FiniteIrreducibleFieldUnicyclicLocalBridge
  (normalizedFieldUnicyclicFMS
   normalizedFieldUnicyclicFMS_coeff)

end Local

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- A compact collar containing the part of a positive-opening Cartesian
Delta-domain which stays a fixed distance from `1`. -/
private def cartesianDeltaAwayCompact (eta m delta : ℝ) : Set ℂ :=
  Metric.closedBall (0 : ℂ) (1 + eta) ∩
    {w : ℂ | delta ≤ dist w 1} ∩
      ({w : ℂ | (w - 1).re ≤ 0} ∪
        {w : ℂ | m * (w - 1).re ≤ |(w - 1).im|})

private theorem isCompact_cartesianDeltaAwayCompact
    (eta m delta : ℝ) :
    IsCompact (cartesianDeltaAwayCompact eta m delta) := by
  have haway : IsClosed {w : ℂ | delta ≤ dist w 1} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hleft : IsClosed {w : ℂ | (w - 1).re ≤ 0} :=
    isClosed_le (by fun_prop) continuous_const
  have hangular : IsClosed
      {w : ℂ | m * (w - 1).re ≤ |(w - 1).im|} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact ((isCompact_closedBall (0 : ℂ) (1 + eta)).inter_right
    haway).inter_right (hleft.union hangular)

private theorem cartesianDelta_away_subset_compact
    {eta m delta : ℝ} :
    {w : ℂ | w ∈ Transfer.cartesianDelta eta m ∧ delta ≤ dist w 1} ⊆
      cartesianDeltaAwayCompact eta m delta := by
  intro w hw
  refine ⟨⟨?_, hw.2⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1.1.le
  · by_cases hleft : (w - 1).re ≤ 0
    · exact Or.inl hleft
    · refine Or.inr ?_
      by_contra hangular
      apply hw.1.2
      exact ⟨(lt_of_not_ge hleft).le, (lt_of_not_ge hangular).le⟩

private theorem cartesianDelta_subset_slit
    {eta eta₀ m : ℝ} (heta : eta ≤ eta₀) (hm : 0 ≤ m) :
    Transfer.cartesianDelta eta m ⊆
      Transfer.cartesianDelta eta₀ 0 := by
  intro w hw
  refine ⟨by linarith [hw.1], ?_⟩
  rintro ⟨hre, him⟩
  apply hw.2
  refine ⟨hre, ?_⟩
  have him0 : |(w - 1).im| = 0 := by
    have : |(w - 1).im| ≤ 0 := by simpa using him
    exact le_antisymm this (abs_nonneg _)
  rw [him0]
  exact mul_nonneg hm hre

private theorem cartesianDeltaAwayCompact_subset_slit
    {eta eta₀ m delta : ℝ} (heta : eta < eta₀)
    (hm : 0 < m) (hdelta : 0 < delta) :
    cartesianDeltaAwayCompact eta m delta ⊆
      Transfer.cartesianDelta eta₀ 0 := by
  intro w hw
  refine ⟨?_, ?_⟩
  · have hnorm : ‖w‖ ≤ 1 + eta := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1.1
    linarith
  · rintro ⟨hre, him⟩
    have himAbs : |(w - 1).im| = 0 := by
      have : |(w - 1).im| ≤ 0 := by simpa using him
      exact le_antisymm this (abs_nonneg _)
    have hreEq : (w - 1).re = 0 := by
      rcases hw.2 with hleft | hangular
      · exact le_antisymm hleft hre
      · have hprod : m * (w - 1).re ≤ 0 := by
          change m * (w - 1).re ≤ |(w - 1).im| at hangular
          rw [himAbs] at hangular
          exact hangular
        nlinarith
    have himEq : (w - 1).im = 0 := abs_eq_zero.mp himAbs
    have hw1 : w = 1 := by
      have : w - 1 = 0 := by
        apply Complex.ext
        · simpa using hreEq
        · simpa using himEq
      exact sub_eq_zero.mp this
    subst w
    have haway := hw.1.2
    change delta ≤ dist (1 : ℂ) 1 at haway
    rw [dist_self] at haway
    exact (not_le_of_gt hdelta) haway

/-- Uniform boundedness transverse to a compact zero-parameter spine.
The field ball in the conclusion is not asserted to be compact. -/
private theorem exists_uniform_bound_on_compact_spine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {K : Set ℂ} (hK : IsCompact K)
    {D : Set (ℂ × E)} (hDopen : IsOpen D)
    {F : ℂ × E → ℂ} (hF : ContinuousOn F D)
    (hspine : K ×ˢ {(0 : E)} ⊆ D) :
    ∃ epsilon B : ℝ, 0 < epsilon ∧ 0 < B ∧
      ∀ w ∈ K, ∀ g ∈ Metric.ball (0 : E) epsilon,
        ‖F (w, g)‖ ≤ B := by
  let K₀ : Set (ℂ × E) := K ×ˢ {(0 : E)}
  have hK₀ : IsCompact K₀ := hK.prod isCompact_singleton
  have hFK₀ : ContinuousOn F K₀ := hF.mono hspine
  obtain ⟨A, hA⟩ := bddAbove_def.mp
    (hK₀.bddAbove_image hFK₀.norm)
  let B : ℝ := max A 0 + 1
  have hB : 0 < B := by
    dsimp only [B]
    linarith [le_max_right A 0]
  let V : Set (ℂ × E) := D ∩ F ⁻¹' Metric.ball (0 : ℂ) B
  have hVopen : IsOpen V := by
    dsimp only [V]
    exact hF.isOpen_inter_preimage hDopen Metric.isOpen_ball
  have hK₀V : K₀ ⊆ V := by
    intro q hq
    refine ⟨hspine hq, ?_⟩
    have hnorm : ‖F q‖ ≤ A :=
      hA ‖F q‖ (mem_image_of_mem (fun z : ℂ × E ↦ ‖F z‖) hq)
    have hlt : ‖F q‖ < B := by
      dsimp only [B]
      linarith [le_max_left A 0]
    change dist (F q) 0 < B
    simpa only [dist_zero_right] using hlt
  obtain ⟨epsilon, hepsilon, hthick⟩ :=
    hK₀.exists_thickening_subset_open hVopen hK₀V
  refine ⟨epsilon, B, hepsilon, hB, ?_⟩
  intro w hw g hg
  have hqthick : (w, g) ∈ Metric.thickening epsilon K₀ := by
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(w, (0 : E)), ⟨hw, Set.mem_singleton _⟩, ?_⟩
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by simpa using hepsilon,
      by simpa only [Metric.mem_ball] using hg⟩
  have hqV := hthick hqthick
  have hball : F (w, g) ∈ Metric.ball (0 : ℂ) B := hqV.2
  simpa only [dist_zero_right] using (Metric.mem_ball.mp hball).le

private theorem oneDimensionalFMS_eq_ofScalars
    (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    p = FormalMultilinearSeries.ofScalars ℂ (fun n ↦ p.coeff n) := by
  let P : PowerSeries ℂ := oneDimensionalPowerSeries p
  have hP : oneDimensionalFormalMultilinearSeries P =
      FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ PowerSeries.coeff n P) := by
    let c : ℕ → ℂ := fun n ↦ PowerSeries.coeff n P
    have hpower : oneDimensionalPowerSeries
        (FormalMultilinearSeries.ofScalars ℂ c) = P := by
      apply PowerSeries.ext
      intro n
      simp only [oneDimensionalPowerSeries_coeff,
        FormalMultilinearSeries.coeff_ofScalars, c]
    calc
      oneDimensionalFormalMultilinearSeries P =
          oneDimensionalFormalMultilinearSeries
            (oneDimensionalPowerSeries
              (FormalMultilinearSeries.ofScalars ℂ c)) :=
        congrArg oneDimensionalFormalMultilinearSeries hpower.symm
      _ = FormalMultilinearSeries.ofScalars ℂ c :=
        oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries _
      _ = FormalMultilinearSeries.ofScalars ℂ
          (fun n ↦ PowerSeries.coeff n P) := by rfl
  calc
    p = oneDimensionalFormalMultilinearSeries P :=
      (oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries p).symm
    _ = FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ PowerSeries.coeff n P) := hP
    _ = FormalMultilinearSeries.ofScalars ℂ (fun n ↦ p.coeff n) := by
      congr 1
      funext n
      simp only [P, oneDimensionalPowerSeries_coeff]

private theorem taylorCoefficient_eq_fms_coeff
    {F : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hF : HasFPowerSeriesAt F p 0) (n : ℕ) :
    Transfer.taylorCoefficient F n = p.coeff n := by
  have hp := oneDimensionalFMS_eq_ofScalars p
  rw [hp] at hF
  exact Transfer.taylorCoefficient_eq_seriesCoefficient hF n

private theorem taylorCoefficient_eq_banachTaylorCoefficient
    (F : ℂ → ℂ) (n : ℕ) :
    Transfer.taylorCoefficient F n =
      Transfer.banachTaylorCoefficient F n := by
  simp only [Transfer.taylorCoefficient,
    Transfer.banachTaylorCoefficient, smul_eq_mul, div_eq_mul_inv]
  ring

private theorem taylorCoefficient_add
    {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hG : AnalyticAt ℂ G 0) (n : ℕ) :
    Transfer.taylorCoefficient (fun w ↦ F w + G w) n =
      Transfer.taylorCoefficient F n +
        Transfer.taylorCoefficient G n := by
  simp only [Transfer.taylorCoefficient,
    iteratedDeriv_fun_add hF.contDiffAt hG.contDiffAt, add_div]

private theorem taylorCoefficient_const_of_pos
    (c : ℂ) {n : ℕ} (hn : 0 < n) :
    Transfer.taylorCoefficient (fun _ : ℂ ↦ c) n = 0 := by
  simp only [Transfer.taylorCoefficient, iteratedDeriv_const,
    if_neg hn.ne', zero_div]

/-- Uniform transfer data for the joint unicyclic continuation.  The
remainder is uniformly of square-root order on one common complex field
ball. -/
theorem exists_normalizedFieldUnicyclic_cartesianDelta_transfer_data
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ (C₀ : C(S, ℂ) → ℂ)
      (G R : ℂ × C(S, ℂ) → ℂ)
      (eta m s B : ℝ),
      0 < eta ∧ 0 < m ∧ m < 4 / 3 ∧ 0 < s ∧ 0 < B ∧
      AnalyticOnNhd ℂ C₀ (Metric.ball (0 : C(S, ℂ)) s) ∧
      AnalyticOnNhd ℂ G
        (Transfer.cartesianDelta eta m ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      AnalyticOnNhd ℂ R
        (Transfer.cartesianDelta eta m ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ q : ℂ × C(S, ℂ),
        G q = -(1 / 2 : ℂ) *
            Complex.log (Transfer.cartesianDeltaSqrt q.1) +
          C₀ q.2 + R q) ∧
      (∀ q ∈ Transfer.cartesianDelta eta m ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        ‖R q‖ ≤ B * ‖q.1 - 1‖ ^ (1 / 2 : ℝ)) ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        HasFPowerSeriesAt (fun w : ℂ ↦ G (w, g))
          (Local.normalizedFieldUnicyclicFMS M hM g) 0 := by
  obtain ⟨eta₀, r₀, s₀, H, C₀, G,
      heta₀, hr₀, hs₀, hH, hHaxis, hC₀, hG, hTaylor,
      hLocal⟩ :=
    Global.exists_normalizedFieldUnicyclic_cartesianDelta_continuation M hM

  have hHzero : AnalyticAt ℂ H
      ((0 : C(S, ℂ)), (0 : ℂ)) :=
    hH (0, 0) ⟨Metric.mem_ball_self hs₀, Metric.mem_ball_self hr₀⟩
  obtain ⟨Q, hQ, hQfactor⟩ :=
    PerronWright.AnalyticVerticalDivision.analytic_vertical_division_smul
      hHzero (Filter.Eventually.of_forall hHaxis)
  obtain ⟨rFactor, hrFactor, hFactorBall⟩ :=
    Metric.eventually_nhds_iff.mp hQfactor

  let Bnear : ℝ := ‖Q (0, 0)‖ + 1
  have hBnear : 0 < Bnear := by
    dsimp only [Bnear]
    positivity
  have hQboundedNhd : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      ‖Q q‖ ≤ Bnear := by
    have hclose : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        Q q ∈ Metric.ball (Q (0, 0)) 1 :=
      hQ.continuousAt (Metric.ball_mem_nhds (Q (0, 0)) zero_lt_one)
    filter_upwards [hclose] with q hq
    have htri : ‖Q q‖ ≤ ‖Q q - Q (0, 0)‖ + ‖Q (0, 0)‖ := by
      have := norm_add_le (Q q - Q (0, 0)) (Q (0, 0))
      simpa only [sub_add_cancel] using this
    have hdist : ‖Q q - Q (0, 0)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hq
    exact htri.trans (by dsimp only [Bnear]; linarith)
  obtain ⟨rBound, hrBound, hQboundBall⟩ :=
    Metric.eventually_nhds_iff.mp hQboundedNhd

  let L : ℂ → ℂ := fun w ↦
    -(1 / 2 : ℂ) * Complex.log (Transfer.cartesianDeltaSqrt w)
  let R : ℂ × C(S, ℂ) → ℂ := fun q ↦
    G q - L q.1 - C₀ q.2
  let D : Set (ℂ × C(S, ℂ)) :=
    Transfer.cartesianDelta eta₀ 0 ×ˢ
      Metric.ball (0 : C(S, ℂ)) s₀
  have hDopen : IsOpen D := by
    dsimp only [D]
    exact (Transfer.isOpen_cartesianDelta eta₀ 0).prod Metric.isOpen_ball
  have hR : AnalyticOnNhd ℂ R D := by
    intro q hq
    have hX : AnalyticAt ℂ
        (fun p : ℂ × C(S, ℂ) ↦
          Transfer.cartesianDeltaSqrt p.1) q :=
      ((Transfer.analyticOnNhd_cartesianDeltaSqrt
        (m := (0 : ℝ)) (by norm_num) q.1 hq.1).comp_of_eq
          analyticAt_fst rfl)
    have hXslit : Transfer.cartesianDeltaSqrt q.1 ∈ Complex.slitPlane :=
      PerronWright.ZeroFieldUnicyclicActivitySingularity.cartesianDeltaSqrt_mem_slitPlane
        (m := (0 : ℝ)) (by norm_num) hq.1
    have hL : AnalyticAt ℂ (fun p : ℂ × C(S, ℂ) ↦ L p.1) q := by
      dsimp only [L]
      exact analyticAt_const.mul ((analyticAt_clog hXslit).comp_of_eq hX rfl)
    have hC : AnalyticAt ℂ
        (fun p : ℂ × C(S, ℂ) ↦ C₀ p.2) q :=
      (hC₀ q.2 hq.2).comp_of_eq analyticAt_snd rfl
    exact ((hG q hq).sub hL).sub hC

  let rLocal : ℝ := min r₀ (min rFactor rBound)
  have hrLocal : 0 < rLocal := lt_min hr₀ (lt_min hrFactor hrBound)
  let sNear : ℝ := min s₀ (min rFactor rBound)
  have hsNear : 0 < sNear := lt_min hs₀ (lt_min hrFactor hrBound)
  let delta : ℝ := rLocal ^ 2 / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hdeltarLocal : delta < rLocal ^ 2 := by
    dsimp only [delta]
    nlinarith [sq_pos_of_pos hrLocal]

  let eta : ℝ := min (eta₀ / 2) (1 / 2)
  let m : ℝ := 1 / 2
  have heta : 0 < eta := by
    dsimp only [eta]
    exact lt_min (half_pos heta₀) (by norm_num)
  have heta_eta₀ : eta < eta₀ :=
    (min_le_left (eta₀ / 2) (1 / 2)).trans_lt
      (half_lt_self heta₀)
  have heta_one : eta ≤ 1 := by
    dsimp only [eta]
    linarith [min_le_right (eta₀ / 2) (1 / 2)]
  have hm : 0 < m := by norm_num [m]
  have hm43 : m < 4 / 3 := by norm_num [m]
  have hsmallSub : Transfer.cartesianDelta eta m ⊆
      Transfer.cartesianDelta eta₀ 0 :=
    cartesianDelta_subset_slit heta_eta₀.le hm.le
  have hsmallSubLocal : Transfer.cartesianDelta eta m ⊆
      Transfer.cartesianDelta 1 0 :=
    cartesianDelta_subset_slit heta_one hm.le

  let K : Set ℂ := cartesianDeltaAwayCompact eta m delta
  have hKcompact : IsCompact K := by
    simpa only [K] using
      isCompact_cartesianDeltaAwayCompact eta m delta
  have hKsub : K ⊆ Transfer.cartesianDelta eta₀ 0 := by
    simpa only [K] using
      (cartesianDeltaAwayCompact_subset_slit heta_eta₀ hm hdelta)
  have hKspine : K ×ˢ {(0 : C(S, ℂ))} ⊆ D := by
    rintro ⟨w, g⟩ ⟨hw, hg⟩
    have hg0 : g = 0 := by simpa only [Set.mem_singleton_iff] using hg
    subst g
    exact ⟨hKsub hw, Metric.mem_ball_self hs₀⟩
  obtain ⟨sAway, Bspine, hsAway, hBspine, hAwayNumerator⟩ :=
    exists_uniform_bound_on_compact_spine hKcompact hDopen
      hR.continuousOn hKspine
  let s : ℝ := min sNear sAway
  have hs : 0 < s := lt_min hsNear hsAway

  let droot : ℝ := delta ^ (1 / 2 : ℝ)
  have hdroot : 0 < droot := by
    dsimp only [droot]
    exact Real.rpow_pos_of_pos hdelta _
  let Baway : ℝ := Bspine / droot
  have hBaway : 0 < Baway := div_pos hBspine hdroot
  have hawayBound : ∀ q ∈ Transfer.cartesianDelta eta m ×ˢ
      Metric.ball (0 : C(S, ℂ)) s,
      delta ≤ dist q.1 1 →
      ‖R q‖ ≤ Baway * ‖q.1 - 1‖ ^ (1 / 2 : ℝ) := by
    intro q hq haway
    have hwK : q.1 ∈ K := by
      apply cartesianDelta_away_subset_compact
      exact ⟨hq.1, haway⟩
    have hgAway : q.2 ∈ Metric.ball (0 : C(S, ℂ)) sAway :=
      Metric.ball_subset_ball (min_le_right sNear sAway) hq.2
    have hnum : ‖R q‖ ≤ Bspine :=
      hAwayNumerator q.1 hwK q.2 hgAway
    have hrootle : droot ≤ ‖q.1 - 1‖ ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow hdelta.le
      · simpa only [Complex.dist_eq] using haway
      · norm_num
    calc
      ‖R q‖ ≤ Bspine := hnum
      _ = Baway * droot := by
        dsimp only [Baway]
        field_simp [hdroot.ne']
      _ ≤ Baway * ‖q.1 - 1‖ ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hrootle hBaway.le

  have hnearBound : ∀ q ∈ Transfer.cartesianDelta eta m ×ˢ
      Metric.ball (0 : C(S, ℂ)) s,
      dist q.1 1 < delta →
      ‖R q‖ ≤ Bnear * ‖q.1 - 1‖ ^ (1 / 2 : ℝ) := by
    intro q hq hnear
    let X : ℂ := Transfer.cartesianDeltaSqrt q.1
    have hXsqNorm : ‖X‖ ^ 2 = ‖1 - q.1‖ := by
      rw [← norm_pow, Transfer.cartesianDeltaSqrt_sq]
    have hdist : ‖1 - q.1‖ < delta := by
      simpa only [Complex.dist_eq, norm_sub_rev] using hnear
    have hXLocal : ‖X‖ < rLocal := by
      nlinarith [hXsqNorm, hdist, norm_nonneg X,
        sq_pos_of_pos hrLocal, hdeltarLocal]
    have hgNear : q.2 ∈ Metric.ball (0 : C(S, ℂ)) sNear :=
      Metric.ball_subset_ball (min_le_left sNear sAway) hq.2
    have hg₀ : q.2 ∈ Metric.ball (0 : C(S, ℂ)) s₀ :=
      Metric.ball_subset_ball (min_le_left s₀ _) hgNear
    have hwLocal : q.1 ∈
        FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r₀ := by
      refine ⟨hsmallSubLocal hq.1, ?_⟩
      change X ∈ Metric.ball (0 : ℂ) r₀
      have : ‖X‖ < r₀ := hXLocal.trans_le (min_le_left r₀ _)
      simpa only [Metric.mem_ball, dist_zero_right] using this
    have hpairFactor : (q.2, X) ∈
        Metric.ball ((0 : C(S, ℂ)), (0 : ℂ)) rFactor := by
      rw [← ball_prod_same]
      refine ⟨?_, ?_⟩
      · exact Metric.ball_subset_ball
          ((min_le_right s₀ _).trans (min_le_left rFactor rBound)) hgNear
      · have : ‖X‖ < rFactor :=
          hXLocal.trans_le
            ((min_le_right r₀ _).trans (min_le_left rFactor rBound))
        simpa only [Metric.mem_ball, dist_zero_right] using this
    have hpairBound : (q.2, X) ∈
        Metric.ball ((0 : C(S, ℂ)), (0 : ℂ)) rBound := by
      rw [← ball_prod_same]
      refine ⟨?_, ?_⟩
      · exact Metric.ball_subset_ball
          ((min_le_right s₀ _).trans (min_le_right rFactor rBound)) hgNear
      · have : ‖X‖ < rBound :=
          hXLocal.trans_le
            ((min_le_right r₀ _).trans (min_le_right rFactor rBound))
        simpa only [Metric.mem_ball, dist_zero_right] using this
    have hRE : R q = H (q.2, X) := by
      have hloc := hLocal q ⟨hwLocal, hg₀⟩
      dsimp only [R, L]
      rw [hloc]
      ring
    have hfactor : H (q.2, X) = X * Q (q.2, X) := by
      have := hFactorBall hpairFactor
      simpa only [smul_eq_mul] using this
    have hQbd : ‖Q (q.2, X)‖ ≤ Bnear := hQboundBall hpairBound
    calc
      ‖R q‖ = ‖X‖ * ‖Q (q.2, X)‖ := by
        rw [hRE, hfactor, norm_mul]
      _ ≤ ‖X‖ * Bnear :=
        mul_le_mul_of_nonneg_left hQbd (norm_nonneg X)
      _ = Bnear * ‖q.1 - 1‖ ^ (1 / 2 : ℝ) := by
        rw [PerronWright.ZeroFieldUnicyclicActivitySingularity.norm_cartesianDeltaSqrt_eq_rpow,
          norm_sub_rev]
        ring

  let B : ℝ := max 1 (max Bnear Baway)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  have hBnearB : Bnear ≤ B :=
    (le_max_left Bnear Baway).trans (le_max_right 1 (max Bnear Baway))
  have hBawayB : Baway ≤ B :=
    (le_max_right Bnear Baway).trans (le_max_right 1 (max Bnear Baway))
  have hglobalBound : ∀ q ∈ Transfer.cartesianDelta eta m ×ˢ
      Metric.ball (0 : C(S, ℂ)) s,
      ‖R q‖ ≤ B * ‖q.1 - 1‖ ^ (1 / 2 : ℝ) := by
    intro q hq
    by_cases hnear : dist q.1 1 < delta
    · exact (hnearBound q hq hnear).trans
        (mul_le_mul_of_nonneg_right hBnearB
          (Real.rpow_nonneg (norm_nonneg _) _))
    · exact (hawayBound q hq (le_of_not_gt hnear)).trans
        (mul_le_mul_of_nonneg_right hBawayB
          (Real.rpow_nonneg (norm_nonneg _) _))

  have hfieldSub : Metric.ball (0 : C(S, ℂ)) s ⊆
      Metric.ball (0 : C(S, ℂ)) s₀ := by
    exact Metric.ball_subset_ball
      ((min_le_left sNear sAway).trans (min_le_left s₀ _))
  have hdomain : Transfer.cartesianDelta eta m ×ˢ
      Metric.ball (0 : C(S, ℂ)) s ⊆ D := by
    intro q hq
    exact ⟨hsmallSub hq.1, hfieldSub hq.2⟩
  refine ⟨C₀, G, R, eta, m, s, B,
    heta, hm, hm43, hs, hB, ?_, ?_, ?_, ?_, hglobalBound, ?_⟩
  · exact hC₀.mono hfieldSub
  · exact hG.mono hdomain
  · exact hR.mono hdomain
  · intro q
    dsimp only [R, L]
    ring
  · intro g hg
    exact hTaylor g (hfieldSub hg)

/-- Family-uniform coefficient form of the joint unicyclic transfer.  The
constants and threshold precede the field parameter, and the coefficient on
the left is the literal normalized complex-field unicyclic FMS coefficient. -/
theorem exists_normalizedFieldUnicyclic_coefficient_uniform_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ (s K : ℝ) (N : ℕ),
      0 < s ∧ 0 < K ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        ∀ n : ℕ, N ≤ n →
          ‖(Local.normalizedFieldUnicyclicFMS M hM g).coeff n -
              (1 / 4 : ℂ) * (n : ℂ)⁻¹‖ ≤
            K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C₀, G, R, eta, m, s, B,
      heta, hm, hm43, hs, hB, _hC₀, hG, hR,
      hFormula, hRbound, hTaylor⟩ :=
    exists_normalizedFieldUnicyclic_cartesianDelta_transfer_data M hM

  let 𝒢 := ↥(Metric.ball (0 : C(S, ℂ)) s)
  let Rslice : 𝒢 → ℂ → ℂ := fun g w ↦ R (w, (g : C(S, ℂ)))
  let Q : 𝒢 → ℂ → ℂ := fun g w ↦ ((B : ℂ)⁻¹) * Rslice g w
  have hQdiff : ∀ g : 𝒢,
      DifferentiableOn ℂ (Q g) (Transfer.cartesianDelta eta m) := by
    intro g w hw
    have hRs : AnalyticAt ℂ (Rslice g) w :=
      (hR (w, (g : C(S, ℂ))) ⟨hw, g.property⟩).comp_of_eq
        (analyticAt_id.prod analyticAt_const) rfl
    exact (analyticAt_const.mul hRs).differentiableAt.differentiableWithinAt
  have hQpower : ∀ g : 𝒢, ∀ w ∈ Transfer.cartesianDelta eta m,
      ‖Q g w‖ ≤ ‖w - 1‖ ^ (1 / 2 : ℝ) := by
    intro g w hw
    have hBnorm : ‖((B : ℂ)⁻¹)‖ = B⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    calc
      ‖Q g w‖ = B⁻¹ * ‖R (w, (g : C(S, ℂ)))‖ := by
        dsimp only [Q, Rslice]
        rw [norm_mul, hBnorm]
      _ ≤ B⁻¹ * (B * ‖w - 1‖ ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (hRbound (w, (g : C(S, ℂ))) ⟨hw, g.property⟩)
          (inv_nonneg.mpr hB.le)
      _ = ‖w - 1‖ ^ (1 / 2 : ℝ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul]

  let Mcontour : ℝ := min (eta / 2) 1
  have hMcontour : 0 < Mcontour := by
    dsimp only [Mcontour]
    exact lt_min (half_pos heta) zero_lt_one
  have hMcontourOne : Mcontour ≤ 1 := min_le_right _ _
  have hMcontourEta : Mcontour < eta :=
    (min_le_left (eta / 2) 1).trans_lt (half_lt_self heta)
  obtain ⟨KQ, hKQ, hQcoeff⟩ :=
    Transfer.exists_uniform_banachCartesianTaylorCoefficient_bound
      (F := Q) (M := Mcontour) (eta := eta) (m := m)
      (a := (1 / 2 : ℝ)) hMcontour hMcontourOne hMcontourEta
      hm.le hm43 (by norm_num) hQdiff hQpower
  obtain ⟨NQ, hNQ⟩ := Filter.eventually_atTop.1 hQcoeff
  let K : ℝ := B * KQ
  let N : ℕ := max NQ 1
  have hK : 0 < K := mul_pos hB hKQ
  refine ⟨s, K, N, hs, hK, ?_⟩
  intro g hg n hn
  have hnQ : NQ ≤ n := (le_max_left NQ 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right NQ 1).trans hn
  have hn0 : 0 < n := Nat.zero_lt_one.trans_le hn1
  let gi : 𝒢 := ⟨g, hg⟩
  have hQn : ‖Transfer.banachTaylorCoefficient (Q gi) n‖ ≤
      KQ * (n : ℝ) ^ (-((1 / 2 : ℝ) + 1)) :=
    hNQ n hnQ gi
  have hQn' : ‖Transfer.banachTaylorCoefficient (Q gi) n‖ ≤
      KQ * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    simpa only [show -((1 / 2 : ℝ) + 1) = -(3 / 2 : ℝ) by
      norm_num] using hQn

  let Rg : ℂ → ℂ := fun w ↦ R (w, g)
  have hCoeffScale :
      Transfer.banachTaylorCoefficient Rg n =
        (B : ℂ) * Transfer.banachTaylorCoefficient (Q gi) n := by
    simp only [Transfer.banachTaylorCoefficient, Q, Rslice, Rg, gi,
      iteratedDeriv_const_mul_field, smul_eq_mul]
    field_simp [hB.ne']
  have hRcoeffBound :
      ‖Transfer.taylorCoefficient Rg n‖ ≤
        K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [taylorCoefficient_eq_banachTaylorCoefficient, hCoeffScale,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    calc
      B * ‖Transfer.banachTaylorCoefficient (Q gi) n‖ ≤
          B * (KQ * (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hQn' hB.le
      _ = K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
        dsimp only [K]
        ring

  have hzeroDelta : (0 : ℂ) ∈ Transfer.cartesianDelta eta m :=
    Transfer.unit_ball_subset_cartesianDelta heta
      (by simpa only [Metric.mem_ball, dist_zero_right, norm_zero] using
        (zero_lt_one : (0 : ℝ) < 1))
  have hG0 : AnalyticAt ℂ (fun w : ℂ ↦ G (w, g)) 0 :=
    (hG (0, g) ⟨hzeroDelta, hg⟩).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  let L : ℂ → ℂ := fun w ↦
    -(1 / 2 : ℂ) * Complex.log (Transfer.cartesianDeltaSqrt w)
  have hLseries : HasFPowerSeriesAt L Transfer.unicyclicLogPowerSeries 0 := by
    simpa only [L, Transfer.cartesianDeltaSqrt] using
      Transfer.neg_half_log_sqrt_one_sub_hasFPowerSeriesAt
  have hL0 : AnalyticAt ℂ L 0 := hLseries.analyticAt
  have hMainCoeff : Transfer.taylorCoefficient L n =
      (1 / 4 : ℂ) * (n : ℂ)⁻¹ := by
    simpa only [L, Transfer.cartesianDeltaSqrt,
      Transfer.logarithmicCoefficient] using
      Transfer.taylorCoefficient_neg_half_log_sqrt_one_sub n
  have hConstCoeff :
      Transfer.taylorCoefficient (fun _ : ℂ ↦ C₀ g) n = 0 :=
    taylorCoefficient_const_of_pos (C₀ g) hn0
  have hSingularCoeff :
      Transfer.taylorCoefficient (fun w : ℂ ↦ L w + C₀ g) n =
        (1 / 4 : ℂ) * (n : ℂ)⁻¹ := by
    rw [taylorCoefficient_add hL0 analyticAt_const n,
      hMainCoeff, hConstCoeff, add_zero]
  have hCoeffGenuine :
      Transfer.taylorCoefficient (fun w : ℂ ↦ G (w, g)) n =
        (Local.normalizedFieldUnicyclicFMS M hM g).coeff n :=
    taylorCoefficient_eq_fms_coeff (hTaylor g hg) n
  have hRcoeffFormula :
      Transfer.taylorCoefficient Rg n =
        (Local.normalizedFieldUnicyclicFMS M hM g).coeff n -
          (1 / 4 : ℂ) * (n : ℂ)⁻¹ := by
    have hsub := Transfer.taylorCoefficient_sub
      (F := fun w : ℂ ↦ G (w, g))
      (G := fun w : ℂ ↦ L w + C₀ g)
      hG0 (hL0.add analyticAt_const) n
    have hfun : (fun w : ℂ ↦
        G (w, g) - (L w + C₀ g)) = Rg := by
      funext w
      rw [hFormula (w, g)]
      dsimp only [L, Rg]
      ring
    rw [hfun, hSingularCoeff, hCoeffGenuine] at hsub
    exact hsub
  rw [← hRcoeffFormula]
  exact hRcoeffBound

/-- The same uniform estimate written directly for the literal connected
graph weight.  This is the exact coefficient bridge needed by the
Perron--Wright statement at surplus one. -/
theorem exists_complexFieldUnicyclic_connectedWeight_uniform_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ (s K : ℝ) (N : ℕ),
      0 < s ∧ 0 < K ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        ∀ n : ℕ, N ≤ n →
          ‖(FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
                (M.bjrModel.complexFieldConnectedWeight g n 1 /
                  (n.factorial : ℂ)) -
              (1 / 4 : ℂ) * (n : ℂ)⁻¹‖ ≤
            K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨s, K, N, hs, hK, hbound⟩ :=
    exists_normalizedFieldUnicyclic_coefficient_uniform_bound M hM
  refine ⟨s, K, N, hs, hK, ?_⟩
  intro g hg n hn
  rw [← Local.normalizedFieldUnicyclicFMS_coeff M hM g n]
  exact hbound g hg n hn

end PerronWright.FiniteIrreducibleFieldUnicyclicCoefficientAsymptotic
