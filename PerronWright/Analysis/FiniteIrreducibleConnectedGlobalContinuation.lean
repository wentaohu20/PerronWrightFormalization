import PerronWright.Analysis.FiniteIrreducibleCubicGlobalContinuation
import PerronWright.Analysis.FiniteIrreducibleNoncubicGlobalContinuation

/-!
# Common global continuation for the genuine finite connected-graph EGF

Both exact graph summands are restricted to one Cartesian Delta-domain with
positive opening and one complex field ball, then added. No continuation is
postulated: the Taylor coefficients are the original connected-graph weights
divided by factorials and rescaled by the actual critical radius.
-/

open Filter Topology Set
open scoped Classical Topology

noncomputable section

namespace PerronWright.FiniteIrreducibleConnectedGlobalContinuation

open GraphCore FiniteIrreducibleKernelAmplitude

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- The sum of the two exact normalized graph Taylor series. -/
def normalizedFieldConnectedFMS
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (g : C(S, ℂ)) (ell : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FiniteIrreducibleCubicGlobalContinuation.normalizedFieldCubicPartFMS
    M hM g ell +
  FiniteIrreducibleNoncubicGlobalContinuation.normalizedFieldNoncubicPartFMS
    M hM g ell

/-- Exact original labelled-graph coefficient, including factorial and
actual-radius rescaling. -/
@[simp] theorem normalizedFieldConnectedFMS_coeff
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (g : C(S, ℂ)) (ell n : ℕ) :
    (normalizedFieldConnectedFMS M hM g ell).coeff n =
      (FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
        (M.bjrModel.complexFieldConnectedWeight g n (ell + 1) /
          (n.factorial : ℂ)) := by
  change
    (FiniteIrreducibleCubicGlobalContinuation.normalizedFieldCubicPartFMS
      M hM g ell).coeff n +
    (FiniteIrreducibleNoncubicGlobalContinuation.normalizedFieldNoncubicPartFMS
      M hM g ell).coeff n = _
  rw [FiniteIrreducibleCubicGlobalContinuation.normalizedFieldCubicPartFMS_coeff,
    FiniteIrreducibleNoncubicGlobalContinuation.normalizedFieldNoncubicPartFMS_coeff,
    complexFieldCubicPartEGF_coeff, complexFieldNoncubicPartEGF_coeff,
    complexFieldConnectedWeight_div_factorial_eq_cubic_add_noncubic]
  ring

private theorem cartesianDelta_restrict {eta eta' : ℝ} (h : eta ≤ eta') :
    Transfer.cartesianDelta eta 1 ⊆ Transfer.cartesianDelta eta' 0 := by
  intro w hw
  refine ⟨hw.1.trans_le (by linarith), ?_⟩
  intro hwedge
  apply hw.2
  exact ⟨hwedge.1, hwedge.2.trans (by linarith [hwedge.1])⟩

/-- Actual jointly analytic total connected-graph continuation on one
positive-opening Cartesian Delta-domain times one field ball, with the
genuine all-size Taylor series and the exact joint fold numerator. -/
theorem exists_complexFieldConnected_cartesianDelta_continuation
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ (eta r s : ℝ) (G : ℂ × C(S, ℂ) → ℂ),
      0 < eta ∧ 0 < r ∧ 0 < s ∧
      AnalyticOnNhd ℂ G
        (Transfer.cartesianDelta eta 1 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        HasFPowerSeriesAt (fun w : ℂ ↦ G (w, g))
          (normalizedFieldConnectedFMS M hM g ell) 0) ∧
      ∀ q ∈ FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 1 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        G q =
          (Transfer.cartesianDeltaSqrt q.1 ^ (3 * ell))⁻¹ *
            (positiveSurplusCubicAdmissibleIntegratedAmplitude M hM ell
                (q.2, Transfer.cartesianDeltaSqrt q.1) +
              positiveSurplusNoncubicIntegratedAmplitude M hM ell
                (q.2, Transfer.cartesianDeltaSqrt q.1)) := by
  obtain ⟨ec, rc, sc, Gc, hec, hrc, hsc, -, -, hGc, hTc, hFc⟩ :=
    FiniteIrreducibleCubicGlobalContinuation.exists_complexFieldCubicPart_cartesianDelta_continuation
      M hM hell
  obtain ⟨en, rn, sn, Gn, hen, hrn, hsn, -, -, hGn, hTn, hFn⟩ :=
    FiniteIrreducibleNoncubicGlobalContinuation.exists_complexFieldNoncubicPart_cartesianDelta_continuation
      M hM hell
  let eta := min ec en
  let r := min rc rn
  let s := min sc sn
  let G : ℂ × C(S, ℂ) → ℂ := fun q ↦ Gc q + Gn q
  have hgC : ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
      g ∈ Metric.ball 0 sc := by
    intro g hg
    exact Metric.mem_ball.mpr
      ((Metric.mem_ball.mp hg).trans_le (min_le_left sc sn))
  have hgN : ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
      g ∈ Metric.ball 0 sn := by
    intro g hg
    exact Metric.mem_ball.mpr
      ((Metric.mem_ball.mp hg).trans_le (min_le_right sc sn))
  refine ⟨eta, r, s, G, lt_min hec hen, lt_min hrc hrn,
    lt_min hsc hsn, ?_, ?_, ?_⟩
  · intro q hq
    exact (hGc q ⟨cartesianDelta_restrict (min_le_left ec en) hq.1,
      hgC q.2 hq.2⟩).add
      (hGn q ⟨cartesianDelta_restrict (min_le_right ec en) hq.1,
        hgN q.2 hq.2⟩)
  · intro g hg
    exact (hTc g (hgC g hg)).add (hTn g (hgN g hg))
  · intro q hq
    have hqC : q ∈
        FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rc ×ˢ
          Metric.ball (0 : C(S, ℂ)) sc :=
      ⟨⟨cartesianDelta_restrict (le_refl 1) hq.1.1,
        Metric.mem_ball.mpr ((Metric.mem_ball.mp hq.1.2).trans_le
          (min_le_left rc rn))⟩, hgC q.2 hq.2⟩
    have hqN : q ∈
        FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rn ×ˢ
          Metric.ball (0 : C(S, ℂ)) sn :=
      ⟨⟨cartesianDelta_restrict (le_refl 1) hq.1.1,
        Metric.mem_ball.mpr ((Metric.mem_ball.mp hq.1.2).trans_le
          (min_le_right rc rn))⟩, hgN q.2 hq.2⟩
    dsimp only [G]
    rw [hFc q hqC, hFn q hqN]
    ring

end PerronWright.FiniteIrreducibleConnectedGlobalContinuation
