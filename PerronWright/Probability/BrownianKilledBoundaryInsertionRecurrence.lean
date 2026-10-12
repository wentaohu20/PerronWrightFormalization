import PerronWright.Probability.BrownianKilledAreaResolventSymmetry

/-! # Actual boundary insertion and its Green recurrence

The positive-order expressions are exactly the actual Kac resolvent
boundary insertions. Tonelli and the last-edge insertion identity prove
their Green recurrence without an additional boundary-exchange premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledBoundaryInsertionRecurrence

open BrownianKilledAreaMomentResolvent BrownianKilledAreaResolventSymmetry

def boundarySlopeNN : ℕ → ℝ → ℝ → ℝ≥0∞
  | 0, p, y => ENNReal.ofReal (2*Real.exp (-y*Real.sqrt (2*p)))
  | n+1, p, y => ((n+1 : ℕ) : ℝ≥0∞)*∫⁻ z : ℝ,
      ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p)))*ENNReal.ofReal z*resolvent n p z y

theorem measurable_boundarySlopeNN (n : ℕ) (p : ℝ) : Measurable (boundarySlopeNN n p) := by
  cases n with
  | zero =>
    change Measurable (fun y : ℝ ↦ ENNReal.ofReal (2*Real.exp (-y*Real.sqrt (2*p))))
    exact (measurable_const.mul ((measurable_id.neg.mul_const (Real.sqrt (2*p))).exp)).ennreal_ofReal
  | succ n =>
    have h0 : Measurable (boundarySlopeNN 0 p) :=
      by
        change Measurable (fun y : ℝ ↦ ENNReal.ofReal (2*Real.exp (-y*Real.sqrt (2*p))))
        exact (measurable_const.mul ((measurable_id.neg.mul_const (Real.sqrt (2*p))).exp)).ennreal_ofReal
    have hm : Measurable (fun q : ℝ × ℝ ↦
        boundarySlopeNN 0 p q.2*ENNReal.ofReal q.2*resolvent n p q.2 q.1) :=
      ((h0.comp measurable_snd).mul measurable_snd.ennreal_ofReal).mul
        ((measurable_resolvent n p).comp (measurable_snd.prodMk measurable_fst))
    change Measurable (fun y : ℝ ↦ ((n+1 : ℕ) : ℝ≥0∞)*∫⁻ z : ℝ,
      boundarySlopeNN 0 p z*ENNReal.ofReal z*resolvent n p z y)
    exact measurable_const.mul (hm.lintegral_prod_right' (ν := volume))

private theorem source_exchange (h : ℝ → ℝ≥0∞) (K A : ℝ → ℝ → ℝ≥0∞)
    (hh : Measurable h) (hK : Measurable (fun q : ℝ × ℝ ↦ K q.1 q.2))
    (hA : Measurable (fun q : ℝ × ℝ ↦ A q.1 q.2)) (y : ℝ) :
    (∫⁻ z : ℝ, h z*ENNReal.ofReal z*(∫⁻ w : ℝ, A z w*ENNReal.ofReal w*K w y)) =
      ∫⁻ w : ℝ, K w y*ENNReal.ofReal w*(∫⁻ z : ℝ, h z*ENNReal.ofReal z*A z w) := by
  have hM : Measurable (fun q : ℝ × ℝ ↦
      h q.1*ENNReal.ofReal q.1*A q.1 q.2*ENNReal.ofReal q.2*K q.2 y) :=
    (((((hh.comp measurable_fst).mul measurable_fst.ennreal_ofReal).mul hA).mul
      measurable_snd.ennreal_ofReal).mul (hK.comp (measurable_snd.prodMk measurable_const)))
  have hL (z : ℝ) : Measurable (fun w : ℝ ↦ A z w*ENNReal.ofReal w*K w y) :=
    (((hA.comp (measurable_const.prodMk measurable_id)).mul measurable_id.ennreal_ofReal).mul
      (hK.comp (measurable_id.prodMk measurable_const)))
  have hR (w : ℝ) : Measurable (fun z : ℝ ↦ h z*ENNReal.ofReal z*A z w) :=
    (hh.mul measurable_id.ennreal_ofReal).mul (hA.comp (measurable_id.prodMk measurable_const))
  calc
    _ = ∫⁻ z : ℝ, ∫⁻ w : ℝ, h z*ENNReal.ofReal z*A z w*ENNReal.ofReal w*K w y := by
      apply lintegral_congr
      intro z
      calc
        _ = ∫⁻ w : ℝ, (h z*ENNReal.ofReal z)*(A z w*ENNReal.ofReal w*K w y) :=
          (lintegral_const_mul (h z*ENNReal.ofReal z) (hL z)).symm
        _ = _ := lintegral_congr (fun w ↦ by ac_rfl)
    _ = ∫⁻ w : ℝ, ∫⁻ z : ℝ, h z*ENNReal.ofReal z*A z w*ENNReal.ofReal w*K w y :=
      lintegral_lintegral_swap hM.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro w
      calc
        _ = ∫⁻ z : ℝ, (h z*ENNReal.ofReal z*A z w)*(ENNReal.ofReal w*K w y) :=
          lintegral_congr (fun z ↦ by ac_rfl)
        _ = (∫⁻ z : ℝ, h z*ENNReal.ofReal z*A z w)*(ENNReal.ofReal w*K w y) :=
          lintegral_mul_const (ENNReal.ofReal w*K w y) (hR w)
        _ = _ := by ac_rfl

theorem boundarySlopeNN_recurrence (n : ℕ) (p : ℝ) (hp : 0 < p) (y : ℝ) :
    boundarySlopeNN (n+1) p y = ((n+1 : ℕ) : ℝ≥0∞)*∫⁻ z : ℝ,
      resolvent 0 p y z*ENNReal.ofReal z*boundarySlopeNN n p z := by
  cases n with
  | zero =>
    simp only [boundarySlopeNN]
    congr 1
    apply lintegral_congr
    intro z
    rw [resolvent_zero_symm p hp z y]
    ac_rfl
  | succ n =>
    have hpull : (∫⁻ z : ℝ, boundarySlopeNN 0 p z*ENNReal.ofReal z*
        (((n+1 : ℕ) : ℝ≥0∞)*rightInsert p (resolvent n p) z y)) =
        ((n+1 : ℕ) : ℝ≥0∞)*(∫⁻ z : ℝ, boundarySlopeNN 0 p z*ENNReal.ofReal z*
          rightInsert p (resolvent n p) z y) := by
      rw [← lintegral_const_mul' _ _ (by simp : ((n+1 : ℕ) : ℝ≥0∞) ≠ ⊤)]
      exact lintegral_congr (fun z ↦ by ac_rfl)
    have hex := source_exchange (boundarySlopeNN 0 p) (resolvent 0 p) (resolvent n p)
      (measurable_boundarySlopeNN 0 p) (measurable_resolvent 0 p) (measurable_resolvent n p) y
    calc
      _ = ((n+2 : ℕ) : ℝ≥0∞)*∫⁻ z : ℝ, boundarySlopeNN 0 p z*ENNReal.ofReal z*
          (((n+1 : ℕ) : ℝ≥0∞)*rightInsert p (resolvent n p) z y) := by
        rw [boundarySlopeNN]
        congr 1
        exact lintegral_congr (fun z ↦ by rw [resolvent_succ_rightInsert,boundarySlopeNN])
      _ = ((n+2 : ℕ) : ℝ≥0∞)*(((n+1 : ℕ) : ℝ≥0∞)*
          ∫⁻ z : ℝ, boundarySlopeNN 0 p z*ENNReal.ofReal z*rightInsert p (resolvent n p) z y) := by
        rw [hpull]
      _ = ((n+2 : ℕ) : ℝ≥0∞)*(((n+1 : ℕ) : ℝ≥0∞)*∫⁻ w : ℝ,
          resolvent 0 p w y*ENNReal.ofReal w*
            (∫⁻ z : ℝ, boundarySlopeNN 0 p z*ENNReal.ofReal z*resolvent n p z w)) := by
        change ((n+2 : ℕ) : ℝ≥0∞)*(((n+1 : ℕ) : ℝ≥0∞)*∫⁻ z : ℝ,
          boundarySlopeNN 0 p z*ENNReal.ofReal z*(∫⁻ w : ℝ,
            resolvent n p z w*ENNReal.ofReal w*resolvent 0 p w y)) = _
        rw [hex]
      _ = _ := by
        rw [← lintegral_const_mul' _ _ (by simp : ((n+1 : ℕ) : ℝ≥0∞) ≠ ⊤)]
        congr 1
        apply lintegral_congr
        intro w
        rw [resolvent_zero_symm p hp w y]
        simp only [boundarySlopeNN]
        ac_rfl

theorem boundarySlopeNN_succ_of_nonpos (n : ℕ) (p y : ℝ) (hy : y ≤ 0) :
    boundarySlopeNN (n+1) p y = 0 := by
  simp only [boundarySlopeNN,resolvent_zero_of_nonpos_target n p _ y hy,mul_zero,lintegral_zero]

end PerronWright.BrownianKilledBoundaryInsertionRecurrence
