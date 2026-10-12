import PerronWright.Probability.BrownianKilledGreenKernel

/-! # Genuine all-order killed-area resolvent symmetry

Tonelli moves insertion from the first edge to the last edge of the
already proved Kac chain. The actual symmetric zeroth Green kernel then
gives symmetry at every order. No path-reversal or symmetry premise is
introduced.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaResolventSymmetry

open BrownianKilledAreaMomentResolvent BrownianKilledGreenKernel

def leftInsert (p : ℝ) (A : ℝ → ℝ → ℝ≥0∞) (x y : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ℝ, resolvent 0 p x z*ENNReal.ofReal z*A z y

def rightInsert (p : ℝ) (A : ℝ → ℝ → ℝ≥0∞) (x y : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ℝ, A x z*ENNReal.ofReal z*resolvent 0 p z y

theorem leftInsert_const_mul (p : ℝ) (A : ℝ → ℝ → ℝ≥0∞) (c : ℝ≥0∞)
    (hc : c ≠ ⊤) (x y : ℝ) :
    leftInsert p (fun a b ↦ c*A a b) x y = c*leftInsert p A x y := by
  unfold leftInsert
  rw [← lintegral_const_mul' _ _ hc]
  apply lintegral_congr
  intro z
  dsimp only
  ac_rfl

theorem rightInsert_const_mul (p : ℝ) (A : ℝ → ℝ → ℝ≥0∞) (c : ℝ≥0∞)
    (hc : c ≠ ⊤) (x y : ℝ) :
    rightInsert p (fun a b ↦ c*A a b) x y = c*rightInsert p A x y := by
  unfold rightInsert
  rw [← lintegral_const_mul' _ _ hc]
  apply lintegral_congr
  intro z
  dsimp only
  ac_rfl

private theorem weightedKernel_exchange (K A : ℝ → ℝ → ℝ≥0∞)
    (hK : Measurable (fun q : ℝ × ℝ ↦ K q.1 q.2))
    (hA : Measurable (fun q : ℝ × ℝ ↦ A q.1 q.2)) (x y : ℝ) :
    (∫⁻ z : ℝ, K x z*ENNReal.ofReal z*(∫⁻ w : ℝ, A z w*ENNReal.ofReal w*K w y)) =
      ∫⁻ w : ℝ, (∫⁻ z : ℝ, K x z*ENNReal.ofReal z*A z w)*ENNReal.ofReal w*K w y := by
  have hM : Measurable (fun q : ℝ × ℝ ↦
      K x q.1*ENNReal.ofReal q.1*A q.1 q.2*ENNReal.ofReal q.2*K q.2 y) :=
    (((((hK.comp (measurable_const.prodMk measurable_fst)).mul measurable_fst.ennreal_ofReal).mul hA).mul
      measurable_snd.ennreal_ofReal).mul (hK.comp (measurable_snd.prodMk measurable_const)))
  have hL (z : ℝ) : Measurable (fun w : ℝ ↦ A z w*ENNReal.ofReal w*K w y) :=
    (((hA.comp (measurable_const.prodMk measurable_id)).mul measurable_id.ennreal_ofReal).mul
      (hK.comp (measurable_id.prodMk measurable_const)))
  have hR (w : ℝ) : Measurable (fun z : ℝ ↦ K x z*ENNReal.ofReal z*A z w) :=
    (((hK.comp (measurable_const.prodMk measurable_id)).mul measurable_id.ennreal_ofReal).mul
      (hA.comp (measurable_id.prodMk measurable_const)))
  calc
    _ = ∫⁻ z : ℝ, ∫⁻ w : ℝ,
        K x z*ENNReal.ofReal z*A z w*ENNReal.ofReal w*K w y := by
      apply lintegral_congr
      intro z
      calc
        _ = ∫⁻ w : ℝ, (K x z*ENNReal.ofReal z)*
            (A z w*ENNReal.ofReal w*K w y) :=
          (lintegral_const_mul (K x z*ENNReal.ofReal z) (hL z)).symm
        _ = _ := lintegral_congr (fun w ↦ by ac_rfl)
    _ = ∫⁻ w : ℝ, ∫⁻ z : ℝ,
        K x z*ENNReal.ofReal z*A z w*ENNReal.ofReal w*K w y :=
      lintegral_lintegral_swap hM.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro w
      calc
        _ = ∫⁻ z : ℝ, (K x z*ENNReal.ofReal z*A z w)*
            (ENNReal.ofReal w*K w y) :=
          lintegral_congr (fun z ↦ by ac_rfl)
        _ = (∫⁻ z : ℝ, K x z*ENNReal.ofReal z*A z w)*
            (ENNReal.ofReal w*K w y) :=
          lintegral_mul_const (ENNReal.ofReal w*K w y) (hR w)
        _ = _ := (mul_assoc _ _ _).symm

theorem leftInsert_rightInsert (p : ℝ) {A : ℝ → ℝ → ℝ≥0∞}
    (hA : Measurable (fun q : ℝ × ℝ ↦ A q.1 q.2)) (x y : ℝ) :
    leftInsert p (rightInsert p A) x y = rightInsert p (leftInsert p A) x y :=
  weightedKernel_exchange (resolvent 0 p) A (measurable_resolvent 0 p) hA x y

theorem resolvent_succ_rightInsert (n : ℕ) (p x y : ℝ) :
    resolvent (n+1) p x y = ((n+1 : ℕ) : ℝ≥0∞)*rightInsert p (resolvent n p) x y := by
  induction n generalizing x y with
  | zero =>
    simpa only [rightInsert] using resolvent_succ 0 p x y
  | succ n ih =>
    have hleft : resolvent (n+1) p =
        (fun a b ↦ ((n+1 : ℕ) : ℝ≥0∞)*leftInsert p (resolvent n p) a b) := by
      funext a b
      exact resolvent_succ n p a b
    have hright : resolvent (n+1) p =
        (fun a b ↦ ((n+1 : ℕ) : ℝ≥0∞)*rightInsert p (resolvent n p) a b) := by
      funext a b
      exact ih a b
    calc
      _ = ((n+2 : ℕ) : ℝ≥0∞)*leftInsert p (resolvent (n+1) p) x y := resolvent_succ (n+1) p x y
      _ = ((n+2 : ℕ) : ℝ≥0∞)*(((n+1 : ℕ) : ℝ≥0∞)*leftInsert p (rightInsert p (resolvent n p)) x y) := by
        rw [hright,leftInsert_const_mul _ _ _ (by simp)]
      _ = ((n+2 : ℕ) : ℝ≥0∞)*(((n+1 : ℕ) : ℝ≥0∞)*rightInsert p (leftInsert p (resolvent n p)) x y) := by
        rw [leftInsert_rightInsert p (measurable_resolvent n p) x y]
      _ = ((n+2 : ℕ) : ℝ≥0∞)*rightInsert p (resolvent (n+1) p) x y := by
        rw [hleft,rightInsert_const_mul _ _ _ (by simp)]

theorem resolvent_succ_right (n : ℕ) (p x y : ℝ) :
    resolvent (n+1) p x y = ((n+1 : ℕ) : ℝ≥0∞)*∫⁻ z : ℝ,
      resolvent n p x z*ENNReal.ofReal z*resolvent 0 p z y :=
  resolvent_succ_rightInsert n p x y

theorem resolvent_zero_symm (p : ℝ) (hp : 0 < p) (x y : ℝ) :
    resolvent 0 p x y = resolvent 0 p y x := by
  rw [resolvent_zero_eq p hp,resolvent_zero_eq p hp]
  unfold green
  have he : (0 < x ∧ 0 < y) ↔ (0 < y ∧ 0 < x) := and_comm
  simp only [he]
  split
  · unfold greenReal
    rw [abs_sub_comm,add_comm x y]
  · rfl

theorem resolvent_symm (n : ℕ) (p : ℝ) (hp : 0 < p) (x y : ℝ) :
    resolvent n p x y = resolvent n p y x := by
  induction n generalizing x y with
  | zero => exact resolvent_zero_symm p hp x y
  | succ n ih =>
    rw [resolvent_succ,resolvent_succ_right]
    congr 1
    apply lintegral_congr
    intro z
    rw [resolvent_zero_symm p hp x z,ih z y]
    ac_rfl

theorem initial_lintegral_eq_target_lintegral (n : ℕ) (p : ℝ) (hp : 0 < p) (y : ℝ) :
    (∫⁻ z : ℝ, resolvent n p z y) = ∫⁻ z : ℝ, resolvent n p y z := by
  exact lintegral_congr (fun z ↦ resolvent_symm n p hp z y)

end PerronWright.BrownianKilledAreaResolventSymmetry
