import PerronWright.Kernel.Composition

/-!
# Direct cycle primitive for unicyclic enumeration

This file deliberately does not use a regularized Fredholm determinant.  The
coefficient of the unicyclic series is the diagonal integral of the iterated
continuous kernel.  The elementary estimates below give the local absolute
convergence needed before any singular analysis is introduced.
-/

open MeasureTheory

noncomputable section

namespace PerronWright
namespace KernelCycle

variable {S : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Restriction of a continuous kernel to the diagonal. -/
def diagonal (a : C(S × S, ℝ)) : C(S, ℝ) :=
  { toFun := fun x ↦ a (x, x)
    continuous_toFun := a.continuous.comp (continuous_id.prodMk continuous_id) }

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem diagonal_apply (a : C(S × S, ℝ)) (x : S) :
    diagonal a x = a (x, x) :=
  rfl

theorem integrable_diagonal (a : C(S × S, ℝ)) (mu : Measure S)
    [IsFiniteMeasure mu] : Integrable (diagonal a) mu := by
  apply (diagonal a).continuous.integrable_of_hasCompactSupport
  exact isClosed_closure.isCompact

/-- The trace of a continuous kernel, defined directly as its diagonal
integral. -/
def trace (mu : Measure S) (a : C(S × S, ℝ)) : ℝ :=
  ∫ x, diagonal a x ∂mu

omit [BorelSpace S] in
/-- A direct trace bound, valid for every finite measure. -/
theorem norm_trace_le (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) :
    ‖trace mu a‖ ≤ ‖a‖ * mu.real Set.univ := by
  unfold trace
  apply norm_integral_le_of_norm_le_const
  filter_upwards [] with x
  simpa only [diagonal_apply] using a.norm_coe_le_norm (x, x)

/-- The sup-norm estimate for composing continuous kernels. -/
theorem norm_comp_le (mu : Measure S) [IsFiniteMeasure mu]
    (a b : C(S × S, ℝ)) :
    ‖KernelMap.comp mu a b‖ ≤ mu.real Set.univ * ‖a‖ * ‖b‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro p
  rw [KernelMap.comp_apply]
  calc
    ‖∫ z, a (p.1, z) * b (z, p.2) ∂mu‖
        ≤ (‖a‖ * ‖b‖) * mu.real Set.univ := by
          apply norm_integral_le_of_norm_le_const
          filter_upwards [] with z
          rw [norm_mul]
          exact mul_le_mul (a.norm_coe_le_norm (p.1, z))
            (b.norm_coe_le_norm (z, p.2)) (norm_nonneg _) (norm_nonneg _)
    _ = mu.real Set.univ * ‖a‖ * ‖b‖ := by ring

/-- The iterated kernel whose index `n` represents the `(n+1)`-st operator
power. -/
def iterated (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) : ℕ → C(S × S, ℝ)
  | 0 => a
  | n + 1 => KernelMap.comp mu a (iterated mu a n)

/-- The `(n+1)`-st cycle trace. -/
def cycleTrace (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (n : ℕ) : ℝ :=
  trace mu (iterated mu a n)

/-- Iterated kernels realize iterated integral operators on continuous
functions.  This connects the direct cycle trace to the compact BJR operator,
without introducing a determinant interface. -/
theorem action_iterated (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (f : C(S, ℝ)) (n : ℕ) :
    KernelMap.action mu (iterated mu a n) f =
      (KernelMap.action mu a)^[n + 1] f := by
  induction n generalizing f with
  | zero => simp [iterated]
  | succ n ih =>
      calc
        KernelMap.action mu (iterated mu a n.succ) f =
            KernelMap.action mu a (KernelMap.action mu (iterated mu a n) f) := by
              rw [iterated, KernelMap.action_comp]
        _ = KernelMap.action mu a ((KernelMap.action mu a)^[n + 1] f) := by
              rw [ih]
        _ = (KernelMap.action mu a)^[n.succ + 1] f := by
              simpa only [Nat.succ_eq_add_one] using
                (Function.iterate_succ_apply' (KernelMap.action mu a) (n + 1) f).symm

theorem norm_iterated_le (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (n : ℕ) :
    ‖iterated mu a n‖ ≤ ‖a‖ ^ (n + 1) * (mu.real Set.univ) ^ n := by
  induction n with
  | zero => simp [iterated]
  | succ n ih =>
      rw [iterated]
      calc
        ‖KernelMap.comp mu a (iterated mu a n)‖
            ≤ mu.real Set.univ * ‖a‖ * ‖iterated mu a n‖ :=
              norm_comp_le mu a (iterated mu a n)
        _ ≤ mu.real Set.univ * ‖a‖ *
              (‖a‖ ^ (n + 1) * (mu.real Set.univ) ^ n) := by
              gcongr
        _ = ‖a‖ ^ (n + 1 + 1) * (mu.real Set.univ) ^ (n + 1) := by ring

/-- The direct cycle trace has the expected geometric bound. -/
theorem norm_cycleTrace_le (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (n : ℕ) :
    ‖cycleTrace mu a n‖ ≤ (mu.real Set.univ * ‖a‖) ^ (n + 1) := by
  calc
    ‖cycleTrace mu a n‖
        ≤ ‖iterated mu a n‖ * mu.real Set.univ := norm_trace_le mu _
    _ ≤ (‖a‖ ^ (n + 1) * (mu.real Set.univ) ^ n) * mu.real Set.univ := by
          gcongr
          exact norm_iterated_le mu a n
    _ = (mu.real Set.univ * ‖a‖) ^ (n + 1) := by ring

/-- The `m ≥ 2` term in the direct unicyclic cycle series. -/
def unicyclicTerm (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (w : ℝ) (n : ℕ) : ℝ :=
  w ^ (n + 2) * cycleTrace mu a (n + 1) / (2 * (n + 2))

/-- A geometric majorant for the `n`-th direct unicyclic term.  The bound is
deliberately slightly wasteful (it drops the factor `1 / (2n+4)`), because
that makes uniform convergence on smaller discs immediate. -/
theorem norm_unicyclicTerm_le_geometric (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (w : ℝ)
    (hw : |w| * mu.real Set.univ * ‖a‖ ≤ 1) (n : ℕ) :
    ‖unicyclicTerm mu a w n‖ ≤ (|w| * mu.real Set.univ * ‖a‖) ^ n := by
  unfold unicyclicTerm
  rw [norm_div, norm_mul, Real.norm_eq_abs, abs_pow]
  have htrace := norm_cycleTrace_le mu a (n + 1)
  have htrace' : ‖cycleTrace mu a (n + 1)‖ ≤
      (mu.real Set.univ * ‖a‖) ^ (n + 2) := by
    have hindex : n + 1 + 1 = n + 2 := by omega
    simpa [hindex] using htrace
  have hdenom : 1 ≤ ‖(2 : ℝ) * (n + 2)‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · have hn : 0 ≤ (n : ℝ) := by positivity
      nlinarith
    · positivity
  let q : ℝ := |w| * mu.real Set.univ * ‖a‖
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_le_one : q ≤ 1 := by simpa [q, mul_assoc] using hw
  calc
    |w| ^ (n + 2) * ‖cycleTrace mu a (n + 1)‖ /
          ‖(2 : ℝ) * (n + 2)‖
        ≤ |w| ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) := by
          calc
            _ ≤ |w| ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) /
                ‖(2 : ℝ) * (n + 2)‖ := by
                  gcongr
            _ ≤ |w| ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) := by
                  apply (div_le_iff₀ (by positivity)).2
                  calc
                    |w| ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) =
                        |w| ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) * 1 := by ring
                    _ ≤ |w| ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) *
                        ‖(2 : ℝ) * (n + 2)‖ := by
                          gcongr
    _ = q ^ (n + 2) := by
          dsimp [q]
          ring
    _ ≤ q ^ n := by
          calc
            q ^ (n + 2) = q ^ n * q ^ 2 := by ring
            _ ≤ q ^ n * 1 := by gcongr; nlinarith
            _ = q ^ n := by ring

/-- Absolute convergence of the direct unicyclic series on the natural
geometric neighbourhood `|w| μ(S) ‖a‖ < 1`. -/
theorem summable_unicyclicTerm (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (w : ℝ)
    (hw : |w| * mu.real Set.univ * ‖a‖ < 1) :
    Summable (unicyclicTerm mu a w) := by
  let q : ℝ := |w| * mu.real Set.univ * ‖a‖
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq : q < 1 := by simpa [q, mul_assoc] using hw
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one hq_nonneg hq)
  intro n
  simpa [q, mul_assoc] using norm_unicyclicTerm_le_geometric mu a w hq.le n

/-- The same term, now in the complex variable used for analytic continuation. -/
def unicyclicTermC (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (w : ℂ) (n : ℕ) : ℂ :=
  w ^ (n + 2) * (cycleTrace mu a (n + 1) : ℂ) /
    (((2 : ℝ) * (n + 2)) : ℂ)

/-- A uniform Weierstrass majorant for the complex cycle series on every
closed subdisc satisfying `r μ(S) ‖κ‖ < 1`. -/
theorem norm_unicyclicTermC_le_geometric (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (r : ℝ) (hr : 0 ≤ r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ ≤ 1)
    (w : ℂ) (hw : ‖w‖ ≤ r) (n : ℕ) :
    ‖unicyclicTermC mu a w n‖ ≤ (r * mu.real Set.univ * ‖a‖) ^ n := by
  unfold unicyclicTermC
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have htrace := norm_cycleTrace_le mu a (n + 1)
  have htrace' : ‖cycleTrace mu a (n + 1)‖ ≤
      (mu.real Set.univ * ‖a‖) ^ (n + 2) := by
    have hindex : n + 1 + 1 = n + 2 := by omega
    simpa [hindex] using htrace
  have htrace_abs : |cycleTrace mu a (n + 1)| ≤
      (mu.real Set.univ * ‖a‖) ^ (n + 2) := by
    simpa [Real.norm_eq_abs] using htrace'
  have hdenom : 1 ≤ ‖(2 : ℂ) * ((n : ℂ) + 2)‖ := by
    rw [norm_mul]
    norm_num
    rw [Complex.norm_def, Complex.normSq_apply]
    simp
    have hn : 0 ≤ (n : ℝ) + 2 := by positivity
    rw [Real.sqrt_mul_self hn]
    nlinarith
  have hfactor_nonneg : 0 ≤ mu.real Set.univ * ‖a‖ := by positivity
  let q : ℝ := r * mu.real Set.univ * ‖a‖
  have hq_nonneg : 0 ≤ q := by dsimp [q]; positivity
  have hq_le_one : q ≤ 1 := by simpa [q, mul_assoc] using hsubcritical
  calc
    ‖w‖ ^ (n + 2) * |cycleTrace mu a (n + 1)| /
          ‖(2 : ℂ) * ((n : ℂ) + 2)‖
        ≤ r ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) := by
          calc
            _ ≤ ‖w‖ ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) /
                ‖(2 : ℂ) * ((n : ℂ) + 2)‖ := by
                  gcongr
            _ ≤ r ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) /
                ‖(2 : ℂ) * ((n : ℂ) + 2)‖ := by
                  gcongr
            _ ≤ r ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) := by
                  apply (div_le_iff₀ (by positivity)).2
                  calc
                    r ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) =
                        r ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) * 1 := by ring
                    _ ≤ r ^ (n + 2) * (mu.real Set.univ * ‖a‖) ^ (n + 2) *
                        ‖(2 : ℂ) * ((n : ℂ) + 2)‖ := by
                          gcongr
    _ = q ^ (n + 2) := by dsimp [q]; ring
    _ ≤ q ^ n := by
          calc
            q ^ (n + 2) = q ^ n * q ^ 2 := by ring
            _ ≤ q ^ n * 1 := by gcongr; nlinarith
            _ = q ^ n := by ring

/-- Absolute (hence normal) convergence of the complex cycle series on every
strictly subcritical closed disc. -/
theorem summable_unicyclicTermC (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (r : ℝ) (hr : 0 ≤ r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    Summable (unicyclicTermC mu a w) := by
  let q : ℝ := r * mu.real Set.univ * ‖a‖
  have hq_nonneg : 0 ≤ q := by dsimp [q]; positivity
  have hq : q < 1 := by simpa [q, mul_assoc] using hsubcritical
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one hq_nonneg hq)
  intro n
  simpa [q, mul_assoc] using
    norm_unicyclicTermC_le_geometric mu a r hr hsubcritical.le w hw n

end KernelCycle
end PerronWright
