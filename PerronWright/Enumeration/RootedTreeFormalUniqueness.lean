import PerronWright.Enumeration.RootedTreeFormalIdentity

/-!
# Uniqueness of the formal rooted-tree fixed point

The first step is purely formal: a zero-constant fixed point of the genuine
compact-BJR rooted-tree operator is unique.  This avoids assuming any radius
of convergence or identifying analytic coefficients by fiat.
-/

open scoped Classical
noncomputable section

namespace PerronWright

/-- Substitution of a zero-constant series into the formal exponential has
constant coefficient one. -/
private theorem subst_exp_coeff_zero
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (A : PowerSeries R) (hA0 : PowerSeries.constantCoeff A = 0) :
    PowerSeries.coeff 0
      (PowerSeries.subst A (PowerSeries.exp R)) = 1 := by
  have hA : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  rw [PowerSeries.coeff_subst' hA (PowerSeries.exp R) 0,
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_pow, hA0, zero_pow hd, smul_zero]

/-- The degree-`n` coefficient of `exp(A)` only depends on the coefficients
of the zero-constant input `A` through degree `n`. -/
theorem powerSeries_subst_exp_coeff_eq_of_coeff_eq_up_to
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (A B : PowerSeries R)
    (hA0 : PowerSeries.constantCoeff A = 0)
    (hB0 : PowerSeries.constantCoeff B = 0)
    (n : ℕ)
    (hcoeff : ∀ k ≤ n, PowerSeries.coeff k A = PowerSeries.coeff k B) :
    PowerSeries.coeff n (PowerSeries.subst A (PowerSeries.exp R)) =
      PowerSeries.coeff n (PowerSeries.subst B (PowerSeries.exp R)) := by
  induction n using Nat.strong_induction_on generalizing A B with
  | h n ih =>
      cases n with
      | zero =>
          rw [subst_exp_coeff_zero A hA0, subst_exp_coeff_zero B hB0]
      | succ m =>
          have hAs : PowerSeries.HasSubst A :=
            PowerSeries.HasSubst.of_constantCoeff_zero' hA0
          have hBs : PowerSeries.HasSubst B :=
            PowerSeries.HasSubst.of_constantCoeff_zero' hB0
          have huQ : IsUnit (((m + 1 : ℕ) : ℚ)) :=
            isUnit_iff_ne_zero.mpr (by positivity)
          have hu : IsUnit ((m + 1 : ℕ) : R) := by
            simpa only [map_natCast] using huQ.map (algebraMap ℚ R)
          apply hu.mul_left_cancel
          simp only [Nat.cast_add, Nat.cast_one]
          rw [powerSeries_subst_exp_coeff_succ A hAs m,
            powerSeries_subst_exp_coeff_succ B hBs m]
          apply Finset.sum_congr rfl
          intro ij hij
          rw [Finset.mem_antidiagonal] at hij
          have hi : ij.1 < m + 1 := by omega
          have hleft := ih ij.1 hi A B hA0 hB0
            (fun k hk => hcoeff k (by omega))
          rw [hleft]
          congr 2
          exact hcoeff (ij.2 + 1) (by omega)

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The genuine labelled-tree series is the unique zero-constant formal
fixed point of the compact-BJR rooted-tree operator. -/
theorem CompactBJRModel.rootedTreeFormalRHS_fixedPoint_unique
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℝ))
    (hF0 : PowerSeries.constantCoeff F = 0)
    (hF : F = M.rootedTreeFormalRHS F) :
    F = M.typeRootedTreeEGF := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          calc
            PowerSeries.coeff 0 F = 0 := by
              simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hF0
            _ = PowerSeries.coeff 0 M.typeRootedTreeEGF :=
              M.typeRootedTreeEGF_coeff_zero.symm
      | succ m =>
          let AF := M.kernelActionPowerSeries F
          let AT := M.kernelActionPowerSeries M.typeRootedTreeEGF
          have hAF0 : PowerSeries.constantCoeff AF = 0 := by
            dsimp only [AF]
            rw [M.kernelActionPowerSeries_constantCoeff, hF0, map_zero]
          have hAT0 : PowerSeries.constantCoeff AT = 0 := by
            exact M.kernelAction_typeRootedTreeEGF_constantCoeff
          have hAcoeff : ∀ k ≤ m,
              PowerSeries.coeff k AF = PowerSeries.coeff k AT := by
            intro k hk
            dsimp only [AF, AT]
            simp only [M.kernelActionPowerSeries_coeff]
            rw [ih k (by omega)]
          have hExp := powerSeries_subst_exp_coeff_eq_of_coeff_eq_up_to
            AF AT hAF0 hAT0 m hAcoeff
          have hFn := congrArg (PowerSeries.coeff (m + 1)) hF
          have hTn := congrArg (PowerSeries.coeff (m + 1))
            M.typeRootedTreeEGF_eq_rootedTreeFormalRHS
          rw [CompactBJRModel.rootedTreeFormalRHS,
            PowerSeries.coeff_succ_X_mul,
            PowerSeries.coeff_C_mul] at hFn hTn
          calc
            PowerSeries.coeff (m + 1) F =
                M.zeroTreeVertexFactor *
                  PowerSeries.coeff m
                    (PowerSeries.subst AF (PowerSeries.exp C(S, ℝ))) := by
              simpa only [AF] using hFn
            _ = M.zeroTreeVertexFactor *
                  PowerSeries.coeff m
                    (PowerSeries.subst AT (PowerSeries.exp C(S, ℝ))) := by
              rw [hExp]
            _ = PowerSeries.coeff (m + 1) M.typeRootedTreeEGF := by
              simpa only [AT] using hTn.symm

end PerronWright
