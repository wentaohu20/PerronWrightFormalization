import PerronWright.Enumeration.RootedTreeAnalyticBridge
import PerronWright.Analysis.TreePhysicalBranch

/-!
# Formal height iteration and finite rooted-tree sums

This module fixes the canonical one-variable formal multilinear series of the
actual labelled-tree EGF, records its analytic zero-tree germ, and constructs
the formal Picard iterates.  It also proves low-degree stabilization and the
basic positivity properties of the finite size truncations.
-/

open scoped Classical Topology
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The canonical one-variable formal multilinear series attached to an
ordinary Banach-valued power series. -/
def oneDimensionalFormalMultilinearSeries
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (F : PowerSeries A) : FormalMultilinearSeries ℂ ℂ A :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
    (PowerSeries.coeff n F)

@[simp] theorem oneDimensionalFormalMultilinearSeries_coeff
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (F : PowerSeries A) (n : ℕ) :
    (oneDimensionalFormalMultilinearSeries F).coeff n =
      PowerSeries.coeff n F := by
  simp [oneDimensionalFormalMultilinearSeries,
    FormalMultilinearSeries.coeff,
    ContinuousMultilinearMap.mkPiRing_apply]

@[simp] theorem oneDimensionalPowerSeries_oneDimensionalFormalMultilinearSeries
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (F : PowerSeries A) :
    oneDimensionalPowerSeries
      (oneDimensionalFormalMultilinearSeries F) = F := by
  apply PowerSeries.ext
  intro n
  simp only [oneDimensionalPowerSeries_coeff,
    oneDimensionalFormalMultilinearSeries_coeff]

@[simp] theorem oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (p : FormalMultilinearSeries ℂ ℂ A) :
    oneDimensionalFormalMultilinearSeries
      (oneDimensionalPowerSeries p) = p := by
  funext n
  simp only [oneDimensionalFormalMultilinearSeries,
    oneDimensionalPowerSeries_coeff]
  exact FormalMultilinearSeries.mkPiRing_coeff_eq p n

/-- The canonical passage from an ordinary power series to its
one-dimensional formal multilinear series preserves addition. -/
theorem oneDimensionalFormalMultilinearSeries_map_add
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (F G : PowerSeries A) :
    oneDimensionalFormalMultilinearSeries (F + G) =
      oneDimensionalFormalMultilinearSeries F +
        oneDimensionalFormalMultilinearSeries G := by
  apply FormalMultilinearSeries.ext
  intro n
  apply ContinuousMultilinearMap.ext
  intro x
  simp only [oneDimensionalFormalMultilinearSeries,
    FormalMultilinearSeries.add_apply, add_apply,
    ContinuousMultilinearMap.mkPiRing_apply, map_add, smul_add]

/-- The canonical passage from an ordinary power series to its
one-dimensional formal multilinear series preserves finite sums. -/
theorem oneDimensionalFormalMultilinearSeries_map_finset_sum
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F : ι → PowerSeries A) :
    oneDimensionalFormalMultilinearSeries (∑ i ∈ s, F i) =
      ∑ i ∈ s, oneDimensionalFormalMultilinearSeries (F i) := by
  induction s using Finset.induction_on with
  | empty =>
      apply FormalMultilinearSeries.ext
      intro n
      simp only [Finset.sum_empty, FormalMultilinearSeries.zero_apply]
      apply ContinuousMultilinearMap.ext
      intro x
      simp only [oneDimensionalFormalMultilinearSeries,
        ContinuousMultilinearMap.mkPiRing_apply, map_zero, smul_zero,
        zero_apply]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi,
        oneDimensionalFormalMultilinearSeries_map_add, ih]

/-- The canonical passage from an ordinary power series to its
one-dimensional formal multilinear series commutes with scalar
multiplication. -/
theorem oneDimensionalFormalMultilinearSeries_map_smul
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (c : ℂ) (F : PowerSeries A) :
    c • oneDimensionalFormalMultilinearSeries F =
      oneDimensionalFormalMultilinearSeries (c • F) := by
  apply FormalMultilinearSeries.ext
  intro n
  apply ContinuousMultilinearMap.ext
  intro x
  simp only [oneDimensionalFormalMultilinearSeries,
    FormalMultilinearSeries.smul_apply, smul_apply,
    ContinuousMultilinearMap.mkPiRing_apply, PowerSeries.coeff_smul]
  exact smul_comm c (∏ i, x i) (PowerSeries.coeff n F)

/-- Canonical analytic Taylor series of the actual labelled-tree EGF. -/
def CompactBJRModel.complexTypeRootedTreeFMS
    (M : CompactBJRModel S) :
    FormalMultilinearSeries ℂ ℂ C(S, ℂ) :=
  oneDimensionalFormalMultilinearSeries M.complexTypeRootedTreeEGF

/-- The analytic zero-tree germ has the canonical formal multilinear series
of the actual labelled-tree EGF. -/
theorem CompactBJRModel.exists_zeroTreeBranch_with_canonicalTaylorSeries
    (M : CompactBJRModel S) :
    ∃ psi : ℂ × C(S, ℂ) → C(S, ℂ),
      AnalyticAt ℂ psi (0, 0) ∧
      psi (0, 0) = 0 ∧
      (∀ᶠ x in 𝓝 (0, (0 : C(S, ℂ))),
        TreeCritical.residual M (x, psi x) = 0) ∧
      HasFPowerSeriesAt (fun z ↦ psi (z, 0))
        M.complexTypeRootedTreeFMS 0 := by
  obtain ⟨psi, p, hpsi, hpsi0, hres, hp, hpPower⟩ :=
    M.exists_zeroTreeBranch_with_labelledTreeTaylorSeries
  refine ⟨psi, hpsi, hpsi0, hres, ?_⟩
  have hpCanonical : p = M.complexTypeRootedTreeFMS := by
    rw [← oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries p,
      hpPower]
    rfl
  simpa only [hpCanonical] using hp

/-- Picard iteration of the genuine rooted-tree operator in the formal-series
ring.  The index is the permitted rooted height, with the zero iterate empty. -/
def CompactBJRModel.rootedTreeFormalIter
    (M : CompactBJRModel S) : ℕ → PowerSeries C(S, ℝ)
  | 0 => 0
  | n + 1 => M.rootedTreeFormalRHS (M.rootedTreeFormalIter n)

@[simp] theorem CompactBJRModel.rootedTreeFormalIter_zero
    (M : CompactBJRModel S) :
    M.rootedTreeFormalIter 0 = 0 := rfl

@[simp] theorem CompactBJRModel.rootedTreeFormalIter_succ
    (M : CompactBJRModel S) (n : ℕ) :
    M.rootedTreeFormalIter (n + 1) =
      M.rootedTreeFormalRHS (M.rootedTreeFormalIter n) := rfl

@[simp] theorem CompactBJRModel.rootedTreeFormalIter_constantCoeff
    (M : CompactBJRModel S) (n : ℕ) :
    PowerSeries.constantCoeff (M.rootedTreeFormalIter n) = 0 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [M.rootedTreeFormalIter_succ,
        ← PowerSeries.coeff_zero_eq_constantCoeff]
      exact M.rootedTreeFormalRHS_coeff_zero (M.rootedTreeFormalIter n)

/-- After `n` formal Picard steps, all coefficients of degree strictly below
`n` have stabilized to the actual labelled-tree coefficients. -/
theorem CompactBJRModel.rootedTreeFormalIter_coeff_eq_typeRootedTreeEGF
    (M : CompactBJRModel S) {n k : ℕ} (hk : k < n) :
    PowerSeries.coeff k (M.rootedTreeFormalIter n) =
      PowerSeries.coeff k M.typeRootedTreeEGF := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero =>
          simp only [M.rootedTreeFormalIter_succ,
            M.rootedTreeFormalRHS_coeff_zero,
            M.typeRootedTreeEGF_coeff_zero]
      | succ m =>
          let AI := M.kernelActionPowerSeries (M.rootedTreeFormalIter n)
          let AT := M.kernelActionPowerSeries M.typeRootedTreeEGF
          have hAI0 : PowerSeries.constantCoeff AI = 0 := by
            dsimp only [AI]
            rw [M.kernelActionPowerSeries_constantCoeff,
              M.rootedTreeFormalIter_constantCoeff, map_zero]
          have hAT0 : PowerSeries.constantCoeff AT = 0 :=
            M.kernelAction_typeRootedTreeEGF_constantCoeff
          have hAcoeff : ∀ j ≤ m,
              PowerSeries.coeff j AI = PowerSeries.coeff j AT := by
            intro j hj
            dsimp only [AI, AT]
            simp only [M.kernelActionPowerSeries_coeff]
            rw [ih (k := j) (by omega)]
          have hExp := powerSeries_subst_exp_coeff_eq_of_coeff_eq_up_to
            AI AT hAI0 hAT0 m hAcoeff
          have hIter := congrArg (PowerSeries.coeff (m + 1))
            (M.rootedTreeFormalIter_succ n)
          have hTree := congrArg (PowerSeries.coeff (m + 1))
            M.typeRootedTreeEGF_eq_rootedTreeFormalRHS
          rw [CompactBJRModel.rootedTreeFormalRHS,
            PowerSeries.coeff_succ_X_mul,
            PowerSeries.coeff_C_mul] at hIter hTree
          calc
            PowerSeries.coeff (m + 1) (M.rootedTreeFormalIter (n + 1)) =
                M.zeroTreeVertexFactor *
                  PowerSeries.coeff m
                    (PowerSeries.subst AI (PowerSeries.exp C(S, ℝ))) := by
              simpa only [AI] using hIter
            _ = M.zeroTreeVertexFactor *
                  PowerSeries.coeff m
                    (PowerSeries.subst AT (PowerSeries.exp C(S, ℝ))) := by
              rw [hExp]
            _ = PowerSeries.coeff (m + 1) M.typeRootedTreeEGF := by
              simpa only [AT] using hTree.symm

/-- Every actual labelled-tree coefficient is pointwise nonnegative. -/
theorem CompactBJRModel.typeRootedTreeEGF_coeff_nonneg
    (M : CompactBJRModel S) (n : ℕ) (x : S) :
    0 ≤ PowerSeries.coeff n M.typeRootedTreeEGF x := by
  cases n with
  | zero => simp
  | succ n =>
      rw [M.typeRootedTreeEGF_coeff_succ,
        M.rootedTreeCoefficientMap_apply]
      exact M.rootedTreeCoefficient_nonneg n x

/-- Finite size truncation of the actual type-resolved rooted-tree EGF. -/
def CompactBJRModel.rootedTreePartialSum
    (M : CompactBJRModel S) (N : ℕ) (w : ℝ) : C(S, ℝ) :=
  ∑ k ∈ Finset.range N,
    w ^ k • PowerSeries.coeff k M.typeRootedTreeEGF

@[simp] theorem CompactBJRModel.rootedTreePartialSum_zero
    (M : CompactBJRModel S) (w : ℝ) :
    M.rootedTreePartialSum 0 w = 0 := by
  simp [CompactBJRModel.rootedTreePartialSum]

theorem CompactBJRModel.rootedTreePartialSum_succ
    (M : CompactBJRModel S) (N : ℕ) (w : ℝ) :
    M.rootedTreePartialSum (N + 1) w =
      M.rootedTreePartialSum N w +
        w ^ N • PowerSeries.coeff N M.typeRootedTreeEGF := by
  simp [CompactBJRModel.rootedTreePartialSum, Finset.sum_range_succ]

theorem CompactBJRModel.rootedTreePartialSum_nonneg
    (M : CompactBJRModel S) (N : ℕ) {w : ℝ} (hw : 0 ≤ w) (x : S) :
    0 ≤ M.rootedTreePartialSum N w x := by
  unfold CompactBJRModel.rootedTreePartialSum
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  exact Finset.sum_nonneg fun k hk =>
    mul_nonneg (pow_nonneg hw _) (M.typeRootedTreeEGF_coeff_nonneg k x)

theorem CompactBJRModel.rootedTreePartialSum_mono
    (M : CompactBJRModel S) (N : ℕ) {w : ℝ} (hw : 0 ≤ w) (x : S) :
    M.rootedTreePartialSum N w x ≤
      M.rootedTreePartialSum (N + 1) w x := by
  rw [M.rootedTreePartialSum_succ, ContinuousMap.add_apply]
  exact le_add_of_nonneg_right <|
    show 0 ≤ (w ^ N • PowerSeries.coeff N M.typeRootedTreeEGF) x by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (pow_nonneg hw _) (M.typeRootedTreeEGF_coeff_nonneg N x)

end PerronWright
