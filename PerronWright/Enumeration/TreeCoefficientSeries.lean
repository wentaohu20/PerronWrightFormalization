import PerronWright.Enumeration.TreeCoefficientContinuous

/-!
# The actual continuous type-resolved rooted-tree series

The finite type-resolved coefficients already constructed from literal
labelled-tree sums are assembled here into a formal power series with values
in `C(S, ℝ)`.  Multiplication by `X` gives the usual size convention: the
coefficient of degree `n + 1` is the rooted-tree profile with `n` non-root
vertices.  Coefficientwise integration recovers the scalar vertex-rooted EGF.
-/

open MeasureTheory
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The coefficient series before the distinguished root contributes its
single power of the size variable. -/
def CompactBJRModel.rootedTreeProfileSeries
    (M : CompactBJRModel S) : PowerSeries C(S, ℝ) :=
  PowerSeries.mk (M.rootedTreeCoefficientMap)

@[simp] theorem CompactBJRModel.rootedTreeProfileSeries_coeff
    (M : CompactBJRModel S) (n : ℕ) :
    PowerSeries.coeff n M.rootedTreeProfileSeries =
      M.rootedTreeCoefficientMap n := by
  simp [CompactBJRModel.rootedTreeProfileSeries]

/-- The genuine type-resolved vertex-rooted tree EGF, with the root counted
in the size variable. -/
def CompactBJRModel.typeRootedTreeEGF
    (M : CompactBJRModel S) : PowerSeries C(S, ℝ) :=
  PowerSeries.X * M.rootedTreeProfileSeries

@[simp] theorem CompactBJRModel.typeRootedTreeEGF_coeff_zero
    (M : CompactBJRModel S) :
    PowerSeries.coeff 0 M.typeRootedTreeEGF = 0 := by
  simp [CompactBJRModel.typeRootedTreeEGF]

@[simp] theorem CompactBJRModel.typeRootedTreeEGF_coeff_succ
    (M : CompactBJRModel S) (n : ℕ) :
    PowerSeries.coeff (n + 1) M.typeRootedTreeEGF =
      M.rootedTreeCoefficientMap n := by
  rw [CompactBJRModel.typeRootedTreeEGF, PowerSeries.coeff_succ_X_mul]
  exact M.rootedTreeProfileSeries_coeff n

/-- Integrating each actual continuous profile gives exactly the corresponding
coefficient of the scalar vertex-rooted tree EGF. -/
theorem CompactBJRModel.vertexRootedTreeEGF_coeff_eq_typeRootedTreeEGF_integral
    (M : CompactBJRModel S) (k : ℕ) :
    PowerSeries.coeff k (M.vertexRootedTreeEGF 0) =
      ∫ x : S, PowerSeries.coeff k M.typeRootedTreeEGF x ∂M.mu := by
  cases k with
  | zero =>
      simp [CompactBJRModel.vertexRootedTreeEGF]
  | succ n =>
      simpa only [Nat.succ_eq_add_one,
        M.typeRootedTreeEGF_coeff_succ,
        CompactBJRModel.rootedTreeCoefficientMap_apply] using
        M.vertexRootedTreeEGF_coeff_eq_rootedTreeCoefficient_integral n

end PerronWright
