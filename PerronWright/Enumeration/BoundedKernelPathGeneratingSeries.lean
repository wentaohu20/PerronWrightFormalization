import PerronWright.Enumeration.BoundedKernelPathAmplitude
import PerronWright.Enumeration.CubicKernelPathGeneratingSeries

/-!
# Formal path products for arbitrary bounded kernels

The one-edge path coefficient and its resolvent sum do not depend on cubic
valence.  This file therefore extends the formal finite-product construction
from cubic kernels to every bounded endpoint table.  Its degree-`d`
coefficient is the literal finite antidiagonal of all assignments of `d`
internal degree-two vertices to the kernel edges, and on a strict
subcritical profile ball the product of the one-edge sums is the product of
the genuine marked-path resolvent kernels.

This is the unrestricted length-assignment series.  Identifying its
admissible part with the actual fixed-surplus core sum still requires a
general, variable-valence subdivision classification and the finite local
simple-graph corrections.
-/

open MeasureTheory PerronWright
open scoped Classical BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Product of the one-edge formal path series over an arbitrary bounded
kernel endpoint table. -/
def boundedKernelPathProductSeries
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S) : PowerSeries ℂ :=
  ∏ e : Fin D.2.1.val,
    profilePathEdgeSeries M tau
      (x (boundedKernelOrderedEndpoints D e).1)
      (x (boundedKernelOrderedEndpoints D e).2)

/-- Exact coefficient formula for the unrestricted bounded-kernel path
product. -/
theorem boundedKernelPathProductSeries_coeff
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S) (d : ℕ) :
    PowerSeries.coeff d (boundedKernelPathProductSeries M tau D x) =
      ∑ l ∈ (Finset.univ.finsuppAntidiag d :
          Finset (Fin D.2.1.val →₀ ℕ)),
        ∏ e : Fin D.2.1.val,
          profilePathEdgeCoefficient M tau
            (x (boundedKernelOrderedEndpoints D e).1)
            (x (boundedKernelOrderedEndpoints D e).2) (l e) := by
  classical
  unfold boundedKernelPathProductSeries
  simpa only [profilePathEdgeSeries_coeff] using
    (PowerSeries.coeff_prod
      (fun e : Fin D.2.1.val ↦
        profilePathEdgeSeries M tau
          (x (boundedKernelOrderedEndpoints D e).1)
          (x (boundedKernelOrderedEndpoints D e).2))
      d Finset.univ)

/-- On a strict subcritical profile ball, the product of all one-edge
coefficient sums is the product of the genuine path-resolvent kernels for
an arbitrary bounded endpoint table. -/
theorem prod_tsum_boundedKernelPathEdgeCoefficient_eq_pathResolventKernel
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S)
    (p : C(S, ℂ) × ℂ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ y, ‖MarkedPathResolvent.profile M hM p y‖ ≤ q) :
    (∏ e : Fin D.2.1.val,
        ∑' n : ℕ,
          profilePathEdgeCoefficient M
            (MarkedPathResolvent.profile M hM p)
            (x (boundedKernelOrderedEndpoints D e).1)
            (x (boundedKernelOrderedEndpoints D e).2) n) =
      ∏ e : Fin D.2.1.val,
        MarkedPathResolvent.pathResolventKernel M hM p
          (x (boundedKernelOrderedEndpoints D e).1,
            x (boundedKernelOrderedEndpoints D e).2) := by
  apply Finset.prod_congr rfl
  intro e _
  exact tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
    M hM p q hq hq1 ha _ _

/-- For a cubic labelled kernel, the bounded-kernel formal product reduces
definitionally to the existing cubic formal product. -/
@[simp] theorem boundedKernelPathProductSeries_cubicKernelBoundedShape
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) :
    boundedKernelPathProductSeries M tau (cubicKernelBoundedShape K) x =
      cubicKernelPathProductSeries M tau K x := by
  unfold boundedKernelPathProductSeries cubicKernelPathProductSeries
    cubicKernelBoundedShape
  rfl

end PerronWright.GraphCore
