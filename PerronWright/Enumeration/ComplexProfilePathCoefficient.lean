import PerronWright.Enumeration.UnicyclicCycleWeightTrace
import PerronWright.Enumeration.BoundedKernelPathGeneratingSeries

/-!
# Literal complex-profile paths and formal edge coefficients

This file identifies the coefficient used by the generic kernel-edge
generating series with the genuine finite-dimensional path integral.  It is
the coefficient-level analytic bridge needed before a fixed core can be
regrouped by its degree-two path lengths.

No infinite sum or graph-classification assertion is made here: every
identity is for a fixed path length, or for the finite antidiagonal in one
coefficient of a fixed bounded endpoint table.
-/

open MeasureTheory PerronWright
open scoped Classical BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Reversal preserves the complex-profile integrand of the standard finite
path. -/
theorem finiteComplexGraphIntegrand_pathGraph_rev
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (m : ℕ) (x : Fin m → S) :
    finiteComplexGraphIntegrand M tau (SimpleGraph.pathGraph m)
        (fun i ↦ x i.rev) =
      finiteComplexGraphIntegrand M tau (SimpleGraph.pathGraph m) x := by
  let r : SimpleGraph.pathGraph m ≃g SimpleGraph.pathGraph m :=
    { Fin.revPerm with
      map_rel_iff' := by
        intro i j
        exact pathGraph_adj_rev m i j }
  have h := finiteComplexGraphIntegrand_iso M tau
    (SimpleGraph.pathGraph m) (SimpleGraph.pathGraph m) r x
  change finiteComplexGraphIntegrand M tau (SimpleGraph.pathGraph m)
      (x ∘ Fin.revPerm) =
    finiteComplexGraphIntegrand M tau (SimpleGraph.pathGraph m) x
  exact h

/-- Reversing all internal coordinates exchanges the endpoint roles of the
literal complex-profile path observable. -/
theorem complexProfilePathObservable_rev
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (n : ℕ) (a b : S) (x : Fin (n + 1) → S) :
    complexProfilePathObservable M tau n a b (fun i ↦ x i.rev) =
      complexProfilePathObservable M tau n b a x := by
  change
    (M.kernel a (x (Fin.rev 0)) : ℂ) *
      finiteComplexGraphIntegrand M tau
        (SimpleGraph.pathGraph (n + 1)) (fun i ↦ x i.rev) *
      (M.kernel (x (Fin.rev (Fin.last n))) b : ℂ) = _
  simp only [Fin.rev_zero, Fin.rev_last,
    finiteComplexGraphIntegrand_pathGraph_rev]
  change
    (M.kernel a (x (Fin.last n)) : ℂ) *
      finiteComplexGraphIntegrand M tau
        (SimpleGraph.pathGraph (n + 1)) x *
      (M.kernel (x 0) b : ℂ) =
    (M.kernel b (x 0) : ℂ) *
      finiteComplexGraphIntegrand M tau
        (SimpleGraph.pathGraph (n + 1)) x *
      (M.kernel (x (Fin.last n)) a : ℂ)
  rw [M.kernel.symmetric a (x (Fin.last n)),
    M.kernel.symmetric (x 0) b]
  ring

/-- Reversal of the product type law, in the complex-valued form used by
the profile path. -/
private theorem integral_complexProfilePathObservable_rev
    (M : CompactBJRModel S) (n : ℕ)
    (F : C((Fin (n + 1) → S), ℂ)) :
    (∫ x : Fin (n + 1) → S, F (fun i ↦ x i.rev)
      ∂Measure.pi (fun _ : Fin (n + 1) ↦ M.mu)) =
      ∫ x : Fin (n + 1) → S, F x
      ∂Measure.pi (fun _ : Fin (n + 1) ↦ M.mu) := by
  let e := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (n + 1) ↦ S) (Fin.revPerm (n := n + 1))
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) ↦ M.mu))
      (Measure.pi (fun _ : Fin (n + 1) ↦ M.mu)) :=
    measurePreserving_piCongrLeft
      (fun _ : Fin (n + 1) ↦ M.mu) (Fin.revPerm (n := n + 1))
  have he (x : Fin (n + 1) → S) :
      e x = (fun i ↦ x i.rev) := by
    funext i
    simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      Fin.revPerm]
  simpa only [he] using
    (hmp.integral_comp' (fun x : Fin (n + 1) → S ↦ F x))

/-- The literal complex-profile path weight is independent of endpoint
orientation for every number of internal vertices. -/
theorem complexProfilePathWeight_symmetric
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (n : ℕ) (a b : S) :
    complexProfilePathWeight M tau n a b =
      complexProfilePathWeight M tau n b a := by
  cases n with
  | zero =>
      change (M.kernel a b : ℂ) = (M.kernel b a : ℂ)
      rw [M.kernel.symmetric a b]
  | succ n =>
      change
        (∫ x : Fin (n + 1) → S,
          complexProfilePathObservable M tau n a b x
          ∂Measure.pi (fun _ : Fin (n + 1) ↦ M.mu)) =
        ∫ x : Fin (n + 1) → S,
          complexProfilePathObservable M tau n b a x
          ∂Measure.pi (fun _ : Fin (n + 1) ↦ M.mu)
      calc
        _ = ∫ x : Fin (n + 1) → S,
            complexProfilePathObservable M tau n b a (fun i ↦ x i.rev)
            ∂Measure.pi (fun _ : Fin (n + 1) ↦ M.mu) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact (complexProfilePathObservable_rev M tau n b a x).symm
        _ = _ := integral_complexProfilePathObservable_rev M n
          (complexProfilePathObservable M tau n b a)

/-- The abstract one-edge coefficient is exactly the literal integral of
the corresponding path with that many internal vertices. -/
theorem complexProfilePathWeight_eq_profilePathEdgeCoefficient
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (a b : S) (n : ℕ) :
    complexProfilePathWeight M tau n a b =
      profilePathEdgeCoefficient M tau a b n := by
  simpa only [profilePathEdgeCoefficient] using
    complexProfilePathWeight_eq_operatorPower M tau n a b

/-- The generic one-edge coefficient is likewise symmetric in its two
endpoint types. -/
theorem profilePathEdgeCoefficient_symmetric
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (a b : S) (n : ℕ) :
    profilePathEdgeCoefficient M tau a b n =
      profilePathEdgeCoefficient M tau b a n := by
  rw [← complexProfilePathWeight_eq_profilePathEdgeCoefficient,
    ← complexProfilePathWeight_eq_profilePathEdgeCoefficient]
  exact complexProfilePathWeight_symmetric M tau n a b

/-- The generic coefficient attached canonically to an unordered endpoint
pair. -/
def profilePathEdgeFactor
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {V : Type*} (x : V → S) (n : ℕ) (z : Sym2 V) : ℂ :=
  Sym2.lift ⟨fun i j ↦ profilePathEdgeCoefficient M tau (x i) (x j) n,
    by
      intro i j
      exact profilePathEdgeCoefficient_symmetric M tau (x i) (x j) n⟩ z

@[simp] theorem profilePathEdgeFactor_mk
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {V : Type*} (x : V → S) (n : ℕ) (i j : V) :
    profilePathEdgeFactor M tau x n s(i,j) =
      profilePathEdgeCoefficient M tau (x i) (x j) n := rfl

/-- Consequently, each coefficient of the formal one-edge series is the
literal finite path integral. -/
theorem profilePathEdgeSeries_coeff_eq_complexProfilePathWeight
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (a b : S) (n : ℕ) :
    PowerSeries.coeff n (profilePathEdgeSeries M tau a b) =
      complexProfilePathWeight M tau n a b := by
  rw [profilePathEdgeSeries_coeff]
  exact (complexProfilePathWeight_eq_profilePathEdgeCoefficient
    M tau a b n).symm

/-- For a fixed bounded endpoint table and fixed branch coordinates, one
coefficient of the unrestricted path product is the exact finite sum of
products of literal path integrals. -/
theorem boundedKernelPathProductSeries_coeff_eq_literalPathWeights
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S) (d : ℕ) :
    PowerSeries.coeff d (boundedKernelPathProductSeries M tau D x) =
      ∑ l ∈ (Finset.univ.finsuppAntidiag d :
          Finset (Fin D.2.1.val →₀ ℕ)),
        ∏ e : Fin D.2.1.val,
          complexProfilePathWeight M tau (l e)
            (x (boundedKernelOrderedEndpoints D e).1)
            (x (boundedKernelOrderedEndpoints D e).2) := by
  rw [boundedKernelPathProductSeries_coeff]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.prod_congr rfl
  intro e he
  exact (complexProfilePathWeight_eq_profilePathEdgeCoefficient M tau
    (x (boundedKernelOrderedEndpoints D e).1)
    (x (boundedKernelOrderedEndpoints D e).2) (l e)).symm

end PerronWright.GraphCore
