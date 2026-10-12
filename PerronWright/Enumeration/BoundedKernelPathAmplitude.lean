import PerronWright.Enumeration.FixedSurplusCubicNoncubicSplit
import PerronWright.Enumeration.FiniteKernelGeneral
import PerronWright.Analysis.MarkedPathResolvent

/-!
# Joint analytic amplitudes for bounded suppressed kernels

Every edge of a bounded positive-surplus kernel contributes one marked-path
resolvent.  Multiplying the local rank-one splitting by the fold coordinate
removes that edge's simple pole.  This file performs that normalization for
an arbitrary bounded endpoint table and then takes the finite product over
all of its edge labels.

Thus a table with `e` edge labels has a jointly analytic amplitude `A` such
that, on the punctured fold germ,

`A(g,X) = X^e * product(path resolvent kernels)`.

For `e < 3 * ell`, its zero-field slice acquires an additional factor `X`
after cubic normalization.  The construction is independent of cubicity;
the noncubic graph theorem at the end supplies the strict inequality for an
actual admissible core.  This is the analytic edge-product bridge only: an
exact regrouping of the full fixed-core profile series into these products
still requires the corresponding general subdivision classification.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.GraphCore

namespace BKPA_MPR

export PerronWright.MarkedPathResolvent
  (residueKernel residueKernel_analytic
   pathRemainderKernel pathRemainderKernel_analytic
   pathResolventKernel pathResolventKernel_fixed_residue_split)

end BKPA_MPR

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- One marked-path kernel after multiplication by the fold coordinate.
This expression is defined and analytic also on the critical axis. -/
def boundedNormalizedPathKernel
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (q : C(S, ℂ) × ℂ) : C(S × S, ℂ) :=
  BKPA_MPR.residueKernel M hM q.1 +
    q.2 • BKPA_MPR.pathRemainderKernel M hM q

/-- The pole-removed one-edge kernel is jointly analytic in the field and
fold coordinate. -/
theorem boundedNormalizedPathKernel_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (boundedNormalizedPathKernel M hM) (0, 0) := by
  have hresidue : AnalyticAt ℂ
      (fun q : C(S, ℂ) × ℂ ↦ BKPA_MPR.residueKernel M hM q.1)
      (0, 0) :=
    (BKPA_MPR.residueKernel_analytic M hM).comp_of_eq analyticAt_fst rfl
  exact hresidue.add
    (analyticAt_snd.smul (BKPA_MPR.pathRemainderKernel_analytic M hM))

/-- On the critical axis the normalized edge kernel is its frozen pole
residue. -/
@[simp] theorem boundedNormalizedPathKernel_axis
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (g : C(S, ℂ)) :
    boundedNormalizedPathKernel M hM (g, 0) =
      BKPA_MPR.residueKernel M hM g := by
  simp [boundedNormalizedPathKernel]

/-- In particular, the value at the joint base point is the Perron residue
kernel at zero field. -/
@[simp] theorem boundedNormalizedPathKernel_base
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    boundedNormalizedPathKernel M hM (0, 0) =
      BKPA_MPR.residueKernel M hM 0 :=
  boundedNormalizedPathKernel_axis M hM 0

/-- On the punctured germ, the analytic one-edge normalization is exactly
`X` times the genuine marked-path resolvent kernel. -/
theorem boundedNormalizedPathKernel_eq_smul_pathResolventKernel
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      boundedNormalizedPathKernel M hM q =
        q.2 • BKPA_MPR.pathResolventKernel M hM q := by
  filter_upwards
    [BKPA_MPR.pathResolventKernel_fixed_residue_split M hM] with q hsplit
  intro hX
  calc
    boundedNormalizedPathKernel M hM q =
        BKPA_MPR.residueKernel M hM q.1 +
          q.2 • BKPA_MPR.pathRemainderKernel M hM q := rfl
    _ = q.2 •
        (q.2⁻¹ • BKPA_MPR.residueKernel M hM q.1 +
          BKPA_MPR.pathRemainderKernel M hM q) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hX, one_smul]
    _ = q.2 • BKPA_MPR.pathResolventKernel M hM q := by
      rw [← hsplit hX]

/-- Canonical endpoint order for one edge of a bounded normalized kernel
table. -/
def boundedKernelOrderedEndpoints {ell : ℕ}
    (D : BoundedKernelShape ell) (e : Fin D.2.1.val) :
    Fin D.1.val × Fin D.1.val :=
  (Sym2.sortEquiv (D.2.2 e)).1

/-- A cubic labelled kernel viewed as a member of the ambient bounded
kernel-shape type. -/
def cubicKernelBoundedShape {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) : BoundedKernelShape ell :=
  ⟨⟨2 * ell, by omega⟩, ⟨3 * ell, by omega⟩, K.graph.endpoints⟩

@[simp] theorem cubicKernelBoundedShape_vertexCount
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    (cubicKernelBoundedShape K).1.val = 2 * ell := rfl

@[simp] theorem cubicKernelBoundedShape_edgeCount
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    (cubicKernelBoundedShape K).2.1.val = 3 * ell := rfl

@[simp] theorem cubicKernelBoundedShape_table
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) :
    (cubicKernelBoundedShape K).2.2 e = K.graph.endpoints e := rfl

@[simp] theorem boundedKernelOrderedEndpoints_cubicKernelBoundedShape
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) :
    boundedKernelOrderedEndpoints (cubicKernelBoundedShape K) e =
      cubicKernelOrderedEndpoints K.graph e := rfl

/-- Evaluation of one normalized edge kernel at the endpoints selected by
one bounded kernel table and one branch-coordinate vector. -/
def boundedKernelNormalizedEdgeFactor
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S) (e : Fin D.2.1.val)
    (q : C(S, ℂ) × ℂ) : ℂ :=
  boundedNormalizedPathKernel M hM q
    (x (boundedKernelOrderedEndpoints D e).1,
      x (boundedKernelOrderedEndpoints D e).2)

/-- Every endpoint-evaluated normalized edge factor is jointly analytic. -/
theorem boundedKernelNormalizedEdgeFactor_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S) (e : Fin D.2.1.val) :
    AnalyticAt ℂ (boundedKernelNormalizedEdgeFactor M hM D x e) (0, 0) := by
  let p : S × S :=
    (x (boundedKernelOrderedEndpoints D e).1,
      x (boundedKernelOrderedEndpoints D e).2)
  have heval : AnalyticAt ℂ
      (fun k : C(S × S, ℂ) ↦ k p)
      (boundedNormalizedPathKernel M hM (0, 0)) :=
    (ContinuousMap.evalCLM ℂ p : C(S × S, ℂ) →L[ℂ] ℂ).analyticAt _
  exact heval.comp_of_eq (boundedNormalizedPathKernel_analytic M hM) rfl

/-- Finite product of the pole-removed edge kernels of one bounded endpoint
table. -/
def boundedKernelNormalizedPathAmplitude
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S) (q : C(S, ℂ) × ℂ) : ℂ :=
  ∏ e : Fin D.2.1.val,
    boundedKernelNormalizedEdgeFactor M hM D x e q

/-- The finite normalized edge product is jointly analytic. -/
theorem boundedKernelNormalizedPathAmplitude_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S) :
    AnalyticAt ℂ (boundedKernelNormalizedPathAmplitude M hM D x) (0, 0) := by
  unfold boundedKernelNormalizedPathAmplitude
  exact (Finset.univ : Finset (Fin D.2.1.val)).analyticAt_fun_prod
    (fun e _ ↦ boundedKernelNormalizedEdgeFactor_analytic M hM D x e)

/-- On the critical axis, the normalized product is the product of the
frozen residue kernels over all bounded kernel edges. -/
@[simp] theorem boundedKernelNormalizedPathAmplitude_axis
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S) (g : C(S, ℂ)) :
    boundedKernelNormalizedPathAmplitude M hM D x (g, 0) =
      ∏ e : Fin D.2.1.val,
        BKPA_MPR.residueKernel M hM g
          (x (boundedKernelOrderedEndpoints D e).1,
            x (boundedKernelOrderedEndpoints D e).2) := by
  unfold boundedKernelNormalizedPathAmplitude
    boundedKernelNormalizedEdgeFactor
  simp only [boundedNormalizedPathKernel_axis]

/-- Base-point value of the joint bounded-kernel amplitude. -/
@[simp] theorem boundedKernelNormalizedPathAmplitude_base
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S) :
    boundedKernelNormalizedPathAmplitude M hM D x (0, 0) =
      ∏ e : Fin D.2.1.val,
        BKPA_MPR.residueKernel M hM 0
          (x (boundedKernelOrderedEndpoints D e).1,
            x (boundedKernelOrderedEndpoints D e).2) :=
  boundedKernelNormalizedPathAmplitude_axis M hM D x 0

/-- On the punctured germ, the normalized amplitude equals `X^e` times
the literal product of the `e` marked-path resolvent kernels. -/
theorem boundedKernelNormalizedPathAmplitude_eq_pow_mul_resolventProduct
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      boundedKernelNormalizedPathAmplitude M hM D x q =
        q.2 ^ D.2.1.val *
          ∏ e : Fin D.2.1.val,
            BKPA_MPR.pathResolventKernel M hM q
              (x (boundedKernelOrderedEndpoints D e).1,
                x (boundedKernelOrderedEndpoints D e).2) := by
  filter_upwards
    [boundedNormalizedPathKernel_eq_smul_pathResolventKernel M hM] with q hq
  intro hX
  have hedge (e : Fin D.2.1.val) :
      boundedKernelNormalizedEdgeFactor M hM D x e q =
        q.2 * BKPA_MPR.pathResolventKernel M hM q
          (x (boundedKernelOrderedEndpoints D e).1,
            x (boundedKernelOrderedEndpoints D e).2) := by
    have hfun := congrArg
      (fun k : C(S × S, ℂ) ↦
        k (x (boundedKernelOrderedEndpoints D e).1,
          x (boundedKernelOrderedEndpoints D e).2))
      (hq hX)
    simpa only [boundedKernelNormalizedEdgeFactor,
      ContinuousMap.smul_apply, smul_eq_mul] using hfun
  unfold boundedKernelNormalizedPathAmplitude
  simp_rw [hedge]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The zero-field slice of a bounded normalized kernel amplitude remains
analytic in the fold coordinate. -/
theorem boundedKernelAxisAmplitude_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S) :
    AnalyticAt ℂ
      (fun X : ℂ ↦
        boundedKernelNormalizedPathAmplitude M hM D x (0, X)) 0 := by
  have haxis : AnalyticAt ℂ
      (fun X : ℂ ↦ ((0 : C(S, ℂ)), X)) 0 :=
    analyticAt_const.prod analyticAt_id
  exact (boundedKernelNormalizedPathAmplitude_analytic M hM D x).comp_of_eq
    haxis rfl

/-- If a bounded kernel table has fewer than `3 * ell` edge labels, then
cubic normalization of its zero-field analytic amplitude has an explicit
extra factor `X`. -/
theorem boundedKernelAxisAmplitude_eq_X_mul_of_edgeCount_lt
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (D : BoundedKernelShape ell)
    (x : Fin D.1.val → S) (hedges : D.2.1.val < 3 * ell) :
    ∃ R : ℂ → ℂ,
      AnalyticAt ℂ R 0 ∧
      ∀ X,
        X ^ (3 * ell - D.2.1.val) *
            boundedKernelNormalizedPathAmplitude M hM D x (0, X) =
          X * R X := by
  exact AnalyticFiniteAmplitude.noncubic_normalizedAmplitude_eq_X_mul
    hedges
    (fun X ↦ boundedKernelNormalizedPathAmplitude M hM D x (0, X))
    (boundedKernelAxisAmplitude_analytic M hM D x)

/-- The edge coordinate of the normalized bounded shape is definitionally
the cardinality of the actual suppressed kernel-edge label type. -/
@[simp] theorem normalizedBoundedKernelShape_edgeCount
    {k ell : ℕ} (G : SimpleGraph (Fin k))
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card (Fin k) + ell) :
    (normalizedBoundedKernelShape G hconn hmin hell hs).2.1.val =
      Nat.card (KernelEdgeLabel G) := by
  rfl

/-- Hence the normalized bounded shape of an actual noncubic admissible
core has strictly fewer than `3 * ell` edge coordinates. -/
theorem normalizedBoundedKernelShape_edgeCount_lt_of_isNoncubic
    {k ell : ℕ} (hell : 0 < ell) {G : SimpleGraph (Fin k)}
    (hG : IsNoncubicAdmissibleAttachmentCore k ell G) :
    let hmin : ∀ v, 2 ≤ G.degree v :=
      minDegree_two_of_isTwoCore_univ hG.1.2.1
    let hs : G.edgeFinset.card = Fintype.card (Fin k) + ell := by
      simpa only [Fintype.card_fin] using hG.1.2.2
    (normalizedBoundedKernelShape G hG.1.1 hmin hell hs).2.1.val <
      3 * ell := by
  dsimp only
  rw [normalizedBoundedKernelShape_edgeCount]
  exact kernelEdgeLabel_card_lt_three_surplus_of_isNoncubic hell hG

end PerronWright.GraphCore
