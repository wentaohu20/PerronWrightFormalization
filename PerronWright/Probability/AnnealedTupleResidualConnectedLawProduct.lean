import PerronWright.Probability.ConnectedTypeLaw
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Exact products of the normalized connected type laws

The product law is literally `Measure.pi` of the already constructed
`ConnectedTypeLaw.law` measures.  Its joint density, its normalization, and
its coupled-observable expectation identity are proved from the finite
product of the graph/type weights; independence is not a separate premise.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedTupleResidualConnectedLawProduct

open AnnealedGraph ConnectedTypeLaw

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

abbrev TupleState {q : ℕ} (S : Type*) (k : Fin q → ℕ) :=
  (i : Fin q) → ConnectedTypeLaw.State S (k i)

/-- Literal unweighted product type-and-graph measure for all components. -/
abbrev baseLaw (M : CompactBJRModel S) {q : ℕ} (k : Fin q → ℕ) :
    Measure (TupleState S k) :=
  Measure.pi (fun i ↦ (typeLaw M (k i)).prod Measure.count)

def productWeight (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) (p : TupleState S k) : ℝ :=
  ∏ i, ConnectedTypeLaw.weight M g (k i) (r i) (p i)

def productNormalizer (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) : ℝ := ∏ i, M.fieldConnectedWeight g (k i) (r i)

theorem productWeight_nonneg (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) (p : TupleState S k) : 0 ≤ productWeight M g k r p :=
  Finset.prod_nonneg (fun i _ ↦ ConnectedTypeLaw.weight_nonneg M g (k i) (r i) (p i))

theorem productWeight_measurable (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) : Measurable (productWeight M g k r) := by
  apply Finset.measurable_prod
  intro i _
  exact (ConnectedTypeLaw.weight_measurable M g (k i) (r i)).comp (measurable_pi_apply i)

theorem productWeight_integrable (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) : Integrable (productWeight M g k r) (baseLaw M k) :=
  Integrable.fintype_prod_dep (fun i ↦ ConnectedTypeLaw.weight_integrable M g (k i) (r i))

/-- Exact Fubini normalization before division: the total product weight
is the product of the literal connected enumerators. -/
theorem integral_productWeight (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) :
    (∫ p, productWeight M g k r p ∂baseLaw M k) = productNormalizer M g k r := by
  unfold productWeight productNormalizer baseLaw
  rw [integral_fintype_prod_eq_prod]
  simp only [ConnectedTypeLaw.integral_weight]

theorem productNormalizer_pos (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) (hC : ∀ i, 0 < M.fieldConnectedWeight g (k i) (r i)) :
    0 < productNormalizer M g k r :=
  Finset.prod_pos (fun i _ ↦ hC i)

/-- The genuine independent product of the normalized connected type laws. -/
def law (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ} (k r : Fin q → ℕ)
    (hC : ∀ i, 0 < M.fieldConnectedWeight g (k i) (r i)) : Measure (TupleState S k) :=
  Measure.pi (fun i ↦ ConnectedTypeLaw.law M g (k i) (r i) (hC i))

instance law_isProbability (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) (hC : ∀ i, 0 < M.fieldConnectedWeight g (k i) (r i)) :
    IsProbabilityMeasure (law M g k r hC) := by
  unfold law
  infer_instance

def normalizedWeight (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) (p : TupleState S k) : ℝ :=
  ∏ i, ConnectedTypeLaw.weight M g (k i) (r i) (p i) /
    M.fieldConnectedWeight g (k i) (r i)

theorem normalizedWeight_eq (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) (p : TupleState S k) :
    normalizedWeight M g k r p = productWeight M g k r p / productNormalizer M g k r := by
  unfold normalizedWeight productWeight productNormalizer
  rw [Finset.prod_div_distrib]

theorem normalizedWeight_nonneg (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) (hC : ∀ i, 0 < M.fieldConnectedWeight g (k i) (r i))
    (p : TupleState S k) : 0 ≤ normalizedWeight M g k r p :=
  Finset.prod_nonneg (fun i _ ↦ div_nonneg
    (ConnectedTypeLaw.weight_nonneg M g (k i) (r i) (p i)) (hC i).le)

theorem normalizedWeight_measurable (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) : Measurable (normalizedWeight M g k r) := by
  apply Finset.measurable_prod
  intro i _
  exact ((ConnectedTypeLaw.weight_measurable M g (k i) (r i)).div_const _).comp
    (measurable_pi_apply i)

/-- The literal product law has the normalized product density on the
literal product of unweighted type-and-graph measures.  The rectangle
calculation proves this identity, rather than postulating independence. -/
theorem law_eq_withDensity (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) (hC : ∀ i, 0 < M.fieldConnectedWeight g (k i) (r i)) :
    law M g k r hC = (baseLaw M k).withDensity
      (fun p ↦ ENNReal.ofReal (normalizedWeight M g k r p)) := by
  unfold law
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    Measure.restrict_pi_pi]
  have hI : Integrable (normalizedWeight M g k r)
      (Measure.pi (fun i ↦ ((typeLaw M (k i)).prod Measure.count).restrict (s i))) :=
    Integrable.fintype_prod_dep (fun i ↦
      ((ConnectedTypeLaw.weight_integrable M g (k i) (r i)).div_const _).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall (normalizedWeight_nonneg M g k r hC))]
  unfold normalizedWeight
  rw [integral_fintype_prod_eq_prod
    (fun i (p : ConnectedTypeLaw.State S (k i)) ↦
      ConnectedTypeLaw.weight M g (k i) (r i) p / M.fieldConnectedWeight g (k i) (r i))]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ integral_nonneg
    (fun p ↦ div_nonneg (ConnectedTypeLaw.weight_nonneg M g (k i) (r i) p) (hC i).le))]
  apply Finset.prod_congr rfl
  intro i _
  rw [ConnectedTypeLaw.law,withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal
    (((ConnectedTypeLaw.weight_integrable M g (k i) (r i)).div_const _).restrict)
    (Filter.Eventually.of_forall (fun p ↦ div_nonneg
      (ConnectedTypeLaw.weight_nonneg M g (k i) (r i) p) (hC i).le))

/-- Exact expectation of every (possibly coupled) observable under the
genuine product of the connected laws.  The denominator is proved to be
the product partition function, not an independently supplied normalizer. -/
theorem expectation_eq_weighted_integral (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ}
    (k r : Fin q → ℕ) (hC : ∀ i, 0 < M.fieldConnectedWeight g (k i) (r i))
    (F : TupleState S k → ℝ) :
    (∫ p, F p ∂law M g k r hC) =
      (∫ p, productWeight M g k r p * F p ∂baseLaw M k) / productNormalizer M g k r := by
  rw [law_eq_withDensity]
  have hd : Measurable (fun p : TupleState S k ↦
      ENNReal.ofReal (normalizedWeight M g k r p)) :=
    ENNReal.measurable_ofReal.comp (normalizedWeight_measurable M g k r)
  rw [integral_withDensity_eq_integral_toReal_smul
    hd
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (normalizedWeight_nonneg M g k r hC _),smul_eq_mul]
  simp_rw [normalizedWeight_eq,div_mul_eq_mul_div]
  rw [integral_div]

/-- Multiplicative form used to turn a literal weighted tuple integral into
the product-connected-law residual expectation. -/
theorem weighted_integral_eq_normalizer_mul_expectation
    (M : CompactBJRModel S) (g : C(S, ℝ)) {q : ℕ} (k r : Fin q → ℕ)
    (hC : ∀ i, 0 < M.fieldConnectedWeight g (k i) (r i)) (F : TupleState S k → ℝ) :
    (∫ p, productWeight M g k r p * F p ∂baseLaw M k) =
      productNormalizer M g k r * ∫ p, F p ∂law M g k r hC := by
  rw [expectation_eq_weighted_integral]
  field_simp [(productNormalizer_pos M g k r hC).ne']

/-- The ordinary `t`-weighted connected graph density from the paper. -/
def ordinaryWeight (M : CompactBJRModel S) (t : ℝ) (k r : ℕ)
    (p : ConnectedTypeLaw.State S k) : ℝ :=
  if ConnectedTypeLaw.Eligible r p.2 then M.graphWeightIntegrand t p.2 p.1 else 0

/-- Pointwise counterpart of the previously proved ordinary/field enumerator
transformation.  The surplus power depends only on the eligible graph size. -/
theorem ordinaryWeight_scalarField (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t)
    (k r : ℕ) (p : ConnectedTypeLaw.State S k) :
    ordinaryWeight M t k r p =
      t ^ ((r : ℤ)-1) * ConnectedTypeLaw.weight M (M.scalarField t) k r p := by
  by_cases he : ConnectedTypeLaw.Eligible r p.2
  · simp only [ordinaryWeight,ConnectedTypeLaw.weight,if_pos he]
    have hk : 0 < k := by
      obtain ⟨v⟩ := he.1.nonempty
      exact Nat.zero_lt_of_lt v.isLt
    have hp : t ^ (k+r-1) = t ^ ((r : ℤ)-1) * t ^ k := by
      rw [← zpow_natCast t (k+r-1),← zpow_natCast t k,← zpow_add₀ ht.ne']
      congr 1
      omega
    have hcross := M.graphWeightIntegrand_field_cross_identity t ht p.2 p.1
    rw [he.2,hp] at hcross
    apply mul_left_cancel₀ (pow_ne_zero k ht.ne')
    calc
      _ = (t ^ ((r : ℤ)-1) * t ^ k) *
          M.fieldGraphWeightIntegrand (M.scalarField t) p.2 p.1 := hcross
      _ = _ := by ring
  · simp only [ordinaryWeight,ConnectedTypeLaw.weight,if_neg he,mul_zero]

def productOrdinaryWeight (M : CompactBJRModel S) (t : ℝ) {q : ℕ}
    (k r : Fin q → ℕ) (p : TupleState S k) : ℝ := ∏ i, ordinaryWeight M t (k i) (r i) (p i)

def ordinaryNormalizer (M : CompactBJRModel S) (t : ℝ) {q : ℕ}
    (k r : Fin q → ℕ) : ℝ := ∏ i, M.connectedWeight t (k i) (r i)

def surplusScale (t : ℝ) {q : ℕ} (r : Fin q → ℕ) : ℝ := ∏ i, t ^ ((r i : ℤ)-1)

theorem surplusScale_pos {q : ℕ} (t : ℝ) (ht : 0 < t) (r : Fin q → ℕ) :
    0 < surplusScale t r := Finset.prod_pos (fun _ _ ↦ zpow_pos ht _)

theorem productOrdinaryWeight_scalarField (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t)
    {q : ℕ} (k r : Fin q → ℕ) (p : TupleState S k) :
    productOrdinaryWeight M t k r p = surplusScale t r * productWeight M (M.scalarField t) k r p := by
  unfold productOrdinaryWeight surplusScale productWeight
  simp_rw [ordinaryWeight_scalarField M t ht]
  rw [Finset.prod_mul_distrib]

theorem ordinaryNormalizer_scalarField (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t)
    {q : ℕ} (k r : Fin q → ℕ) :
    ordinaryNormalizer M t k r = surplusScale t r * productNormalizer M (M.scalarField t) k r := by
  unfold ordinaryNormalizer surplusScale productNormalizer
  simp_rw [M.connectedWeight_scalarField t ht]
  rw [Finset.prod_mul_distrib]

theorem ordinaryNormalizer_pos (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t)
    {q : ℕ} (k r : Fin q → ℕ)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField t) (k i) (r i)) :
    0 < ordinaryNormalizer M t k r := by
  rw [ordinaryNormalizer_scalarField M t ht]
  exact mul_pos (surplusScale_pos t ht r) (productNormalizer_pos M _ k r hC)

/-- The literal ordinary-`t` weighted tuple integral is a genuine expectation
under the product of `ConnectedTypeLaw` at the exact scalar field `g_t`.
Thus the `t` dependence is derived from the existing exact weight transform. -/
theorem ordinary_weighted_integral_eq_normalizer_mul_expectation
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t) {q : ℕ} (k r : Fin q → ℕ)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField t) (k i) (r i))
    (F : TupleState S k → ℝ) :
    (∫ p, productOrdinaryWeight M t k r p * F p ∂baseLaw M k) =
      ordinaryNormalizer M t k r * ∫ p, F p ∂law M (M.scalarField t) k r hC := by
  simp_rw [productOrdinaryWeight_scalarField M t ht]
  rw [show (fun p : TupleState S k ↦
      (surplusScale t r * productWeight M (M.scalarField t) k r p) * F p) =
      (fun p ↦ surplusScale t r * (productWeight M (M.scalarField t) k r p * F p)) by
    funext p; ring]
  rw [integral_const_mul,weighted_integral_eq_normalizer_mul_expectation M _ k r hC F,
    ordinaryNormalizer_scalarField M t ht]
  ring

end PerronWright.AnnealedTupleResidualConnectedLawProduct
