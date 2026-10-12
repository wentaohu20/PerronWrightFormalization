import PerronWright.Analysis.PerronSpectrum

open MeasureTheory Module
noncomputable section
namespace PerronWright

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

abbrev fixedComplement (T : E →L[ℝ] E) :=
  (Module.End.eigenspace T.toLinearMap 1)ᗮ

def fixedComplementOperator (T : E →L[ℝ] E) (hT : T.IsSymmetric) :
    fixedComplement T →L[ℝ] fixedComplement T :=
  T.restrict (hT.invariant_orthogonalComplement_eigenspace 1)

omit [CompleteSpace E] in
theorem fixedComplementOperator_norm_le (T : E →L[ℝ] E) (hT : T.IsSymmetric) :
    ‖fixedComplementOperator T hT‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact T.le_opNorm v

omit [CompleteSpace E] in
theorem fixedComplementOperator_no_one (T : E →L[ℝ] E) (hT : T.IsSymmetric) :
    ¬ Module.End.HasEigenvalue (fixedComplementOperator T hT).toLinearMap 1 := by
  intro hev
  obtain ⟨v, hv, hvne⟩ := hev.exists_hasEigenvector
  have heq : T (v : E) = (v : E) := by
    have := congrArg (fun w : fixedComplement T => (w : E))
      (Module.End.mem_eigenspace_iff.mp hv)
    simpa [fixedComplementOperator] using this
  have hvfix : (v : E) ∈ Module.End.eigenspace T.toLinearMap 1 :=
    Module.End.mem_eigenspace_iff.mpr (by simpa using heq)
  have hzero : (v : E) = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (v.property _ hvfix)
  exact hvne (Subtype.ext hzero)

omit [CompleteSpace E] in
theorem fixedComplementOperator_no_neg_one (T : E →L[ℝ] E) (hT : T.IsSymmetric)
    (hneg : ¬ Module.End.HasEigenvalue T.toLinearMap (-1)) :
    ¬ Module.End.HasEigenvalue (fixedComplementOperator T hT).toLinearMap (-1) := by
  intro hev
  obtain ⟨v, hv, hvne⟩ := hev.exists_hasEigenvector
  apply hneg
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := (v : E))
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    have := congrArg (fun w : fixedComplement T => (w : E))
      (Module.End.mem_eigenspace_iff.mp hv)
    simpa [fixedComplementOperator] using this
  · intro hz
    exact hvne (Subtype.ext hz)

theorem fixedComplementOperator_norm_lt_one (T : E →L[ℝ] E)
    (hT : T.IsSymmetric) (hcompact : IsCompactOperator T) (hnorm : ‖T‖ = 1)
    (hneg : ¬ Module.End.HasEigenvalue T.toLinearMap (-1)) :
    ‖fixedComplementOperator T hT‖ < 1 := by
  have hle : ‖fixedComplementOperator T hT‖ ≤ 1 :=
    hnorm ▸ fixedComplementOperator_norm_le T hT
  apply lt_of_le_of_ne hle
  intro heq
  have hc : IsCompactOperator (fixedComplementOperator T hT) :=
    hcompact.restrict' (hT.invariant_orthogonalComplement_eigenspace 1)
  have hs : (fixedComplementOperator T hT).IsSymmetric :=
    hT.restrict_invariant (hT.invariant_orthogonalComplement_eigenspace 1)
  rcases eigenvalue_one_or_neg_one (fixedComplementOperator T hT) hc hs heq with hp | hn
  · exact fixedComplementOperator_no_one T hT hp
  · exact fixedComplementOperator_no_neg_one T hT hneg hn

theorem fixedComplementOperator_one_sub_isUnit (T : E →L[ℝ] E)
    (hT : T.IsSymmetric) (hcompact : IsCompactOperator T) (hnorm : ‖T‖ = 1)
    (hneg : ¬ Module.End.HasEigenvalue T.toLinearMap (-1)) :
    IsUnit (1 - fixedComplementOperator T hT) :=
  isUnit_one_sub_of_norm_lt_one (x := fixedComplementOperator T hT)
    (fixedComplementOperator_norm_lt_one T hT hcompact hnorm hneg)

omit [CompleteSpace E] in
theorem eigenvector_mem_fixedComplement (T : E →L[ℝ] E) (hT : T.IsSymmetric)
    (lam : ℝ) (hlam : lam ≠ 1) (v : E) (hv : T v = lam • v) :
    v ∈ fixedComplement T := by
  intro w hw
  have hwfix : T w = w := by
    simpa using Module.End.mem_eigenspace_iff.mp hw
  have hsym := hT w v
  change inner ℝ (T w) v = inner ℝ w (T v) at hsym
  rw [hwfix, hv, real_inner_smul_right] at hsym
  have hz : (lam - 1) * inner ℝ w v = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hlam)

omit [CompleteSpace E] in
theorem eigenvalue_norm_le_fixedComplementOperator (T : E →L[ℝ] E)
    (hT : T.IsSymmetric) (lam : ℝ) (hlam : lam ≠ 1) (v : E)
    (hvne : v ≠ 0) (hv : T v = lam • v) :
    |lam| ≤ ‖fixedComplementOperator T hT‖ := by
  let w : fixedComplement T := ⟨v, eigenvector_mem_fixedComplement T hT lam hlam v hv⟩
  have hbound := (fixedComplementOperator T hT).le_opNorm w
  have hnorm : ‖(fixedComplementOperator T hT) w‖ = |lam| * ‖v‖ := by
    change ‖T v‖ = |lam| * ‖v‖
    rw [hv, norm_smul, Real.norm_eq_abs]
  rw [hnorm] at hbound
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hvne)).mp hbound

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem complex_eigenvalue_norm_le_complement (M : CompactBJRModel S)
    (B : M.B1Witness) (f : C(S, ℂ)) (hfne : f ≠ 0) (lam : ℂ)
    (hlam : lam ≠ 1) (hf : M.kernel.complexAction M.mu f = lam • f) :
    ‖lam‖ ≤ ‖fixedComplementOperator B.operator B.isSymmetric‖ := by
  have him := complex_eigenvalue_im_eq_zero M B f hfne lam hf
  have hreal : (lam.re : ℂ) = lam := by
    apply Complex.ext <;> simp [him]
  have hre : lam.re ≠ 1 := by
    intro heq
    apply hlam
    rw [← hreal, heq]
    simp
  have hnorm : ‖lam‖ = |lam.re| := by
    calc
      ‖lam‖ = ‖(lam.re : ℂ)‖ := congrArg norm hreal.symm
      _ = |lam.re| := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  let a := ContinuousMap.toLp 2 M.mu ℝ (realMap f)
  let b := ContinuousMap.toLp 2 M.mu ℝ (imagMap f)
  have ha : B.operator a = lam.re • a := by
    dsimp [a]
    rw [B.associated.intertwines, realMap_eigen_equation M f lam hf,
      him, zero_smul, sub_zero, map_smul]
  have hb : B.operator b = lam.re • b := by
    dsimp [b]
    rw [B.associated.intertwines, imagMap_eigen_equation M f lam hf,
      him, zero_smul, zero_add, map_smul]
  by_cases ha0 : a = 0
  · have hbne : b ≠ 0 := by
      intro hb0
      have har : realMap f = 0 := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) M.mu
        (by simpa [a] using ha0)
      have hbi : imagMap f = 0 := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) M.mu
        (by simpa [b] using hb0)
      apply hfne
      ext x
      apply Complex.ext
      · exact congrArg (fun g : C(S, ℝ) => g x) har
      · exact congrArg (fun g : C(S, ℝ) => g x) hbi
    exact eigenvalue_norm_le_fixedComplementOperator B.operator B.isSymmetric lam.re hre b hbne hb
  · exact eigenvalue_norm_le_fixedComplementOperator B.operator B.isSymmetric lam.re hre a ha0 ha

theorem compactBJR_complex_spectral_gap (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (B : M.B1Witness) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ∀ lam ∈ spectrum ℂ (M.kernel.complexActionCLM M.mu), lam ≠ 1 → ‖lam‖ ≤ q := by
  refine ⟨‖fixedComplementOperator B.operator B.isSymmetric‖, ?_, ?_, ?_⟩
  · exact norm_nonneg (fixedComplementOperator B.operator B.isSymmetric)
  · exact fixedComplementOperator_norm_lt_one B.operator B.isSymmetric B.isCompact B.norm_eq_one
      (l2_not_hasEigenvalue_neg_one M hM B)
  · intro lam hs hne1
    by_cases hzero : lam = 0
    · simpa only [hzero, norm_zero] using
        norm_nonneg (fixedComplementOperator B.operator B.isSymmetric)
    · have hcompact := M.kernel.isCompactOperator_complexActionCLM M.mu
      have hev := (hcompact.hasEigenvalue_iff_mem_spectrum hzero).mpr hs
      obtain ⟨f, hf, hfne⟩ := hev.exists_hasEigenvector
      exact complex_eigenvalue_norm_le_complement M B f hfne lam hne1
        (Module.End.mem_eigenspace_iff.mp hf)

theorem exists_complex_spectral_gap (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ∀ lam ∈ spectrum ℂ (M.kernel.complexActionCLM M.mu), lam ≠ 1 → ‖lam‖ ≤ q := by
  obtain ⟨B⟩ := hM.b1
  exact compactBJR_complex_spectral_gap M hM B




end PerronWright

