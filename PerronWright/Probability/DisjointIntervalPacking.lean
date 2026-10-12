import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Tactic.Linarith

/-! # Finite packing of genuine disjoint real intervals

Positive-length intervals in a bounded positive time horizon form a finite
family. The proof injects their left endpoints into a finite floor grid;
no local-finiteness or probability premise is assumed.
-/

open Set
noncomputable section

namespace PerronWright.DisjointIntervalPacking

theorem finite_of_length_lower_bound {I : Type*} (L R : I → ℝ) {a H : ℝ}
    (ha : 0 < a) (hL : ∀ i, 0 ≤ L i) (hR : ∀ i, R i ≤ H)
    (hlen : ∀ i, a ≤ R i - L i)
    (hdis : Pairwise (fun i j ↦ Disjoint (Ioo (L i) (R i)) (Ioo (L j) (R j)))) :
    Finite I := by
  let f : I → Fin (⌊H / a⌋₊ + 1) := fun i ↦
    ⟨⌊L i / a⌋₊, Nat.lt_succ_of_le (Nat.floor_le_floor
      (div_le_div_of_nonneg_right (by linarith [hlen i, hR i]) ha.le))⟩
  apply Finite.of_injective f
  intro i j hij
  have hf : ⌊L i / a⌋₊ = ⌊L j / a⌋₊ := congrArg Fin.val hij
  have hgap (k l : I) (hkl : ⌊L k / a⌋₊ = ⌊L l / a⌋₊) : L l < R k := by
    have hh := Nat.lt_floor_add_one (L l / a)
    rw [← hkl] at hh
    have hfloor := Nat.floor_le (div_nonneg (hL k) ha.le)
    have hh' : L l / a < (L k + a) / a := by
      rw [add_div, div_self ha.ne']
      exact hh.trans_le (by linarith)
    have hl : L l < L k + a := (div_lt_div_iff_of_pos_right ha).mp hh'
    exact hl.trans_le (by linarith [hlen k])
  by_contra hne
  have h1 := hgap i j hf
  have h2 := hgap j i hf.symm
  have hi : L i < R i := by linarith [hlen i]
  have hj : L j < R j := by linarith [hlen j]
  have hnon : max (L i) (L j) < min (R i) (R j) :=
    max_lt (lt_min hi h2) (lt_min h1 hj)
  exact (not_lt_of_ge (Ioo_disjoint_Ioo.mp (hdis hne))) hnon

/-- Only the retained indices need the bounded-horizon and length bounds. -/
theorem finite_set_of_length_lower_bound {I : Type*} (A : Set I) (L R : I → ℝ)
    {a H : ℝ} (ha : 0 < a) (hL : ∀ i ∈ A, 0 ≤ L i) (hR : ∀ i ∈ A, R i ≤ H)
    (hlen : ∀ i ∈ A, a ≤ R i - L i)
    (hdis : A.Pairwise (fun i j ↦ Disjoint (Ioo (L i) (R i)) (Ioo (L j) (R j)))) :
    A.Finite := by
  have : Finite A := finite_of_length_lower_bound (fun i : A ↦ L i) (fun i : A ↦ R i)
    ha (fun i ↦ hL i i.property) (fun i ↦ hR i i.property)
    (fun i ↦ hlen i i.property) (fun i j hij ↦ hdis i.property j.property
      (fun h ↦ hij (Subtype.ext h)))
  exact Set.toFinite A

end PerronWright.DisjointIntervalPacking
