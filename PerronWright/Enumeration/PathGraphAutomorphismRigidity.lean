import PerronWright.Enumeration.PathKernelSymmetry

/-!
# Rigidity of finite path-graph automorphisms

The only automorphisms of a nonempty standard finite path are the identity
and reversal.  The proof is intrinsic to `SimpleGraph.pathGraph`: first its
vertices of degree less than two are identified as the two endpoints, and
then adjacency and injectivity propagate the image of the first endpoint
along the whole path.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Reversal, regarded as a graph automorphism of the standard finite path. -/
def pathGraphRevIso (n : ℕ) :
    SimpleGraph.pathGraph n ≃g SimpleGraph.pathGraph n :=
  { Fin.revPerm with
    map_rel_iff' := by
      intro i j
      exact pathGraph_adj_rev n i j }

/-- The two endpoints are exactly the vertices of degree less than two in a
nonempty standard finite path.  For the one-vertex path they coincide. -/
theorem pathGraph_degree_lt_two_iff_eq_zero_or_last
    (n : ℕ) (i : Fin (n + 1)) :
    (SimpleGraph.pathGraph (n + 1)).degree i < 2 ↔
      i = 0 ∨ i = Fin.last n := by
  constructor
  · intro hdegree
    by_contra hend
    push Not at hend
    have hi0 : 0 < i.val := by
      by_contra h
      have hval : i.val = 0 := Nat.eq_zero_of_not_pos h
      have : i = 0 := by
        apply Fin.ext
        simpa using hval
      exact hend.1 this
    have hilast : i.val < n := by
      have hle : i.val ≤ n := by omega
      have hne : i.val ≠ n := by
        intro h
        apply hend.2
        apply Fin.ext
        simpa using h
      omega
    let p : Fin (n + 1) := ⟨i.val - 1, by omega⟩
    let q : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    have hpi : (SimpleGraph.pathGraph (n + 1)).Adj p i := by
      rw [SimpleGraph.pathGraph_adj]
      left
      simp only [p]
      omega
    have hiq : (SimpleGraph.pathGraph (n + 1)).Adj i q := by
      rw [SimpleGraph.pathGraph_adj]
      left
      simp only [q]
    have hpq : p ≠ q := by
      intro h
      have hval := congrArg Fin.val h
      simp only [p, q] at hval
      omega
    have hcard :
        1 < ((SimpleGraph.pathGraph (n + 1)).neighborFinset i).card := by
      apply Finset.one_lt_card_iff.mpr
      exact ⟨p, q,
        ((SimpleGraph.pathGraph (n + 1)).mem_neighborFinset i p).mpr hpi.symm,
        ((SimpleGraph.pathGraph (n + 1)).mem_neighborFinset i q).mpr hiq,
        hpq⟩
    rw [(SimpleGraph.pathGraph (n + 1)).card_neighborFinset_eq_degree] at hcard
    omega
  · rintro (rfl | rfl)
    · rw [← (SimpleGraph.pathGraph (n + 1)).card_neighborFinset_eq_degree]
      have hcard :
          ((SimpleGraph.pathGraph (n + 1)).neighborFinset 0).card ≤ 1 := by
        apply Finset.card_le_one_iff.mpr
        intro a b ha hb
        rw [SimpleGraph.mem_neighborFinset,
          SimpleGraph.pathGraph_adj] at ha hb
        apply Fin.ext
        simp only [Fin.val_zero] at ha hb
        omega
      omega
    · rw [← (SimpleGraph.pathGraph (n + 1)).card_neighborFinset_eq_degree]
      have hcard :
          ((SimpleGraph.pathGraph (n + 1)).neighborFinset
            (Fin.last n)).card ≤ 1 := by
        apply Finset.card_le_one_iff.mpr
        intro a b ha hb
        rw [SimpleGraph.mem_neighborFinset,
          SimpleGraph.pathGraph_adj] at ha hb
        apply Fin.ext
        simp only [Fin.val_last] at ha hb
        have ha_lt := a.isLt
        have hb_lt := b.isLt
        omega
      omega

/-- Once a path automorphism fixes the first endpoint, adjacency and
injectivity force it to fix every vertex. -/
theorem pathGraphIso_apply_eq_self_of_apply_zero_eq_zero
    {n : ℕ}
    (e : SimpleGraph.pathGraph (n + 1) ≃g
      SimpleGraph.pathGraph (n + 1))
    (hzero : e 0 = 0) :
    ∀ i : Fin (n + 1), e i = i := by
  have hvalue : ∀ (m : ℕ) (hm : m < n + 1),
      (e (⟨m, hm⟩ : Fin (n + 1))).val = m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hm
        by_cases hm0 : m = 0
        · subst m
          exact congrArg Fin.val hzero
        · let p : Fin (n + 1) := ⟨m - 1, by omega⟩
          let z : Fin (n + 1) := ⟨m, hm⟩
          change (e z).val = m
          have hp : (e p).val = m - 1 := by
            exact ih (m - 1) (by omega) p.isLt
          have hpz : (SimpleGraph.pathGraph (n + 1)).Adj p z := by
            rw [SimpleGraph.pathGraph_adj]
            left
            simp only [p, z]
            omega
          have hmap :
              (SimpleGraph.pathGraph (n + 1)).Adj (e p) (e z) :=
            e.map_rel_iff.mpr hpz
          rw [SimpleGraph.pathGraph_adj] at hmap
          rcases hmap with hforward | hbackward
          · calc
              (e z).val = (e p).val + 1 := hforward.symm
              _ = (m - 1) + 1 := congrArg (fun a : ℕ ↦ a + 1) hp
              _ = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)
          · have hbackward' : (e z).val + 1 = m - 1 := by
              calc
                (e z).val + 1 = (e p).val := hbackward
                _ = m - 1 := hp
            have hez_lt : (e z).val < m := by omega
            have hfixedValue : (e (e z)).val = (e z).val :=
              ih (e z).val hez_lt (e z).isLt
            have hfixed : e (e z) = e z := Fin.ext hfixedValue
            have hez : e z = z := e.injective hfixed
            have hezValue : (e z).val = m := by
              simpa only [z] using congrArg Fin.val hez
            exact hezValue
  intro i
  apply Fin.ext
  exact hvalue i.val i.isLt

/-- Pointwise rigidity of a nonempty finite path: an automorphism is either
the identity on every vertex or reversal on every vertex. -/
theorem pathGraphIso_apply_eq_self_or_rev
    {n : ℕ}
    (e : SimpleGraph.pathGraph (n + 1) ≃g
      SimpleGraph.pathGraph (n + 1)) :
    (∀ i : Fin (n + 1), e i = i) ∨
      (∀ i : Fin (n + 1), e i = i.rev) := by
  have hend : e 0 = 0 ∨ e 0 = Fin.last n := by
    apply (pathGraph_degree_lt_two_iff_eq_zero_or_last n (e 0)).mp
    rw [e.degree_eq]
    exact (pathGraph_degree_lt_two_iff_eq_zero_or_last n 0).mpr (Or.inl rfl)
  rcases hend with hzero | hlast
  · exact Or.inl (pathGraphIso_apply_eq_self_of_apply_zero_eq_zero e hzero)
  · right
    let er := e.trans (pathGraphRevIso (n + 1))
    have herZero : er 0 = 0 := by
      change (e 0).rev = 0
      rw [hlast, Fin.rev_last]
    have hfix := pathGraphIso_apply_eq_self_of_apply_zero_eq_zero er herZero
    intro i
    have hi := hfix i
    change (e i).rev = i at hi
    exact Fin.rev_eq_iff.mp hi

/-- Equivalence-valued form of path-graph automorphism rigidity. -/
theorem pathGraphIso_toEquiv_eq_refl_or_rev
    {n : ℕ}
    (e : SimpleGraph.pathGraph n ≃g SimpleGraph.pathGraph n) :
    e.toEquiv = Equiv.refl (Fin n) ∨
      e.toEquiv = Fin.revPerm := by
  cases n with
  | zero =>
      left
      exact Subsingleton.elim _ _
  | succ n =>
      rcases pathGraphIso_apply_eq_self_or_rev e with h | h
      · left
        apply Equiv.ext
        intro i
        apply Fin.ext
        exact congrArg Fin.val (h i)
      · right
        apply Equiv.ext
        intro i
        apply Fin.ext
        exact congrArg Fin.val (h i)

end PerronWright.GraphCore
