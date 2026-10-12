import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Genuine countable extension of consistent finite real laws

The transition kernels are actual regular conditional distributions of
the given finite laws. Ionescu-Tulcea then constructs a genuine measure
on real sequences. Exact finite-prefix marginals are proved by induction;
existence of a projective limit is not an assumed interface. The next
Gaussian module applies this construction to literal Brownian finite
Gaussian laws and discharges the consistency condition there.
-/

open MeasureTheory ProbabilityTheory Preorder Filter Topology
open scoped BigOperators Classical ProbabilityTheory

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.CountableRealProjectiveLaw

abbrev Prefix (n : ℕ) := (i : Finset.Iic n) → ℝ

def splitPrefix (n : ℕ) (x : Prefix (n + 1)) : Prefix n × ℝ :=
  (frestrictLe₂ (π := fun _ : ℕ ↦ ℝ) n.le_succ x,x ⟨n + 1,Finset.mem_Iic.mpr le_rfl⟩)

def joinPrefix (n : ℕ) (p : Prefix n × ℝ) : Prefix (n + 1) :=
  fun i ↦ if hi : i.val ≤ n then p.1 ⟨i.val,Finset.mem_Iic.mpr hi⟩ else p.2

theorem measurable_splitPrefix (n : ℕ) : Measurable (splitPrefix n) := by
  exact (measurable_frestrictLe₂ (X := fun _ : ℕ ↦ ℝ) n.le_succ).prodMk (measurable_pi_apply _)

theorem measurable_joinPrefix (n : ℕ) : Measurable (joinPrefix n) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i.val ≤ n
  · simp only [joinPrefix,dif_pos hi]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [joinPrefix,dif_neg hi]
    exact measurable_snd

theorem joinPrefix_splitPrefix (n : ℕ) (x : Prefix (n + 1)) :
    joinPrefix n (splitPrefix n x) = x := by
  funext i
  by_cases hi : i.val ≤ n
  · simp only [joinPrefix,dif_pos hi,splitPrefix,frestrictLe₂_apply]
  · have hv : i.val = n + 1 := by have := Finset.mem_Iic.mp i.property; omega
    simp only [joinPrefix,dif_neg hi,splitPrefix]
    exact congrArg x (Subtype.ext hv.symm)

theorem joinPrefix_sample (n : ℕ) (x : ℕ → ℝ) :
    joinPrefix n (frestrictLe (π := fun _ : ℕ ↦ ℝ) n x,x (n + 1)) =
      frestrictLe (π := fun _ : ℕ ↦ ℝ) (n + 1) x := by
  funext i
  by_cases hi : i.val ≤ n
  · simp only [joinPrefix,dif_pos hi,frestrictLe_apply]
  · have hv : i.val = n + 1 := by have := Finset.mem_Iic.mp i.property; omega
    simp [joinPrefix,frestrictLe_apply,hv]

variable (μ : (n : ℕ) → Measure (Prefix n)) [∀ n, IsProbabilityMeasure (μ n)]

/-- Actual conditional distribution of the next coordinate under its
finite Gaussian/source law, given the literal preceding coordinates. -/
def transition (n : ℕ) : Kernel (Prefix n) ℝ :=
  condDistrib (fun x : Prefix (n + 1) ↦ x ⟨n + 1,Finset.mem_Iic.mpr le_rfl⟩)
    (frestrictLe₂ (π := fun _ : ℕ ↦ ℝ) n.le_succ) (μ (n + 1))

instance (n : ℕ) : IsMarkovKernel (transition μ n) := by
  unfold transition
  infer_instance

def initialLaw : Measure ℝ := (μ 0).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ ℝ))

instance : IsProbabilityMeasure (initialLaw μ) :=
  Measure.isProbabilityMeasure_map (MeasurableEquiv.measurable _).aemeasurable

/-- A genuine normalized law on real sequences, constructed by
Ionescu-Tulcea using the actual source conditional distributions. -/
def law : Measure (ℕ → ℝ) := Kernel.trajMeasure (X := fun _ : ℕ ↦ ℝ) (initialLaw μ) (transition μ)

instance : IsProbabilityMeasure (law μ) := by
  unfold law
  infer_instance

theorem law_prefix_zero : (law μ).map (frestrictLe (π := fun _ : ℕ ↦ ℝ) 0) = μ 0 := by
  unfold law Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_frestrictLe (X := fun _ : ℕ ↦ ℝ) 0),Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self,Measure.id_comp]
  exact (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ ℝ)).map_symm_map

variable (hμ : ∀ (a b : ℕ) (hab : a ≤ b),
  (μ b).map (frestrictLe₂ (π := fun _ : ℕ ↦ ℝ) hab) = μ a)

include hμ

theorem prefix_compProd_transition (n : ℕ) :
    (μ n) ⊗ₘ transition μ n = (μ (n + 1)).map (splitPrefix n) := by
  rw [← hμ n (n + 1) n.le_succ]
  exact compProd_map_condDistrib (measurable_pi_apply _).aemeasurable

/-- Every actual finite-prefix source law is exactly the corresponding
marginal of the constructed normalized infinite sequence law. -/
theorem law_prefix (n : ℕ) : (law μ).map (frestrictLe (π := fun _ : ℕ ↦ ℝ) n) = μ n := by
  induction n with
  | zero => exact law_prefix_zero μ
  | succ n ih =>
    have hj : (fun x : ℕ → ℝ ↦ joinPrefix n
        (frestrictLe (π := fun _ : ℕ ↦ ℝ) n x,x (n + 1))) =
        frestrictLe (π := fun _ : ℕ ↦ ℝ) (n + 1) := funext (joinPrefix_sample n)
    calc
      _ = ((law μ).map (fun x : ℕ → ℝ ↦
          (frestrictLe (π := fun _ : ℕ ↦ ℝ) n x,x (n + 1)))).map (joinPrefix n) := by
        rw [Measure.map_map (measurable_joinPrefix n)
          ((measurable_frestrictLe (X := fun _ : ℕ ↦ ℝ) n).prodMk (measurable_pi_apply (n + 1)))]
        exact congrArg (fun f ↦ (law μ).map f) hj.symm
      _ = ((law μ).map (frestrictLe (π := fun _ : ℕ ↦ ℝ) n) ⊗ₘ transition μ n).map (joinPrefix n) := by
        unfold law
        rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure]
      _ = ((μ n) ⊗ₘ transition μ n).map (joinPrefix n) := by rw [ih]
      _ = ((μ (n + 1)).map (splitPrefix n)).map (joinPrefix n) := by
        rw [prefix_compProd_transition μ hμ n]
      _ = μ (n + 1) := by
        rw [Measure.map_map (measurable_joinPrefix n) (measurable_splitPrefix n)]
        have he : joinPrefix n ∘ splitPrefix n = id := funext (joinPrefix_splitPrefix n)
        rw [he,Measure.map_id]

end PerronWright.CountableRealProjectiveLaw
