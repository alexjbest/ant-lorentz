import Mathlib.Tactic -- lots of tactics
import Mathlib.LinearAlgebra.QuadraticForm.Basic -- quadratic forms
import Mathlib.LinearAlgebra.TensorProduct -- tensor products (for base change)
import Mathlib.LinearAlgebra.Dimension -- rank of modules
import Mathlib.NumberTheory.Padics.PadicNumbers
import AntLorentz.Diagonalize
import AntLorentz.BaseChange

namespace QuadraticForm

variable [Semiring R] [AddCommMonoid M] [Module R M]

abbrev Isotropic (Q : QuadraticForm R M) : Prop := ¬ Anisotropic (Q)

end QuadraticForm

/-!

# Hasse-Minkowski experiments

Mathematical experiments around the local-global principle.


Thoughts:
- Proof splits into several cases 0, 1, 2, 3, 4, ≥ 5, should do this separately
- also should prove the obvious direction first!
- Should decide what generality, probably just Q at first, but maybe think of other number fields / function 
  fields where possible.
- there are many proofs out there, https://mathoverflow.net/questions/384352/a-list-of-proofs-of-the-hasse-minkowski-theorem
  has a summary
- need fact that any quadratic form is diagonalizable, this is more or less in mathlib
- Kevin recommends cours d'arithmetique, looks nice
- many proofs use dirichlets theorem on primes in arithmetic progressions, this is not in mathlib but has been formalized before
  (at least by Carneiro pssibly others)
- Cassels - NOTE ON QUADRATIC FORMS OVER THE RATIONAL FIELD
  claims only hard case is 4, others do not require deep results
  and that the n = 4 case can be done with minkowski's convex body theorem, this is in mathlib
  he also uses "Gauss's theorem on the existence of forms in genera"
- n = 0 and 1 cases should be "trivial"
- n = 2 needs that a number is a global square iff it is an everywhre local square
- n = 3 case works by diagonalizing and maybe some QR / modular stuff
- https://etd.ohiolink.edu/apexprod/rws_etd/send_file/send?accession=osu1338317481&disposition=inline seems an ok reference for 2,3
-/



-- Let V be a ℚ-vector space
variable {V : Type _} [AddCommGroup V] [Module ℚ V]
variable {V₂ : Type _} [AddCommGroup V₂] [Module ℚ V₂]

-- Assume `V` is finite-dimensional (mathematical remark: is this definitely necessary??)
variable [FiniteDimensional ℚ V]

-- Let `F` be a quadratic form on V
variable (F : QuadraticForm ℚ V)

namespace QuadraticForm

/-- A quadratic form over ℚ is everywhere locally isotropic if it has nontrivial
p-adic points for all p, and real points. -/
def EverywhereLocallyIsotropic :=
  (∀ (p : ℕ) [Fact (p.Prime)], (F.baseChange ℚ_[p]).Isotropic) ∧
  (F.baseChange ℝ).Isotropic

/-- The *statement* of the Hasse-Minkowski theorem. -/
def HasseMinkowski (F : QuadraticForm ℚ V) : Prop :=
  F.Isotropic ↔ F.EverywhereLocallyIsotropic

theorem HasseMinkowski_easy_way [Module.Finite ℚ V] (F : QuadraticForm ℚ V) (h : F.Isotropic) :
    F.EverywhereLocallyIsotropic := by
  rw [EverywhereLocallyIsotropic]
  simp only [Isotropic, Anisotropic, not_forall, exists_prop] at h ⊢ 
  push_neg at h
  obtain ⟨x, hx, hne⟩ := h
  constructor
  . intro p hp
    use (1 ⊗ₜ x)
    simp [hx]
    sorry
  . use (1 ⊗ₜ x)
    simp [hx]
    sorry


-- some easier problems

variable (k W : Type) [Field k] [AddCommGroup W]

-- The quadratic form 0 on a vector space of dimension greater than zero is isotropic. 
lemma Isotropic_of_zero_quadForm_dim_ge1 [Module k W] (Q : QuadraticForm k W) (h₁ : Q = 0) 
    (h₂ : Module.rank k W ≠ 0) : Q.Isotropic := by
  rw [QuadraticForm.Isotropic, QuadraticForm.Anisotropic]
  have h : ∃ (w : W), w ≠ 0 := by
    simpa only [ne_eq, rank_zero_iff_forall_zero, not_forall] using h₂
  obtain ⟨w, hw⟩ := h 
  have : Q w = 0 := by 
    rw [h₁]
    simp only [zero_apply]
  tauto

-- (0) dim(V)=0 case

-- Every quadratic form on a zero-dimensional vector space is anisotropic. 
lemma anisotropic_of_quadForm_dim_zero [Module k W] (Q : QuadraticForm k W) 
    (h : Module.rank k W = 0) : Q.Anisotropic := by
  intro (w : W) _
  rw [rank_zero_iff_forall_zero] at h
  exact h w

theorem HasseMinkowski0 (hV : Module.rank ℚ V = 0) : ∀ (F : QuadraticForm ℚ V), HasseMinkowski F := by
  intro F
  rw [HasseMinkowski]
  constructor 
  · contrapose
    intro 
    rw [QuadraticForm.Isotropic]
    simp only [not_not]
    apply anisotropic_of_quadForm_dim_zero _ _ F hV
  · contrapose
    intro 
    rw [QuadraticForm.EverywhereLocallyIsotropic]
    push_neg
    intro 
    simp only [not_not] 
    apply anisotropic_of_quadForm_dim_zero
    rw [← base_change_module_rank_preserved, hV] 


-- (1) dim(V)=1 case

-- Every non-zero quadratic form on a vector space of dimension 1 is anisotropic. 
lemma anisotropic_of_nonzero_quadForm_dim_1 [Module k W] (Q : QuadraticForm k W) 
    (h₁ : Q ≠ 0) (h₂ : Module.rank k W = 1) : Q.Anisotropic := sorry

theorem HasseMinkowski1 (hV : Module.rank V = 1) :
    ∀ (F : QuadraticForm ℚ V), HasseMinkowski F := sorry


lemma HasseMinkowski_of_Equivalent {Q : QuadraticForm ℚ V} {S : QuadraticForm ℚ V₂}
    (h : Q.Equivalent S) :
    Q.HasseMinkowski ↔ S.HasseMinkowski := by
  simp only [HasseMinkowski, Isotropic, EverywhereLocallyIsotropic] at *
  simp only [anisotropic_iff _ _ h]
  rw [anisotropic_iff _ _ (baseChange.Equivalent ℝ _ _ h)]
  conv in (Anisotropic (baseChange _ Q)) =>
    rw [anisotropic_iff _ _ (baseChange.Equivalent (R := ℚ) ℚ_[p] _ _ h)]


theorem HasseMinkowski_of_degenerate (Q : QuadraticForm ℚ V) (hQ : ¬ (associated (R₁ := ℚ) Q).Nondegenerate) :
  HasseMinkowski Q := by
  have degenQ := Q.nondegenerate_of_anisotropic.mt hQ
  have degenR := (nondegenerate_of_anisotropic _).mt (baseChange_of_degenerate (A := ℝ) _ hQ)
  simp only [HasseMinkowski, Isotropic, degenQ, not_false_eq_true,
    EverywhereLocallyIsotropic, degenR, and_true, true_iff]
  intro p hp
  exact (nondegenerate_of_anisotropic (Q.baseChange ℚ_[p])).mt (baseChange_of_degenerate (A := ℚ_[p]) _ hQ)

open FinVec
theorem ex (Q : QuadraticForm ℚ V) (h : FiniteDimensional.finrank ℚ V = 2) :
  HasseMinkowski Q := by
  by_cases hQ : (associated (R₁ := ℚ) Q).Nondegenerate
  . obtain ⟨w, hw1, hw0, hEQ⟩ := equivalent_weightedSumSquares_units_of_nondegenerate'' Q (by simp [h]) h.symm hQ -- TODO norm_num no work
    have := HasseMinkowski_of_Equivalent (V := V) hEQ
    rw [this]
    rw [HasseMinkowski, Isotropic, EverywhereLocallyIsotropic, Isotropic]
    -- rw [anisotropic_iff Q (weightedSumSquares ℚ w) hEQ]
    -- intro x
    simp at *
    -- rw [show x = ![x 0, x 1] from (etaExpand_eq x).symm]
    -- -- simp at *
    -- simp [hw1]
    sorry
  . exact HasseMinkowski_of_degenerate Q hQ -- TODO exact? fails
    
  -- (2) dim(V)=2 case

lemma rat_sq_iff_local_sq (x : ℚ) : IsSquare x ↔ (∀ (p : ℕ) [Fact (p.Prime)], IsSquare (x : ℚ_[p])) ∧ IsSquare (x : ℝ) := by
  sorry 

theorem HasseMinkowski2 (hV : Module.rank V = 2) :
    ∀ (F : QuadraticForm ℚ V), HasseMinkowski F := sorry

#lint -- TODO should ignore unfinished

-- a nontrivial project (probably publishable if someone does it)
theorem HasseMinkowski_proof [Module.Finite ℚ V] (F : QuadraticForm ℚ V) : F.HasseMinkowski := by
  match h : FiniteDimensional.finrank ℚ V with
  | 0       => sorry
  | 1       => sorry
  | 2       => sorry
  | 3       => sorry
  | 4       => sorry
  | (n + 5) => sorry