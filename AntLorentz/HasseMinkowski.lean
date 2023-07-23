import Mathlib.Tactic -- lots of tactics
import Mathlib.LinearAlgebra.QuadraticForm.Basic -- quadratic forms
import Mathlib.LinearAlgebra.TensorProduct -- tensor products (for base change)
import Mathlib.LinearAlgebra.Dimension -- rank of modules
import Mathlib.NumberTheory.Padics.PadicNumbers
import AntLorentz.Diagonalize
import AntLorentz.BaseChange
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.Squarefree

--import Lean
--open Lean Elab Tactic

--elab "tada" : tactic => do
--  let gs ← getUnsolvedGoals
--  if gs.isEmpty then
--    logInfo "Goals accomplished 🎉"
--  else
--    Term.reportUnsolvedGoals gs
--    throwAbortTactic


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


-- General dimension

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

-- the easy direction
theorem HasseMinkowski_global_to_local (F : QuadraticForm ℚ V) (h : F.Isotropic) :
    F.EverywhereLocallyIsotropic := by
  rw [EverywhereLocallyIsotropic]
  simp only [Isotropic, Anisotropic, not_forall, exists_prop] at h ⊢ 
  push_neg at h
  obtain ⟨x, hx, hne⟩ := h
  constructor
  . intro p hp
    use (1 ⊗ₜ x)
    simp only [baseChange_eval, mul_one, hx, _root_.map_zero, mul_zero, true_and]
    sorry
  . use (1 ⊗ₜ x)
    simp only [baseChange_eval, mul_one, hx, _root_.map_zero, mul_zero, true_and]
    sorry


-- using equivalent forms
lemma HasseMinkowski_of_Equivalent {Q : QuadraticForm ℚ V} {S : QuadraticForm ℚ V₂}
    (h : Q.Equivalent S) :
    Q.HasseMinkowski ↔ S.HasseMinkowski := by
  simp only [HasseMinkowski, Isotropic, EverywhereLocallyIsotropic] at *
  simp only [anisotropic_iff _ _ h]
  rw [anisotropic_iff _ _ (baseChange.Equivalent ℝ _ _ h)]
  conv in (Anisotropic (baseChange _ Q)) =>
    rw [anisotropic_iff _ _ (baseChange.Equivalent (R := ℚ) ℚ_[p] _ _ h)]


-- (0) dim(V)=0 case

-- Every quadratic form on a zero-dimensional vector space is anisotropic. 
lemma anisotropic_of_quadForm_dim_zero [Module k W] (Q : QuadraticForm k W) 
    (h : Module.rank k W = 0) : Q.Anisotropic := by
  intro (w : W) _
  rw [rank_zero_iff_forall_zero] at h
  exact h w

-- Proof of Hasse Minkowski in dimension 0.
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


-- General lemma for all cases of dimension at least 1:

-- The quadratic form 0 on a vector space of dimension greater than zero is isotropic. 
lemma isotropic_of_zero_quadForm_dim_ge1 [Module k W] (Q : QuadraticForm k W) (h₁ : Q = 0)
    (h₂ : Module.rank k W ≠ 0) : Q.Isotropic := by
  rw [QuadraticForm.Isotropic]
  rw [QuadraticForm.Anisotropic]
  have h: ∃ (w : W), w ≠ 0 := by
    simpa only [ne_eq, rank_zero_iff_forall_zero, not_forall] using h₂
  obtain ⟨w, hw⟩ := h 
  have : Q w = 0 := by 
    rw [h₁]
    simp only [zero_apply]
  tauto


-- (1) dim(V)=1 case

-- Every non-zero quadratic form on a vector space of dimension 1 is anisotropic. 
lemma anisotropic_of_nonzero_quadForm_dim_1 [Module k W] (Q : QuadraticForm k W) 
    (h₁ : Q ≠ 0) (h₂ : Module.rank k W = 1) : Q.Anisotropic := by
  rw [QuadraticForm.Anisotropic]
  have h: ∃ (w : W), Q w ≠ 0 := by sorry -- using h₁
  obtain ⟨w, hw⟩ := h   
  have h': ∀ (v : W) (h'': v ≠ 0), Q v ≠ 0 := by sorry -- using h₂: v = a*w, Q v = a^2*Q w ≠ 0
  intro 
  contrapose
  apply h'     

-- Proof of Hasse Minkowski in dimension 1. 
theorem HasseMinkowski1 (hV : Module.rank V = 1) :
    ∀ (F : QuadraticForm ℚ V), HasseMinkowski F := sorry


-- Some general lemmas for all cases of dimension at least 2:

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

/- not needed any more
lemma rat_sq_iff_local_sq (x : ℚ) : IsSquare x ↔ (∀ (p : ℕ) [Fact (p.Prime)], IsSquare (x : ℚ_[p])) ∧ IsSquare (x : ℝ) := by
  sorry 
-/

open Int

-- TODO: make this more general
theorem weightedSumSquares_basechange_anisotropic_iff {a : ℕ} {p : ℕ} (w : Fin a → ℤ) [hp : Fact p.Prime] : ((weightedSumSquares ℚ w).baseChange ℚ_[p]).Anisotropic ↔ (weightedSumSquares ℚ_[p] (fun i => (w i : ℚ_[p]))).Anisotropic := by
  sorry

theorem HasseMinkowski2 (hV : FiniteDimensional.finrank ℚ V = 2) (F : QuadraticForm ℚ V) : HasseMinkowski F := by
  by_cases hF : (associated (R₁ := ℚ) F).Nondegenerate
  · have hV0 : 0 < FiniteDimensional.finrank ℚ V := by rw [hV]; norm_num
    obtain ⟨w, hw1, hw0, hEF⟩ := equivalent_weightedSumSquares_units_of_nondegenerate'' F hV0 hV.symm hF
    rw [HasseMinkowski_of_Equivalent (V := V) hEF, HasseMinkowski]
    constructor
    · intro h
      exact HasseMinkowski_global_to_local _ h
    · intro hl
      by_cases hw : w ⟨1, (by norm_num)⟩ = -1
      · rw [Isotropic, Anisotropic]
        push_neg
        sorry -- use (1,1)
      · exfalso
        rw [EverywhereLocallyIsotropic, Isotropic, Anisotropic] at hl
        let a := w 1
        have ha : Squarefree a := hw0 1
        rcases hl with ⟨hlf, hli⟩
        cases lt_or_gt_of_ne (Squarefree.ne_zero ha) with
        | inl hneg => {
            let n := a.natAbs
            have ngt1 : n > 1 := by sorry -- combine hw with hneg
            rw [← squarefree_natAbs] at ha
            let f := n.factors
            by_cases hf : f = []
            · have : n = 1 := by 
                sorry
              sorry -- now we have a = -1 after all
            · have hp := List.exists_mem_of_ne_nil f hf
              rcases hp with ⟨p, hp⟩
              have hp2 := Nat.prime_of_mem_factors hp 
              have : Fact (p.Prime) := by exact { out := hp2 }
              specialize hlf p
              rw [Isotropic, weightedSumSquares_basechange_anisotropic_iff w, Anisotropic] at hlf
              push_neg at hlf
              rcases hlf with ⟨x, ⟨ hx1, hx2⟩ ⟩
              simp only [weightedSumSquares_apply, smul_eq_mul, Fin.sum_univ_two] at hx1 
              by_cases hx3 : x 0 = 0
              · have : x = 0 := by
                  simp?
                  sorry
                exact hx2 this
              · have : (w 1 : ℚ_[p]) * (x 1 * x 1) = -(x 0 * x 0) := by sorry -- use hw1 and hx1
                sorry -- contradiction with square-freeness and the choice of p
          }
        | inr hpos => {
            sorry -- get contradiction with hli
        }
  · exact HasseMinkowski_of_degenerate F hF


--#lint -- TODO should ignore unfinished

-- a nontrivial project (probably publishable if someone does it)
lemma HasseMinkowski_proof_finite [Module.Finite ℚ V] (F : QuadraticForm ℚ V) : F.HasseMinkowski := by
  match h : FiniteDimensional.finrank ℚ V with
  | 0       => sorry
  | 1       => sorry
  | 2       => exact HasseMinkowski2 h F
  | 3       => sorry
  | 4       => sorry
  | (n + 5) => sorry

lemma HasseMinkowski_proof_infinite (h : ¬ Module.Finite ℚ V) (F : QuadraticForm ℚ V) : F.HasseMinkowski := by
  /- Kevin's idea (if I understood correctly):
     Suppose that V is of dimension >= 3 and F is everywhere locally
     soluble.
     1. Let W₀ ⊆ V be of dimension 3. Then F restricted to W₀ is
     locally soluble at all but finitely many places.
     Indeed, choose a basis such that F
     is given by an integral quadratic polynomial on W₀. It has
     solutions modulo every prime by Chevalley-Warning. For
     primes not dividing the discriminant, these solutions can
     be lifted to local solutions.
     2. For the finitely many remaining places p, choose solutions
     v_p in ℚ_p ⊗ V. They are finite sums of pure sensors
     v_p = y_{p,1} ⊗ v_{p,1} + ... + y_{p,n} ⊗ v_{p,n}.
     3. Let W be the span of W₀ ∪ {v_{p,i} : p, i}, which is
     finite-dimensional. Then F restricted to W is everywhere locally
     soluble, hence by finite-dimensional Hasse-Minkowski
     we get that F has a solution in W ⊂ V. 
  -/
  sorry

theorem HasseMinkowski_proof (F : QuadraticForm ℚ V) : F.HasseMinkowski := by
  cases em (Module.Finite ℚ V) with
  | inl finite   => exact HasseMinkowski_proof_finite F
  | inr infinite => exact HasseMinkowski_proof_infinite infinite F
