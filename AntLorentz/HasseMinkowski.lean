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

section base_change

/-

## Base extension of quadratic forms

Unfortunately we don't seem to have this in the library, so we have
to develop it ourselves including making all the basic results which we'll need.
Note that we also make the theory in maximal generality (for example
we use semirings instead of rings, so the theory works for quadratic
forms over the naturals)

-/

-- Let `M` be an `R`-module
variable (R : Type) (M : Type) [CommRing R] [AddCommGroup M] [Module R M]

-- Let `A` be an `R`-algebra
variable (A : Type) [Semiring A] [Algebra R A]

open TensorProduct -- this line gives us access to ⊗ notation

-- Let's be lazy and assume 1/2 ∈ R
variable [Invertible (2 : R)]

-- Let V be a ℚ-vector space
variable {V : Type} [AddCommGroup V] [Module ℚ V]

-- Assume `V` is finite-dimensional (mathematical remark: is this definitely necessary??)
variable [FiniteDimensional ℚ V]

-- Let `F` be a quadratic form on V
variable (F : QuadraticForm ℚ V)

/-- A quadratic form over ℚ is everywhere locally isotropic if it has nontrivial
p-adic points for all p, and real points. -/
def QuadraticForm.EverywhereLocallyIsotropic :=
  (∀ (p : ℕ) [Fact (p.Prime)], (F.baseChange ℚ V ℚ_[p]).Isotropic) ∧
  (F.baseChange ℚ V ℝ).Isotropic

/-- The *statement* of the Hasse-Minkowski theorem. -/
def QuadraticForm.Hasse_Minkowski (F : QuadraticForm ℚ V) : Prop :=
  F.Isotropic ↔ F.EverywhereLocallyIsotropic

open QuadraticForm

-- a nontrivial project (probably publishable if someone does it)
theorem Hasse_Minkowski_proof : ∀ (F : QuadraticForm ℚ V), F.Hasse_Minkowski := sorry

-- some easier problems

variable (k W : Type) [Field k] [AddCommGroup W]

lemma Isotropic_of_zero_quadForm_dim_ge1 : [Module k W] (Q : QuadraticForm k W) (h₁ : Q=0) 
(h2 : Module.rank k W ≠ 0) : Q.Isotropic := sorry

-- (0) dim(V)=0 case

lemma anisotropic_of_quadForm_dim_zero [Module k W] (Q : QuadraticForm k W) 
(h : Module.rank k W = 0) : Q.Anisotropic := by
   intro (w : W)
   intro 
   rw [rank_zero_iff_forall_zero] at h
   exact h w
   #check anisotropic_of_quadform_dim_zero

theorem Hasse_Minkowski0 (hV : Module.rank ℚ V = 0) : ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := by
   intro F
   rw [Hasse_Minkowski]
   constructor 
   · contrapose
     intro 
     rw [QuadraticForm.Isotropic]
     simp
     apply anisotropic_of_quadform_dim_zero _ _ F hV
   · contrapose
     intro 
     rw [QuadraticForm.EverywhereLocallyIsotropic]
     push_neg
     intro 
     simp 
     apply anisotropic_of_quadform_dim_zero
     rw [← base_change_module_rank_preserved, hV] 


-- (1) dim(V)=1 case

lemma anisotropic_of_nonzero_quadForm_dim_1 : [Module k W] (Q : QuadraticForm k W) 
(h₁ : Q ≠ 0) (h₂ : Module.rank k W = 1) : Q.Anisotropic := sorry

theorem Hasse_Minkowski1 (hV : Module.rank V = 1) :
    ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := sorry


lemma HM_of_Equivalent {Q S : QuadraticForm ℚ V} (h : Q.Equivalent S) :
    Q.Hasse_Minkowski ↔ S.Hasse_Minkowski := by
  simp only [Hasse_Minkowski, Isotropic, EverywhereLocallyIsotropic] at *
  simp [anisotropic_iff _ _ h]
  rw [anisotropic_iff _ _ (baseChange.Equivalent ℚ V ℝ _ _ h)]
  simp_rw [anisotropic_iff _ _ (baseChange.Equivalent ℚ V ℚ_[_] _ _ h)]


-- (2) dim(V)=2 case
theorem Hasse_Minkowski2 (hV : Module.rank V = 2) :
    ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := sorry

-- All of these should be possible, although you'll quickly learn that formalisation of
-- mathematics is more annoying than you might think...