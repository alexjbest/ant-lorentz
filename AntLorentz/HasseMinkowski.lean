import Mathlib.Tactic -- lots of tactics
import Mathlib.LinearAlgebra.QuadraticForm.Basic -- quadratic forms
import Mathlib.LinearAlgebra.TensorProduct -- tensor products (for base change)
import Mathlib.LinearAlgebra.Dimension -- rank of modules
import Mathlib.NumberTheory.Padics.PadicNumbers
import AntLorentz.Diagonalize

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

def BilinForm.baseChange (F : BilinForm R M) : BilinForm A (A ⊗[R] M) :=
  --let L := BilinForm.toLinHom
  sorry

/-- If `F : QuadraticForm R M` and `A` is an `R`-algebra then `F.baseChange A`
is the associated quadratic form on `M ⊗[R] A` -/
def QuadraticForm.baseChange (F : QuadraticForm R M) : QuadraticForm A (A ⊗[R] M) := by
  let B : BilinForm R M := associatedHom R F
  let B' : BilinForm A (A ⊗[R] M) := B.baseChange R M A -- base change
  exact B'.toQuadraticForm


lemma QuadraticForm.baseChange.Equivalent (Q S : QuadraticForm R M) (h : Q.Equivalent S) :
    (baseChange R M A Q).Equivalent (baseChange R M A S) := sorry

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

-- (0) dim(V)=0 case

variable (k W : Type) [Field k] [AddCommMonoid W]

theorem quadform_zero_dim_eq_zero [Module k W] (Q : QuadraticForm k W) (h : Module.rank W = 0) : Q = 0 := by sorry

theorem Hasse_Minkowski0 (hV : Module.rank V = 0) :
    ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := by
    sorry
    -- idea: no non-zero elements of V:
    -- rank_zero_iff_forall_zero -- says that every element in a rank 0 module is 0
--------------------------------------------------------------------






-- (1) dim(V)=1 case
theorem Hasse_Minkowski1 (hV : Module.rank V = 1) :
    ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := sorry



/--
⊗


-/
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
-- testing a push