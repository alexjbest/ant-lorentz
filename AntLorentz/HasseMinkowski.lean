import Mathlib.Tactic -- lots of tactics
import Mathlib.LinearAlgebra.QuadraticForm.Basic -- quadratic forms
import Mathlib.LinearAlgebra.TensorProduct -- tensor products (for base change)
import Mathlib.LinearAlgebra.Dimension -- rank of modules
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace QuadraticForm

variable [Semiring R] [AddCommMonoid M] [Module R M]

abbrev Isotropic (Q : QuadraticForm R M) : Prop := ¬ Anisotropic (Q)

end QuadraticForm

/-!

# Hasse-Minkowski experiments

Mathematical experiments around the local-global principle.

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

-- temporary NOT CORRECT YET
lemma base_change_module_rank_preserved : Module.rank R M = Module.rank A (A ⊗[R] M) :=by sorry

/-- If `F : QuadraticForm R M` and `A` is an `R`-algebra then `F.baseChange A`
is the associated quadratic form on `M ⊗[R] A` -/
def QuadraticForm.baseChange (F : QuadraticForm R M) : QuadraticForm A (A ⊗[R] M) := by
  let B : BilinForm R M := associatedHom R F
  let B' : BilinForm A (A ⊗[R] M) := B.baseChange R M A -- base change
  exact B'.toQuadraticForm

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
def Hasse_Minkowski (F : QuadraticForm ℚ V) : Prop :=
  F.Isotropic ↔ F.EverywhereLocallyIsotropic

-- a nontrivial project (probably publishable if someone does it)
theorem Hasse_Minkowski_proof : ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := sorry

-- some easier problems

-- (0) dim(V)=0 case

variable (k W : Type) [Field k] [AddCommGroup W]

lemma anisotropic_of_quadform_dim_zero [Module k W] (Q : QuadraticForm k W) (h : Module.rank k W = 0) : Q.Anisotropic := by
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

lemma zero_of_quadform_dim_zero [Module k W] (Q : QuadraticForm k W) (h : Module.rank W = 0) : Q = 0 := by sorry
  -- rank_zero_iff_forall_zero 


   
    





-- (1) dim(V)=1 case
theorem Hasse_Minkowski1 (hV : Module.rank V = 1) :
    ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := sorry



-- (2) dim(V)=2 case
theorem Hasse_Minkowski2 (hV : Module.rank V = 2) :
    ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := sorry

-- All of these should be possible, although you'll quickly learn that formalisation of
-- mathematics is more annoying than you might think...
-- testing a push