import Mathlib.Tactic -- lots of tactics
import Mathlib.LinearAlgebra.QuadraticForm.Basic -- quadratic forms
import Mathlib.LinearAlgebra.TensorProduct -- tensor products (for base change)
import Mathlib.LinearAlgebra.Dimension -- rank of modules
import Mathlib.NumberTheory.Padics.PadicNumbers
import AntLorentz.BaseChange


variable [Semiring R] [AddCommMonoid M] [Module R M]

namespace QuadraticForm
abbrev Isotropic (Q : QuadraticForm R M) : Prop := ¬ Anisotropic (Q)
end QuadraticForm

/-!

# Hasse-Minkowski experiments

Mathematical experiments around the local-global principle.

-/


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
  (∀ (p : ℕ) [Fact (p.Prime)], (F.baseChange ℚ ℚ_[p] V).Isotropic) ∧
  (F.baseChange ℚ ℝ V).Isotropic

/-- The *statement* of the Hasse-Minkowski theorem. -/
def Hasse_Minkowski (F : QuadraticForm ℚ V) : Prop :=
  F.Isotropic ↔ F.EverywhereLocallyIsotropic

-- a nontrivial project (probably publishable if someone does it)
theorem Hasse_Minkowski_proof : ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := sorry

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



-- (2) dim(V)=2 case
theorem Hasse_Minkowski2 (hV : Module.rank V = 2) :
    ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := sorry

-- All of these should be possible, although you'll quickly learn that formalisation of
-- mathematics is more annoying than you might think...
-- testing a push