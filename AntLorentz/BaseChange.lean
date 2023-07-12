--import Mathlib
import Mathlib.Tactic -- lots of tactics
import Mathlib.LinearAlgebra.QuadraticForm.Basic -- quadratic forms
import Mathlib.LinearAlgebra.TensorProduct -- tensor products (for base change)
import Mathlib.LinearAlgebra.Dimension -- rank of modules
import Mathlib.NumberTheory.Padics.PadicNumbers

/-

## Base extension of quadratic forms

Unfortunately we don't seem to have this in the library, so we have
to develop it ourselves including making all the basic results which we'll need.
Note that we also make the theory in maximal generality (for example
we use semirings instead of rings, so the theory works for quadratic
forms over the naturals)

-/

section base_change

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring A] [Algebra R A]

open QuadraticForm

-- Let's be lazy and assume 1/2 ∈ R
variable [Invertible (2 : R)]



-- I want to do base change for quadratic forms.
-- How much of the below is re-inventing the wheel?

-- M and N are R-modules and A is an R-algebra and T is an A-module
variable (R A M N T : Type) [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  [AddCommGroup T] [Module A T]
  -- and I want to regard T as an R-module too, in the obvious way
  [Module R T] [IsScalarTower R A T]

open TensorProduct -- for notation

def LinearMap.baseChangeLeft (f : M →ₗ[R] T) : A ⊗[R] M →ₗ[A] T where
  toFun := TensorProduct.lift ({
    toFun := fun a ↦ a • f
    map_add' := sorry
    map_smul' := sorry
  } : A →ₗ[R] M →ₗ[R] T)
  map_add' := sorry
  map_smul' := sorry

def algebraMap' : R →ₗ[R] A where
  toFun := algebraMap R A
  map_add' := sorry
  map_smul' := sorry

def TensorProduct.rid' : A ⊗[R] R ≃ₗ[A] A where
  toLinearMap := LinearMap.baseChangeLeft R A R A (algebraMap' R A)
  invFun := fun a ↦ a ⊗ₜ 1
  left_inv := sorry
  right_inv := sorry

variable {R M}

def BilinForm.baseChange (F : BilinForm R M) : BilinForm A (A ⊗[R] M) := by
  let L := BilinForm.toLinHom R F
  let L' := L.baseChange A
  refine LinearMap.toBilin ?_
  refine LinearMap.comp ?_ L'
  apply LinearMap.baseChangeLeft
  refine LinearMap.comp ?_ (LinearMap.baseChangeHom R A _ _)
  apply LinearMap.restrictScalars R (S := A)
  refine LinearMap.llcomp A _ _ _ (?_ : A ⊗[R] R →ₗ[A] A)
  exact (TensorProduct.rid' R A).toLinearMap

def QuadraticForm.baseChange [Invertible (2 : R)] (F : QuadraticForm R M) : QuadraticForm A (A ⊗[R] M) := by
  let B : BilinForm R M := associatedHom R F
  let B' : BilinForm A (A ⊗[R] M) := B.baseChange A
  exact B'.toQuadraticForm

lemma BilinForm.baseChange_eval (F : BilinForm R M) (a b : A) (m n : M) :
    F.baseChange A (a ⊗ₜ m) (b ⊗ₜ n) = a * b * algebraMap R A (F m n) := by
  unfold baseChange
  dsimp
  unfold bilin
  dsimp
  sorry

/-- If F_A is the base change of the quadratic form F to A, then F_A(a ⊗ m) = a^2*F(m). -/
lemma QuadraticForm.baseChange_eval (F : QuadraticForm R M) (m : M) [Invertible (2 : R)] :
  F.baseChange A (a ⊗ₜ m) = a * a * algebraMap R A (F m) := by
  rw [baseChange, BilinForm.toQuadraticForm_apply, BilinForm.baseChange_eval, associated_apply,
      ← two_smul R m, QuadraticForm.map_smul]
  congr
  rw [mul_assoc, invOf_mul_eq_iff_eq_mul_left]
  ring