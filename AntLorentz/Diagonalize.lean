import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.Algebra.Squarefree
import Mathlib.Data.Fin.Tuple.Reflection

-- THESE things are probably not needed as equivalent_weightedSumSquares_units_of_nondegenerate' is in the library
-- variable {V : Type u} {K : Type v} [Field K] [AddCommGroup V] [Module K V]

-- variable [FiniteDimensional K V]
-- open FiniteDimensional

-- namespace BilinForm
-- -- TODO port expand_exists
-- noncomputable
-- def IsSymm.orthogonalBasis [Invertible (2 : K)] {B : BilinForm K V} (hB₂ : B.IsSymm) :
--     Basis (Fin (finrank K V)) K V := Classical.choose <| B.exists_orthogonal_basis hB₂
-- lemma orthogonalBasis.iIsOrtho [Invertible (2 : K)] {B : BilinForm K V} (hB₂ : B.IsSymm) : 
--     B.iIsOrtho hB₂.orthogonalBasis := 
--   Classical.choose_spec <| B.exists_orthogonal_basis hB₂
-- end BilinForm

-- namespace QuadraticForm
-- variable
--     {R₁ M} [Field R₁] [AddCommGroup M] [Module R₁ M] [FiniteDimensional R₁ M] [Invertible (2 : R₁)]
-- noncomputable
-- def orthogonalBasis (Q : QuadraticForm R₁ M) := (Q.associated_isSymm R₁).orthogonalBasis
-- lemma orthogonal_basis.iIsOrtho (Q : QuadraticForm R₁ M) :
--     (associated (R₁ := R₁) Q).iIsOrtho (orthogonalBasis Q) := 
--   BilinForm.orthogonalBasis.iIsOrtho (Q.associated_isSymm R₁)
-- end QuadraticForm
namespace QuadraticForm

variable {ι R K M M₁ M₂ M₃ V : Type _}

namespace QuadraticForm

variable [Semiring R]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃]

instance {Q : QuadraticForm R M} {S : QuadraticForm R M₂} : LinearEquivClass (Isometry Q S) R M M₂ where
  coe := fun a => a
  inv := fun a => a.symm
  left_inv := fun a => a.toEquiv.left_inv
  right_inv := fun a => a.toEquiv.right_inv
  coe_injective' := by
    intro e f h _
    simpa using h
  map_add := fun f a b => map_add f.toLinearMap a b
  map_smulₛₗ := fun f a b => map_smulₛₗ f.toLinearMap a b

end QuadraticForm

variable {R : Type _} {M : Type _} [Field R] [AddCommGroup M]
  [Module R M] [FiniteDimensional R M] [Invertible (2 : R)] (Q : QuadraticForm R M) 

open QuadraticForm
-- lemma exists_weighted (Q : QuadraticForm R M) :
--   ∃ (ι : Type) (ins : Fintype ι) (v : ι → M), Set.range (Q : M → R) = Set.range (weightedSumSquares _ fun (i : ι) => Q (v i)) :=
-- by
--   let a := Q.orthogonalBasis
--   use Fin (finrank R M)
--   constructor
--   use a -- TODO auto refactoring, let a, use a
--   rw [← basisRepr_eq_of_iIsOrtho]
--   simp
--   sorry
--   exact orthogonal_basis.iIsOrtho Q

lemma anisotropic_of_Equivalent
    [AddCommGroup M₂] [Module R M₂] (Q : QuadraticForm R M) (S : QuadraticForm R M₂) (h : Q.Equivalent S) :
    Q.Anisotropic → S.Anisotropic := by
  rcases h with ⟨val⟩
  intro h
  simp only [Anisotropic] at *
  intro x hx
  specialize h (val.symm x)
  simp only [Isometry.map_app, AddEquivClass.map_eq_zero_iff] at h  
  specialize h hx
  simpa using h


lemma anisotropic_iff [AddCommGroup M₂] [Module R M₂] (Q : QuadraticForm R M) (S : QuadraticForm R M₂) (h : Q.Equivalent S) :
    Q.Anisotropic ↔ S.Anisotropic := 
⟨anisotropic_of_Equivalent Q S h, anisotropic_of_Equivalent S Q h.symm⟩
  


-- lemma exists_weighted₂ (hf : finrank R M = 2) (Q : QuadraticForm R M) :
--     ∃ a b : R, Q.Anisotropic ↔ (weightedSumSquares R ![a, b]).Anisotropic := by
--   simp [Anisotropic]

section
variable [AddCommGroup V] [Module ℚ V]

instance : Invertible (2 : ℚ) := ⟨2⁻¹, by norm_num, by norm_num⟩

-- theorem equivalent_weightedSumSquares_units_of_nondegenerate'' (Q : QuadraticForm ℚ V) (h : 0 < FiniteDimensional.finrank ℚ V)
--     (hQ : (associated (R₁ := ℚ) Q).Nondegenerate) :
--     ∃ (w : Fin a → ℤ)
--       (hw1 : w ⟨0, h⟩ = 1)
--       (hw0 : ∀ i, Squarefree (w i)),
--       Equivalent Q (weightedSumSquares ℚ w) := by
--     sorry

-- TODO simpa only not clickable

theorem equivalent_weightedSumSquares_units_of_nondegenerate'' (Q : QuadraticForm ℚ V) (h : 0 < FiniteDimensional.finrank ℚ V)
    (ha : a = FiniteDimensional.finrank ℚ V)
    (hQ : (associated (R₁ := ℚ) Q).Nondegenerate) :
    ∃ (w : Fin a → ℤ)
      (hw1 : w ⟨0, ha ▸ h⟩ = 1)
      (hw0 : ∀ i, Squarefree (w i)),
      Equivalent Q (weightedSumSquares ℚ w) := by
    sorry