--import Mathlib
import Mathlib.Tactic -- lots of tactics
import Mathlib.LinearAlgebra.QuadraticForm.Isometry -- quadratic forms
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
    map_add' := fun x y => add_smul x y f
    map_smul' := by
      intro r x
      simp only [smul_assoc, RingHom.id_apply]
  } : A →ₗ[R] M →ₗ[R] T)
  map_add' := map_add _
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply]
    --show (r • x) • f =  _
    sorry

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

def boop : A →ₗ[A] R →ₗ[R] A :=
  LinearMap.mk₂' A R (fun a r => r • a) (fun m₁ m₂ n => smul_add n m₁ m₂) (fun c m n => smul_comm n c m)
  (fun m n₁ n₂ => add_smul n₁ n₂ m) (fun c m n => smul_assoc c n m)

def BilinForm.baseChange (F : BilinForm R M) : BilinForm A (A ⊗[R] M) := by
  let L := BilinForm.toLinHom R F
  let L' := L.baseChange A
  refine LinearMap.toBilin ?_
  refine LinearMap.comp ?_ L'
  apply LinearMap.baseChangeLeft
  refine LinearMap.comp ?_ (LinearMap.baseChangeHom R A _ _)
  apply LinearMap.restrictScalars R (S := A)
  refine LinearMap.llcomp A _ _ _ (?_ : A ⊗[R] R →ₗ[A] A)
  apply TensorProduct.AlgebraTensorModule.lift
  exact boop _
  --exact (TensorProduct.rid' R A).toLinearMap

def QuadraticForm.baseChange [Invertible (2 : R)] (F : QuadraticForm R M) : QuadraticForm A (A ⊗[R] M) := by
  let B : BilinForm R M := associatedHom R F
  let B' : BilinForm A (A ⊗[R] M) := B.baseChange A
  exact B'.toQuadraticForm

@[simp]
lemma BilinForm.baseChange_eval (F : BilinForm R M) (a b : A) (m n : M) :
    F.baseChange A (a ⊗ₜ m) (b ⊗ₜ n) = a * b * algebraMap R A (F m n) := by
  unfold baseChange
  dsimp
  unfold bilin
  dsimp
  sorry


/-- If F_A is the base change of the quadratic form F to A, then F_A(a ⊗ m) = a^2*F(m). -/
@[simp]
lemma QuadraticForm.baseChange_eval (F : QuadraticForm R M) (m : M) [Invertible (2 : R)] :
  F.baseChange A (a ⊗ₜ m) = a * a * algebraMap R A (F m) := by
  rw [baseChange, BilinForm.toQuadraticForm_apply, BilinForm.baseChange_eval, associated_apply,
      ← two_smul R m, QuadraticForm.map_smul]
  congr
  rw [mul_assoc, invOf_mul_eq_iff_eq_mul_left]
  ring

lemma BilinForm.baseChangeSymm (F : BilinForm R M) (hF : F.IsSymm) :
  (F.baseChange A).IsSymm := by
  simp [IsSymm] at *
  intros x y
  induction x using TensorProduct.induction_on generalizing y
  . simp
  . rename_i t z
    induction y using TensorProduct.induction_on
    . simp
    . rename_i e r
      simp [hF, mul_comm t]
    . rename_i e r he hr 
      simp [*]
  . rename_i t z ht hz
    induction y using TensorProduct.induction_on
    . simp
    . rename_i e r
      simp [*]
    . rename_i e r _ _
      simp only [add_right, add_left, *]
      ac_rfl

@[simp]
lemma QuadraticForm.baseChange_associatedHom (F : QuadraticForm R M) [Invertible (2 : R)] [Invertible (2 : A)] :
  associatedHom R (F.baseChange A) = (associatedHom R F).baseChange A := by
  simp only [baseChange]
  apply associated_left_inverse
  apply BilinForm.baseChangeSymm
  exact associated_isSymm R F

section associated
variable [CommRing R₁] [AddCommGroup M] [Module R₁ M]

variable [Invertible (2 : R₁)]
variable {A : Type _} [CommRing A] [Algebra R₁ A] [Invertible (2 : A)]
variable (F : QuadraticForm R₁ M)
  
@[simp]
lemma QuadraticForm.baseChange_associated (F : QuadraticForm R₁ M) :
  -- this is annoying
  (associated : _ →ₗ[A] _) (F.baseChange A) = ((associated : _ →ₗ[R₁] _) F).baseChange A := by
  simp only [baseChange]
  apply associated_left_inverse
  apply BilinForm.baseChangeSymm
  exact associated_isSymm R₁ F
end associated

-- /-- If F_A is the base change of the quadratic form F to A, then F_A(a ⊗ m) = a^2*F(m). -/
-- @[simp]
-- lemma QuadraticForm.baseChange_companion (F : QuadraticForm R M) [Invertible (2 : R)]
--   (B : BilinForm R M) (bH : ∀ x y, F (x + y) = F x + F y + B x y) :
--   F.baseChange A (x + y) = F.baseChange A x + F.baseChange A y + B.baseChange A x y := by
--   rw [baseChange, BilinForm.toQuadraticForm_apply]
--   simp
--   rw [← BilinForm.bilin_add_left]
--   rw [← BilinForm.bilin_add_left]
--   rw [← BilinForm.bilin_add_right]
  
--   -- , BilinForm.baseChange_eval, associated_apply,
--   --     ← two_smul R m, QuadraticForm.map_smul]
--   congr
--   rw [mul_assoc, invOf_mul_eq_iff_eq_mul_left]
--   ring

end base_change

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
variable {R : Type _} {M : Type _} [CommRing R] [AddCommGroup M] [Module R M]
variable              {M₂ : Type _}              [AddCommGroup M₂] [Module R M₂]

-- Let `A` be an `R`-algebra
variable (A : Type _) [Semiring A] [Algebra R A]

open TensorProduct -- this line gives us access to ⊗ notation

-- Let's be lazy and assume 1/2 ∈ R
variable [Invertible (2 : R)]

def ten {R A M N} [CommRing R] [Ring A] [Algebra R A] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module A M]
  [Module R N] [Module A N]
  (f : M →ₗ[R] N) :
  A ⊗[R] M →ₗ[A] A ⊗[R] N :=
  LinearMap.baseChange A f

@[simp]
lemma LinearMap.baseChange_id {R A M} [CommRing R] [Ring A] [Algebra R A]
  [AddCommMonoid M]
  [Module R M] :
  LinearMap.baseChange A LinearMap.id (R := R) = LinearMap.id (M := A ⊗[R] M) := by
  ext
  simp


@[simp]
lemma LinearMap.baseChange_comp {R A M N} [CommRing R] [Ring A] [Algebra R A]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid B]
    [Module R M] [Module R N] [Module R B] (f : M →ₗ[R] N) (g : N →ₗ[R] B) :
  (g.baseChange A).comp (f.baseChange A) = (g.comp f).baseChange A := by
  ext
  simp

-- TODO timeout if we make A a semiring
def LinearEquiv.baseChange {R A M N} [CommRing R] [Ring A] [Algebra R A] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    (f : M ≃ₗ[R] N) :
  A ⊗[R] M ≃ₗ[A] A ⊗[R] N where
    __ := LinearMap.baseChange A f
    invFun := LinearMap.baseChange A f.symm
    left_inv := by
      intro a
      simp [← LinearMap.comp_apply]
    right_inv := by
      intro a
      simp [← LinearMap.comp_apply]

@[simp]
lemma LinearEquiv.baseChange_apply {R A M N} [CommRing R] [Ring A] [Algebra R A] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    (f : M ≃ₗ[R] N) (a : A) (v : M) :
  ((f.baseChange : A ⊗[R] M ≃ₗ[A] A ⊗[R] N) : _ → _) (a ⊗ₜ[R] v) = (a ⊗ₜ f v) := rfl



lemma QuadraticForm.baseChange.Equivalent
  (A : Type _) [CommRing A] [Algebra R A]
  (Q : QuadraticForm R M) (S : QuadraticForm R M₂) (h : Q.Equivalent S) :
    (baseChange A Q).Equivalent (baseChange A S) := by
  cases' h with val
  constructor
  use (LinearEquiv.baseChange val.toLinearEquiv)
  intro m
  simp
  -- rw? -- TODO timeout whnf very quickly
  induction m using TensorProduct.induction_on
  . simp
  . simp
  . simp [map_add, *]
    obtain ⟨B, hB⟩ := (baseChange A S).exists_companion
    rw [hB] at *
    simp [*]
    sorry

end base_change

section basis
variable [Field k] [AddCommGroup M] [Module k M] [Ring A] [Algebra k A] [Module A M] [IsScalarTower k A M] 
  [StrongRankCondition A] [Module.Free k M] [Module.Free A M] [Module.Free k A]

open TensorProduct -- for notation

noncomputable
def _root_.Basis.base_change (h : Basis ι k M) : Basis ι A (A ⊗[k] M) :=
Algebra.TensorProduct.basis A h

lemma base_change_module_rank_preserved : Module.rank k M = Module.rank A (A ⊗[k] M) := by 
  obtain ⟨⟨_, bM⟩⟩ := Module.Free.exists_basis (R := k) (M := M)
  rw [← bM.mk_eq_rank'', (bM.base_change (A := A)).mk_eq_rank'']
end basis

-- section discr
-- variable [Field k] [AddCommGroup M] [Module k M] [CommRing A] [Algebra k A] [Module A M] [IsScalarTower k A M] 
--   [StrongRankCondition A] [Module.Free k M] [Module.Free A M] [Module.Free k A]
--   [Invertible (2 : k)]
--   [Invertible (2 : A)]

-- open TensorProduct -- for notation

-- lemma discr (Q : QuadraticForm k M) : (Q.baseChange A).discr = Q.discr := by 
--   obtain ⟨⟨_, bM⟩⟩ := Module.Free.exists_basis (R := k) (M := M)
--   rw [← bM.mk_eq_rank'', (bM.base_change (A := A)).mk_eq_rank'']

-- end discr
section degenerate
variable {k A} [Field k] [AddCommGroup M] [Module k M] [CommRing A] [Algebra k A] [Module A M] [IsScalarTower k A M] 
  [StrongRankCondition A] [Module.Free k M] [Module.Free A M] [Module.Free k A]
  [Invertible (2 : k)]
  [Invertible (2 : A)] -- TODO should this follow from TC

open QuadraticForm
theorem BilinForm.baseChange_of_degenerate (B : BilinForm k M) (hB : ¬ B.Nondegenerate) :
    ¬ (B.baseChange A).Nondegenerate := by
  simp only [BilinForm.Nondegenerate, not_forall, exists_prop] at *
  obtain ⟨x, hn, hx⟩ := hB
  refine ⟨(1 ⊗ₜ x), ?_, ?_⟩
  . intro n
    induction n using TensorProduct.induction_on
    . simp
    . simp [hn]
    . simp [*]
  . simp
    intro h
    apply hx
    sorry -- need to assume module is flat or something TODO?
    

theorem baseChange_of_degenerate (Q : QuadraticForm k M) (hQ : ¬ (associated (R₁ := k) Q).Nondegenerate) :
    ¬ (associated (R₁ := A) (Q.baseChange A)).Nondegenerate := by
  simp only [baseChange_associated]
  exact BilinForm.baseChange_of_degenerate _ hQ

end degenerate