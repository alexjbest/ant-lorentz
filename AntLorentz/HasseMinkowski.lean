import Mathlib.Tactic -- lots of tactics
import Mathlib.LinearAlgebra.QuadraticForm.Basic -- quadratic forms
import Mathlib.LinearAlgebra.TensorProduct -- tensor products (for base change)
import Mathlib.LinearAlgebra.Dimension -- rank of modules
import Mathlib.NumberTheory.Padics.PadicNumbers
import AntLorentz.Diagonalize
import AntLorentz.BaseChange

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


-- Let `M` be an `R`-module
variable {R : Type _} {M : Type _} [CommRing R] [AddCommGroup M] [Module R M]

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
  simp only [AlgebraTensorModule.curry_apply, curry_apply, coe_restrictScalars, baseChange_tmul, id_coe, id_eq]


@[simp]
lemma LinearMap.baseChange_comp {R A M N} [CommRing R] [Ring A] [Algebra R A]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid B]
    [Module R M] [Module R N] [Module R B] (f : M →ₗ[R] N) (g : N →ₗ[R] B) :
  (g.baseChange A).comp (f.baseChange A) = (g.comp f).baseChange A := by
  ext
  simp only [AlgebraTensorModule.curry_apply, curry_apply, coe_restrictScalars, coe_comp, Function.comp_apply,
    baseChange_tmul]

-- TODO timeout if we make A a semiring
def LinearEquiv.baseChange {R A M N} [CommRing R] [Ring A] [Algebra R A] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    (f : M ≃ₗ[R] N) :
  A ⊗[R] M ≃ₗ[A] A ⊗[R] N where
    __ := LinearMap.baseChange A f
    invFun := LinearMap.baseChange A f.symm
    left_inv := by
      intro a
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ← LinearMap.comp_apply, LinearMap.baseChange_comp, comp_coe,
        self_trans_symm, refl_toLinearMap, LinearMap.baseChange_id, LinearMap.id_coe, id_eq]
    right_inv := by
      intro a
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ← LinearMap.comp_apply, LinearMap.baseChange_comp, comp_coe,
        symm_trans_self, refl_toLinearMap, LinearMap.baseChange_id, LinearMap.id_coe, id_eq]


lemma QuadraticForm.baseChange.Equivalent
  (A : Type _) [CommRing A] [Algebra R A]
  (Q S : QuadraticForm R M) (h : Q.Equivalent S) :
    (baseChange A Q).Equivalent (baseChange A S) := by
  cases' h with val
  constructor
  use (LinearEquiv.baseChange val.toLinearEquiv)
  intro m
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
  -- rw? -- TODO timeout whnf very quickly
  sorry

-- Let V be a ℚ-vector space
variable {V : Type} [AddCommGroup V] [Module ℚ V]

-- Assume `V` is finite-dimensional (mathematical remark: is this definitely necessary??)
variable [FiniteDimensional ℚ V]

-- Let `F` be a quadratic form on V
variable (F : QuadraticForm ℚ V)

/-- A quadratic form over ℚ is everywhere locally isotropic if it has nontrivial
p-adic points for all p, and real points. -/
def QuadraticForm.EverywhereLocallyIsotropic :=
  (∀ (p : ℕ) [Fact (p.Prime)], (F.baseChange ℚ_[p]).Isotropic) ∧
  (F.baseChange ℝ).Isotropic

/-- The *statement* of the Hasse-Minkowski theorem. -/
def QuadraticForm.Hasse_Minkowski (F : QuadraticForm ℚ V) : Prop :=
  F.Isotropic ↔ F.EverywhereLocallyIsotropic


namespace QuadraticForm

-- a nontrivial project (probably publishable if someone does it)
theorem Hasse_Minkowski_proof : ∀ (F : QuadraticForm ℚ V), F.Hasse_Minkowski := sorry

-- some easier problems

variable (k W : Type) [Field k] [AddCommGroup W]

-- The quadratic form 0 on a vector space of dimension greater than zero is isotropic. 
lemma Isotropic_of_zero_quadForm_dim_ge1 [Module k W] (Q : QuadraticForm k W) (h₁ : Q=0) 
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

-- the easy direction
theorem QuadraticForm.global_to_local (F : QuadraticForm ℚ V) : F.Isotropic → F.EverywhereLocallyIsotropic := by
  simp only [Isotropic, Anisotropic, not_forall, exists_prop, EverywhereLocallyIsotropic, forall_exists_index, and_imp]
  intro x Fx0 xn0
  constructor
  · intro p hp
    use ((1 : ℚ_[p]) ⊗ₜ x)
    constructor
    · rw [F.baseChange_eval ℚ_[p] x, Fx0]
      simp only [mul_one, _root_.map_zero, mul_zero]
    sorry -- todo: base change of non-zero to ℚ_[p] is non-zero
  use ((1 : ℝ) ⊗ₜ x)
  constructor
  · rw [F.baseChange_eval ℝ x, Fx0]
    simp only [mul_one, _root_.map_zero, mul_zero]
  sorry -- todo: base change of non-zero to ℝ is non-zero


-- (0) dim(V)=0 case

-- Every quadratic form on a zero-dimensional vector space is anisotropic. 
lemma anisotropic_of_quadForm_dim_zero [Module k W] (Q : QuadraticForm k W) 
(h : Module.rank k W = 0) : Q.Anisotropic := by
   intro (w : W)
   intro 
   rw [rank_zero_iff_forall_zero] at h
   exact h w

-- Proof of Hasse Minkowski in dimension 0.
theorem Hasse_Minkowski0 (hV : Module.rank ℚ V = 0) : ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := by
   intro F
   rw [Hasse_Minkowski]
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
lemma isotropic_of_zero_quadForm_dim_ge1 [Module k W] (Q : QuadraticForm k W) (h₁ : Q=0) 
(h₂ : Module.rank k W ≠ 0) : Q.Isotropic := by
  rw [QuadraticForm.Isotropic]
  rw [QuadraticForm.Anisotropic]
  have h: ∃ (w : W), w ≠ 0 := by
    simpa [rank_zero_iff_forall_zero] using h₂
  obtain ⟨w, hw⟩ := h 
  have : Q w = 0 := by 
    rw [h₁]
    simp
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
theorem Hasse_Minkowski1 (hV : Module.rank V = 1) :
    ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := sorry


-- Some general lemmas for all cases of dimension at least 2:

lemma HM_of_Equivalent {Q S : QuadraticForm ℚ V} (h : Q.Equivalent S) :
    Q.Hasse_Minkowski ↔ S.Hasse_Minkowski := by
  simp only [Hasse_Minkowski, Isotropic, EverywhereLocallyIsotropic] at *
  simp only [anisotropic_iff _ _ h]
  rw [anisotropic_iff _ _ (baseChange.Equivalent ℝ _ _ h)]
  conv in (Anisotropic (baseChange _ Q)) =>
    rw [anisotropic_iff _ _ (baseChange.Equivalent (R := ℚ) ℚ_[p] _ _ h)]


-- (2) dim(V)=2 case

lemma rat_sq_iff_local_sq (x : ℚ) : IsSquare x ↔ (∀ (p : ℕ) [Fact (p.Prime)], IsSquare (x : ℚ_[p])) ∧ IsSquare (x : ℝ) := by
  sorry 

theorem Hasse_Minkowski2 (hV : Module.rank V = 2) :
    ∀ (F : QuadraticForm ℚ V), Hasse_Minkowski F := sorry

--#lint