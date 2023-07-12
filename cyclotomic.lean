import Mathlib.Tactic -- tactics
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure -- algebraic closures


/-!

# The cyclotomic character

Thoughts about the definition of the cyclotomic character.

-/

-- let `K` be a field and let `L` be an algebraic closure of `K` (should be sep closure)
variable (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]

/-

## The mod n theory

-/

-- let `n` be a positive natural number
variable (n : ℕ+)

def Torsion : Submonoid L where
  carrier := {x : L | x ^ n.val = 1}
  mul_mem' := sorry
  one_mem' := sorry

instance : Group (Torsion L n) where
  toMonoid := inferInstance
  inv := fun x ↦ ⟨x⁻¹, sorry⟩
  mul_left_inv := sorry

instance : Finite (Torsion L n) := sorry

def Torsion.galois_action (g : L ≃ₐ[K] L) : Torsion L n →* Torsion L n where
  toFun := fun t ↦ ⟨g t, sorry⟩
  map_one' := sorry
  map_mul' := sorry

instance Torsion.isCyclic : IsCyclic (Torsion L n) :=
  isCyclic_of_subgroup_isDomain (Submonoid.subtype (Torsion L n)) sorry

-- MonoidHom.map_cyclic is the theorem that any automorphism of a cyclic group (G,×)
-- is "raise every element to the power m" for some integer m
theorem Torsion.galois_action.integer_power (g : L ≃ₐ[K] L) :
    ∃ m : ℤ, ∀ t : Torsion L n, g t = t ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (Torsion.galois_action K L n g)
  use m
  simpa [Subtype.ext_iff, -SetLike.coe_eq_coe] using hm
