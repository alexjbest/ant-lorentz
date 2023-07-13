import Mathlib.Tactic -- tactics
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure -- algebraic closures


/-!

# The cyclotomic character

Thoughts about the definition of the cyclotomic character.

-/

-- let `L` be a field
variable (L : Type) [Field L]

/-

## The mod n theory

-/

-- let `n` be a positive natural number
variable (n : ℕ+)

example: ∀ a b c: L, a=b → a*c=b*c:= by
  intro a b c h
  exact?

def Torsion : Submonoid L where
  carrier := {x : L | x ^ n.val = 1}
  mul_mem' := by
    intro x y a b
    simp at *
    have h: (x*y)^n.val = x^n.val * y^n.val:= by
      rw [mul_pow]
    rw [h]
    rw[a,b,mul_one]
  one_mem' := by
    have hyp: 1^n.val=1:= by
      rw [one_pow]
    simp

    instance : Group (Torsion L n) where
  toMonoid := inferInstance
  inv := fun x ↦ ⟨x⁻¹, sorry⟩
  -- show x^-1 is also a torsion point.
    -- have h: ∀ a b c: L, a*b=c → (a*b)^n.val=c^n.val:= by
    --   simp
    -- simp [Torsion] ⟩
  mul_left_inv := by
    intro a
    cases' a with a ha
    simp
    ext
    simp
    have h': ∀ b: Torsion L n, (b : L) ≠ 0:= by
      have h₁: ∀ c: L, c^n.val ≠ 0 → c ≠ 0:=by
        simp
      have h₂: ∀ d: Torsion L n, (d:L)^n.val ≠ 0:= by
        simp [Torsion]
        intro x hx hx₀
        rw [hx₀] at hx
        simp at hx









instance : Finite (Torsion L n) := sorry

variable {L}

instance Torsion.isCyclic : IsCyclic (Torsion L n) :=
  isCyclic_of_subgroup_isDomain (Submonoid.subtype (Torsion L n)) sorry

def Torsion.galois_action (g : L ≃+* L) : Torsion L n →* Torsion L n where
  toFun := fun t ↦ ⟨g t, sorry⟩
  map_one' := sorry
  map_mul' := sorry

-- MonoidHom.map_cyclic is the theorem that any automorphism of a cyclic group (G,×)
-- is "raise every element to the power m" for some integer m
theorem Torsion.galois_action.integer_power (g : L ≃+* L) :
    ∃ m : ℤ, ∀ t : Torsion L n, g t = t ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (Torsion.galois_action n g)
  use m
  simpa [Subtype.ext_iff, -SetLike.coe_eq_coe] using hm
