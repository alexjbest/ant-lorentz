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
  exact congrFun (congrArg HMul.hMul h) c

def Torsion : Submonoid L where
  carrier := {x : L | x ^ n.val = 1}
  mul_mem' := by
    intro x y a b
    simp at *
    have h: (x*y)^n.val = x^n.val * y^n.val:= by
      rw [mul_pow]
    rw [h]
    rw[a,b,mul_one]
    done

  one_mem' := by
    have: 1^n.val=1:= by
      rw [one_pow]
    simp
    done

  lemma mem_torsion_iff(a:L): a ∈ Torsion L n ↔ a^n.val=1:= by
    rfl
    done

  variable {L}
  lemma nonzero_of_torsion (a : L) (ha: a ∈ Torsion L n): a ≠ 0:= by
    rw [mem_torsion_iff] at ha
    intro h
    rw [h] at ha
    simp at ha
    done




    instance : Group (Torsion L n) where
  toMonoid := inferInstance
  inv := fun x ↦ ⟨x⁻¹, by
  -- show x^-1 is also a torsion point.
    have: ∀ a b c: L, a*b=c → (a*b)^n.val=c^n.val:= by
      simp
    simp [Torsion]
    apply x.prop⟩

  mul_left_inv := by
    intro a
    cases' a with a ha
    simp
    ext
    simp
    have h₄: ∀ a: L, a ≠ 0 → a⁻¹*a=1 := by
      intro b
      intro hb
      simp [hb]
    apply h₄
    apply nonzero_of_torsion n a ha
    done


instance : Finite (Torsion L n) := by
  apply Set.finite_coe_iff.mpr
  classical
  let x := (Polynomial.nthRoots n (1: L)).toFinset
  convert Set.finite_mem_finset x
  simp [Torsion]


instance Torsion.isCyclic : IsCyclic (Torsion L n) :=
  isCyclic_of_subgroup_isDomain (Submonoid.subtype (Torsion L n)) ( by
  -- rintro⟨x,hx⟩ ⟨y,hy⟩ rfl
  intro x y h
  simp at h
  exact h
  done)


def Torsion.galois_action (g : L ≃+* L) : Torsion L n →* Torsion L n where
  toFun := fun t ↦ ⟨g t, by
  -- prove this is in torsion
  cases' t with t ht
  dsimp
  rw [mem_torsion_iff] at ht ⊢
  rw [← map_pow]
  rw [ht]
  rw [map_one]
  done⟩
  map_one' := by
    simp
    rfl
    done
  map_mul' := by
    simp
    done


-- MonoidHom.map_cyclic is the theorem that any automorphism of a cyclic group (G,×)
-- is "raise every element to the power m" for some integer m
theorem Torsion.galois_action.integer_power (g : L ≃+* L) :
    ∃ m : ℤ, ∀ t : Torsion L n, g t = t ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (Torsion.galois_action n g)
  use m
  simpa [Subtype.ext_iff, -SetLike.coe_eq_coe] using hm

  /-- `ModularCyclotomicCharacter_aux g n` is a non-canonical auxiliary integer `m`,
   only well-defined mod n, such that `g(ζ)=ζ^m` for all n'th roots of unity ζ in L . -/
noncomputable def ModularCyclotomicCharacter_aux (g : L ≃+* L) (n : ℕ+) : ℤ :=
  (Torsion.galois_action.integer_power n g).choose

-- the only thing we know about `ModularCyclotomicCharacter_aux g n`
theorem ModularCyclotomicCharacter_aux_spec (g : L ≃+* L) (n : ℕ+) :
    ∀ t : Torsion L n, g t = t ^ (ModularCyclotomicCharacter_aux g n) :=
  (Torsion.galois_action.integer_power n g).choose_spec

/-- `ModularCyclotomicCharacter g n` is the `m : ZMod n` such that `g(ζ)=ζ^m` for all
n'th roots of unity. -/
noncomputable def ModularCyclotomicCharacter (g : L ≃+* L) (n : ℕ+) : ZMod n :=
  ModularCyclotomicCharacter_aux g n

-- This appears to be missing from the library
theorem Group.pow_eq_pow_mod {G : Type _} [Group G] {x : G} (m : ℤ) {n : ℕ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % (n : ℤ)) := by
  have t : x ^ m = x ^ ((n : ℤ) * (m / (n : ℤ)) + m % (n : ℤ)) :=
    congr_arg (fun a => x ^ a) ((Int.add_comm _ _).trans (Int.emod_add_ediv _ _)).symm
  dsimp at t
  rw [t, zpow_add, zpow_mul]
  simp
  rw [h, one_zpow]


/-- The formula which characterises the output of `ModularCyclotomicCharacter g n`. -/
theorem ModularCyclotomicCharacter_spec (g : L ≃+* L) (n : ℕ+) :
    ∀ t : Torsion L n, g t = t ^ (ModularCyclotomicCharacter g n).val := by
  rintro t
  -- this is nearly right
  convert ModularCyclotomicCharacter_aux_spec g n t
  rw [← zpow_ofNat, ModularCyclotomicCharacter, ZMod.val_int_cast, ←Group.pow_eq_pow_mod]
  rcases t with ⟨t, ht⟩
  convert ht
  simp [Torsion]
  aesop
  done

-- need to prove it is monoid homomorphism

  -- lemma have_nth_roots_of_unity

-- lemma ModularCyclotomicCharacter_id: ModularCyclotomicCharacter (RingEquiv.refl) (n)
-- -- error !!!!!!




-- lemma ModularCyclotomicCharacter_comm (g:  L ≃+* L) (h:  L ≃+* L) (n : ℕ+) :
-- --  do we need to assume we have all nth roots of unity?
--   (ModularCyclotomicCharacter g n).val+(ModularCyclotomicCharacter h n).val =(ModularCyclotomicCharacter (g * h) n).val := by
--     have hyp: ∀ t ∈ Torsion L n, (g * h) t=t^( (ModularCyclotomicCharacter g n).val*(ModularCyclotomicCharacter h n).val):= by
--       apply ModularCyclotomicCharacter_spec

--   done



-- for the general cyclotomic character, we do not want to fix a p, but make a map to Z^*