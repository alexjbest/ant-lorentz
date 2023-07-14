import Mathlib.Tactic -- tactics
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure -- algebraic closures
import Lean
open Lean Elab Tactic

elab "tada" : tactic => do
  let gs ← getUnsolvedGoals
  if gs.isEmpty then
    logInfo "Goals accomplished 🎉"
  else
    Term.reportUnsolvedGoals gs
    throwAbortTactic



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

noncomputable instance: Fintype (Torsion L n):= Fintype.ofFinite _


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

  -- During the writing of the proof of this lemma, I realised that `Fintype G` seems to
-- be the way to state that `G` is finite in the statements of lemmas, so I changed
-- the statement of the lemma.
lemma ModularCyclotomicCharacter.ext {G : Type _} [Group G] [Fintype G] [IsCyclic G]
    (n : ℕ+) (a b : ZMod n) (hGcard : Fintype.card G = n) (h : ∀ t : G, t^a.val = t^b.val) :
  a = b := by
  -- G is cyclic so get an element g and a proof hg that G=<g>
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  -- Deduce `hgord`, the fact that order of g is |G|. This deduction is already in the
  -- library as `orderOf_eq_card_of_forall_mem_zpowers` (guess the statement from the name!)
  -- Remark: I found this lemma by opening the file where `IsCyclic` is defined, and then
  -- just reading through the *statements* of the lemmas until I found the useful one.
  have hgord := orderOf_eq_card_of_forall_mem_zpowers hg
  -- use hypothesis `h` on this `g`
  specialize h g
  -- our hypothesis is now `g^A=g^B` for some naturals A and B (the `val`s of `a` and `b`),
  -- and we know the
  -- order of g is n, so we want to deduce something like A-B is a multiple of n.
  -- But natural subtraction is a weird function (it gives the wrong answer if B>A)
  -- so that's not the function we want to use as we'll lose information.
  -- Looking through lemmas that start with `pow_eq_pow` using the Esc, ctrl-space trick
  -- which I showed you today, we find this:
  rw [pow_eq_pow_iff_modEq] at h
  -- So now `h says A≡B [MOD orderOf g]` and we're trying to get into `ZMod n`
  -- so we're going to need that `orderOf G = n` so we may as well fix this now
  rw [hgord, hGcard] at h -- `h : ZMod.val a ≡ ZMod.val b [MOD n]`
  -- The plan is now :
  -- (1) `A≡B [MOD n]` implies `(A : ZMod n) = (B : ZMod n)`
  -- and (2) `(↑A : ZMod n)=a` (lift then reduce and you're back where you started)

  -- Solve (1) like this. The output tells you the relevant lemma.
  -- `have h2 : ((ZMod.val a) : ZMod n) = ((ZMod.val b) : ZMod n) := by exact?`
  rw [← ZMod.nat_cast_eq_nat_cast_iff] at h
  -- Solve (2) with `have foo : ((ZMod.val a) : ZMod n) = a := by simp?`. Again
  -- the output tells you the relevant lemmas
  simpa [ZMod.nat_cast_val, ZMod.cast_id'] using h
  done


-- need to prove it is monoid homomorphism

lemma ModularCyclotomicCharacter_id (hGcard : Fintype.card (Torsion L n) = n): ModularCyclotomicCharacter (RingEquiv.refl L) (n)=1 := by
  sorry
-- -- needs hGcarc
-- show we get a map to (Z/nZ)^*

lemma coe_pow (a : Torsion L n) (b : ℕ) : (a : L)^b = ((a^b : Torsion L n) : L) := by exact rfl

lemma coe_mul (n m : ℕ) (a b : ZMod n) (h : m ∣ n) : ((a * b : ZMod n) : ZMod m) = (a : ZMod m) * (b : ZMod m) := by
    apply ZMod.cast_mul h a b



lemma ModularCyclotomicCharacter_mul (g:  L ≃+* L) (h:  L ≃+* L) (n : ℕ+) (hGcard : Fintype.card (Torsion L n) = n):
--  do we need to assume we have all nth roots of unity?


  (ModularCyclotomicCharacter g n)*(ModularCyclotomicCharacter h n) =(ModularCyclotomicCharacter (g * h) n) := by
    -- have hyp: ∀ t ∈ Torsion L n, (g * h) t=t^( (ModularCyclotomicCharacter g n).val*(ModularCyclotomicCharacter h n).val):= by
  apply ModularCyclotomicCharacter.ext n _ _ hGcard
  intro t
  apply SetCoe.ext
  rw [← ModularCyclotomicCharacter_spec]
  change _ = (g (h t))
  rw [ModularCyclotomicCharacter_spec]
  rw [ModularCyclotomicCharacter_spec]
  -- cases' t with t ht
  simp
  rw [← pow_mul]
  rw [coe_pow]
  rw [coe_pow]
  congr 1
  rw [pow_eq_pow_iff_modEq]
  rw [← ZMod.nat_cast_eq_nat_cast_iff]
  -- Solve (2) with `have foo : ((ZMod.val a) : ZMod n) = a := by simp?`. Again
  -- the output tells you the relevant lemmas
  simp [ZMod.nat_cast_val, ZMod.cast_id']
  rw [coe_mul, mul_comm]
  rw [← hGcard]
  exact orderOf_dvd_card_univ
  tada

  
--   done



-- for the general cyclotomic character, we do not want to fix a p, but make a map to Z^*