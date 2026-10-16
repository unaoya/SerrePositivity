module
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Ideal.Operations

/-! # Finite ideal filtrations for extension-closed properties of arbitrary modules -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory
variable {R : Type u} [CommRing R]

/-- Any extension-closed property holding on I-annihilated modules holds on Iⁿ-annihilated ones. -/
lemma moduleProperty_of_idealPower_annihilated (I : Ideal R) (P : ModuleCat.{u} R → Prop)
    (hI : ∀ N : ModuleCat.{u} R, (∀ r ∈ I, ∀ x : N, r • x = 0) → P N)
    (hExt : ∀ S : ShortComplex (ModuleCat.{u} R), S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂) :
    ∀ n : ℕ, ∀ N : ModuleCat.{u} R, (∀ r ∈ I ^ n, ∀ x : N, r • x = 0) → P N := by
  intro n
  induction n with
  | zero =>
    intro N hN
    have hx (x : N) : x = 0 := by simpa using hN 1 (by simp) x
    apply hI N
    intro r hr x
    rw [hx x, smul_zero]
  | succ n ih =>
    intro N hN
    let K : Submodule R N := I • ⊤
    have hK : ∀ r ∈ I ^ n, ∀ x : K, r • x = 0 := by
      intro r hr x
      apply Subtype.ext
      change r • (x : N) = 0
      refine Submodule.smul_induction_on x.property ?_ ?_
      · intro s hs y hy
        rw [← mul_smul]
        exact hN (r * s) (by simpa only [pow_succ] using Ideal.mul_mem_mul hr hs) y
      · intro x y hx hy
        rw [smul_add, hx, hy, add_zero]
    have hQ : ∀ r ∈ I, ∀ x : N ⧸ K, r • x = 0 := by
      intro r hr x
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        change Submodule.Quotient.mk (r • x) = (0 : N ⧸ K)
        exact (Submodule.Quotient.mk_eq_zero K).mpr
          (Submodule.smul_mem_smul hr (Submodule.mem_top))
    let S := ModuleCat.shortComplexOfCompEqZero K.subtype K.mkQ
      (LinearMap.exact_subtype_mkQ K).linearMap_comp_eq_zero
    have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
      (LinearMap.exact_subtype_mkQ K) K.injective_subtype K.mkQ_surjective
    exact hExt S hS (ih (ModuleCat.of R K) hK) (hI (ModuleCat.of R (N ⧸ K)) hQ)

/-- A nilpotent ideal makes this finite extension argument apply to every module. -/
lemma moduleProperty_of_nilpotentIdeal (I : Ideal R) (hNil : ∃ n : ℕ, I ^ n = ⊥)
    (P : ModuleCat.{u} R → Prop)
    (hI : ∀ N : ModuleCat.{u} R, (∀ r ∈ I, ∀ x : N, r • x = 0) → P N)
    (hExt : ∀ S : ShortComplex (ModuleCat.{u} R), S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (N : ModuleCat.{u} R) : P N := by
  obtain ⟨n, hn⟩ := hNil
  apply moduleProperty_of_idealPower_annihilated I P hI hExt n N
  intro r hr x
  rw [hn, Ideal.mem_bot] at hr
  rw [hr, zero_smul]

end SerrePositivity
