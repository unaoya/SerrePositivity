module

public import SerrePositivity.CommutativeAlgebra.ScalarIsogeny
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators

/-! # Claim 2.4.8の一般加群版

被約環上の有限生成加群から有限自由加群への写像がgを反転すると同型なら、
その実導来錐へのあるg冪倍は零射である。perfectoid化の存在やalmost purityは使わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R] [IsReduced R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- 核をg^a、余核をg^bが消すとき、錐はg^(a+b)で零化される。 -/
theorem finiteFreeConeIsogeny (g : R) (r : ℕ) (f : M →ₗ[R] (Fin r → R))
    (hf : Function.Bijective (awayModuleMap g f)) :
    ∃ n : ℕ, moduleMapConeScalar R f (g ^ n) = 0 := by
  obtain ⟨a, b, ha, hb⟩ := exists_pow_ker_coker_annihilator g r f hf
  refine ⟨a + b, ?_⟩
  rw [pow_add]
  exact moduleMapConeScalar_eq_zero_of_ker_coker_annihilated R f (g ^ a) (g ^ b) ha hb

/-- 同じg冪による核・余核の零化と、実導来錐の零射を同時に公開する。 -/
theorem finiteFreeConeIsogeny_with_annihilators
    (g : R) (r : ℕ) (f : M →ₗ[R] (Fin r → R))
    (hf : Function.Bijective (awayModuleMap g f)) :
    ∃ n : ℕ, moduleMapConeScalar R f (g ^ n) = 0 ∧
      (∀ x : f.ker, g ^ n • x = 0) ∧
      (∀ y : (Fin r → R) ⧸ f.range, g ^ n • y = 0) := by
  obtain ⟨n, hn⟩ := finiteFreeConeIsogeny R g r f hf
  exact ⟨n, hn, moduleMapCone_pow_scalar_eq_zero_annihilates R f g n hn⟩

/-- 有限R代数から有限直積RへのR線形写像に対するClaim 2.4.8。 -/
theorem finiteAlgebraConeIsogeny {S : Type u} [CommRing S] [Algebra R S]
    [Module.Finite R S] (g : R) (r : ℕ) (f : S →ₗ[R] (Fin r → R))
    (hf : Function.Bijective (awayModuleMap g f)) :
    ∃ n : ℕ, moduleMapConeScalar R f (g ^ n) = 0 :=
  finiteFreeConeIsogeny R g r f hf

end SerrePositivity.CLMST
