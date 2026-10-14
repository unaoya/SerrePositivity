module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteMilnorAnnihilator
public import SerrePositivity.HomologicalAlgebra.TwoCohomologyAnnihilator

/-! # 完備な二次数導来対象の標準Koszul塔からの零化

比較同型を追加の入力にせず、標準再構成と既存の二段零化を合成する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 完備な二次数対象のKoszul剰余の一様零化から、対象上のg⁴ᴺ零射を得る。 -/
theorem complete_two_cohomology_scalar_pow_eq_zero
    (p : R) (X : DerivedCategory (ModuleCat.{u} R)) (hX : IsComplete R p X)
    (a b : ℤ) (hab : a + 1 = b) [X.IsGE a] [X.IsLE b] (g : R) (N : ℕ)
    (ha : ∀ n,
      (∀ x : (complexPowerKoszulStage R p (DerivedCategory.Q.objPreimage X) n).homology a,
        g ^ N • x = 0) ∧
      (∀ x : (complexPowerKoszulStage R p (DerivedCategory.Q.objPreimage X) n).homology (a - 1),
        g ^ N • x = 0))
    (hb : ∀ n,
      (∀ x : (complexPowerKoszulStage R p (DerivedCategory.Q.objPreimage X) n).homology b,
        g ^ N • x = 0) ∧
      (∀ x : (complexPowerKoszulStage R p (DerivedCategory.Q.objPreimage X) n).homology (b - 1),
        g ^ N • x = 0)) :
    g ^ (4 * N) • 𝟙 X = 0 :=
  two_cohomology_scalar_pow_eq_zero_of_iso_homotopyLimit R X a b hab
    (complexPowerKoszulStage R p (DerivedCategory.Q.objPreimage X))
    (complexPowerKoszulTransition R p (DerivedCategory.Q.objPreimage X))
    (completeDerivedKoszulHomotopyLimitIso R p X hX) g N ha hb

/-- 実際の加群写像の導来錐への標準再構成を使った零化。
Milnor列に必要な-2,-1,0の全次数を仮定に残す。 -/
theorem complete_moduleMapConeScalar_pow_eq_zero (p : R)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hC : IsComplete R p (moduleMapCone R f)) (g : R) (q : ℕ)
    (ha : ∀ n,
      (∀ x : (complexPowerKoszulStage R p
        (DerivedCategory.Q.objPreimage (moduleMapCone R f)) n).homology (-1), g ^ q • x = 0) ∧
      (∀ x : (complexPowerKoszulStage R p
        (DerivedCategory.Q.objPreimage (moduleMapCone R f)) n).homology (-2), g ^ q • x = 0))
    (hb : ∀ n,
      (∀ x : (complexPowerKoszulStage R p
        (DerivedCategory.Q.objPreimage (moduleMapCone R f)) n).homology 0, g ^ q • x = 0) ∧
      (∀ x : (complexPowerKoszulStage R p
        (DerivedCategory.Q.objPreimage (moduleMapCone R f)) n).homology (-1), g ^ q • x = 0)) :
    moduleMapConeScalar R f (g ^ (4 * q)) = 0 :=
  moduleMapConeScalar_pow_eq_zero_of_iso_homotopyLimit R f
    (complexPowerKoszulStage R p (DerivedCategory.Q.objPreimage (moduleMapCone R f)))
    (complexPowerKoszulTransition R p (DerivedCategory.Q.objPreimage (moduleMapCone R f)))
    (completeDerivedKoszulHomotopyLimitIso R p (moduleMapCone R f) hC) g q ha hb

end SerrePositivity
