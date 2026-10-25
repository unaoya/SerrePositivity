module

public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticPowerResidueNilpotent

/-! # 冪零prism剰余を経由する実導来基底変更

A→A/(a,dⁿ)→A/(a,d)の標準射に沿って、二つの実導来対象を比較する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] (a d : A) (n : ℕ) (hn : 0 < n)
local notation "qₙ" => Ideal.Quotient.mk (Ideal.span (Set.insert a (Set.singleton (d ^ n))))
local notation "q₁" => Ideal.Quotient.mk (Ideal.span (Set.insert a (Set.singleton d)))
local notation "rₙ" => prismaticPowerResidueMap a d n hn

/-- 冪零剰余射を経由する通常基底変更の複体上での標準合成比較。 -/
def prismaticPowerResidueCochainCompositionIso :
    (ModuleCat.extendScalars q₁).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars qₙ).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.extendScalars rₙ).mapHomologicalComplex (.up ℤ) := by
  let e : ModuleCat.extendScalars q₁ ≅
      ModuleCat.extendScalars qₙ ⋙ ModuleCat.extendScalars rₙ :=
    eqToIso (congrArg ModuleCat.extendScalars
        (prismaticPowerResidueMap_comp a d n hn).symm) ≪≫
      ModuleCat.extendScalarsComp qₙ rₙ
  exact (Functor.mapHomologicalComplexCompIso e.symm (.up ℤ)).symm

/-- 実一乗剰余への基底変更を、実冪剰余と実冪零剰余射の二段階で計算する。 -/
def prismaticPowerResidueDerivedCompositionIso
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    (boundedAboveDerivedBaseChange q₁).obj X ≅
      (boundedAboveDerivedBaseChange rₙ).obj
        ((boundedAboveDerivedBaseChange qₙ).obj X) :=
  ObjectProperty.isoMk _
    (DerivedCategory.Q.mapIso ((prismaticPowerResidueCochainCompositionIso a d n hn).app
        (boundedAboveDerivedChosenModel X).complex) ≪≫
      (boundedAboveDerivedBaseChangeModelIso rₙ ((boundedAboveDerivedBaseChange qₙ).obj X)
        (boundedAboveDerivedBaseChangeModel qₙ X)).symm)

end SerrePositivity.BhattScholze
