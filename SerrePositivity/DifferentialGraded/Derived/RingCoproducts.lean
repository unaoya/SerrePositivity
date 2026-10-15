module
public import SerrePositivity.DifferentialGraded.Derived.Coproducts
public import SerrePositivity.DifferentialGraded.Derived.Ring
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # 一対象環の導来圏比較による余積の保存 -/
@[expose] public section
noncomputable section
universe u w t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable (J : Type t) [Small.{u} J]

instance ringDerivedEquivalencePreservesCoproducts :
    PreservesColimitsOfShape (Discrete J) (ringDerivedEquivalence A).functor := inferInstance

instance ringDerivedInversePreservesCoproducts :
    PreservesColimitsOfShape (Discrete J) (ringDerivedEquivalence A).inverse := inferInstance

/-- 指定宇宙の既存導来圏にも同じ添字の余積を移送する。 -/
instance ringDerivedTargetHasCoproducts :
    HasColimitsOfShape (Discrete J) (DerivedCategory (ModuleCat A)) :=
  Adjunction.hasColimitsOfShape_of_equivalence (ringDerivedEquivalence A).inverse

instance ringDerivedCoproductComparisonIsIso (M : J → DerivedModuleCategory A PUnit.{1}) :
    IsIso (sigmaComparison (ringDerivedEquivalence A).functor M) := inferInstance

end SerrePositivity.DifferentialGraded
