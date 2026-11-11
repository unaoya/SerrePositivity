module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitTransport

/-!
概要：左右の関手の同型に沿って指定単位の条件を同時に移送する。
方針：二つの既存の単位移送を順に適用し、指定した単位の式で同定する。
規約：元の全関手圏の射の式を入力にする。
使われ方：実単位の母空間での随伴条件の不変性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：左右の関手の可逆比較と可換単位は同じ随伴条件を移す。
方針：左・右関手の指定単位の移送を合成し、元の単位の等式で終点を揃える。
規約：移送後の随伴の存在は追加仮定にしない。
使われ方：元の対応空間の辺の単位条件の不変性。 -/
lemma unitMappingSpaceCondition_changePair {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {L₀ L₁ : C ⟶ D} {R₀ R₁ : D ⟶ C}
    {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 C) (L₀ ≫ R₀)} {η' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 C) (L₁ ≫ R₁)}
    (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso L₀ L₁) (j : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso R₀ R₁)
    (hη : (η ≫ (hoFunctor.map ((ihom C).map R₀)).toFunctor.map i.hom) ≫
      (hoFunctor.map ((pre L₁).app C)).toFunctor.map j.hom = η')
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (F := L₀) (G := R₀) η) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (F := L₁) (G := R₁) η' := by
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitMappingSpaceCondition_changeLeft (C := C) (D := D)
    (L := L₀) (L' := L₁) (R := R₀) (η := η) h i
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitMappingSpaceCondition_changeRight (C := C) (D := D)
    (L := L₁) (R := R₀) (R' := R₁)
    (η := η ≫ (hoFunctor.map ((ihom C).map R₀)).toFunctor.map i.hom) hL j
  exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (F := L₁) (G := R₁)) hη).mp hR

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
