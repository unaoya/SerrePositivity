module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitHomFormula

/-!
概要：指定単位の Hom 比較の始域側の自然性を h Fun で表す。
方針：双圏の単位 Hom 写像の自然性を二胞体表示同値で移す。
規約：単位の普遍性や余単位は不要。
使われ方：B1 の右三角恒等式から左 zigzag の単位による像を計算する。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
local instance unitLeftNaturalityHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

/-- 概要：単位の Hom 比較は始域側の二胞体による前合成に自然。
方針：双圏の自然性を二胞体の表示同値で移す。
規約：U,U',V は任意の関手。
使われ方：左 zigzag の単位による像の計算。 -/
lemma qcatUnitHomMap_naturality_left {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    {U U' : A ⟶ X} {V : A ⟶ Y} (γ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' U) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap η U' V ((hoFunctor.map ((ihom A).map F)).toFunctor.map γ ≫ α) =
      γ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap η U V α := by
  obtain ⟨γ', rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U' U).surjective γ
  obtain ⟨α', rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U ≫ F) V).surjective α
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight γ' F]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryUnitHomMap
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (F ≫ G)).symm η) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap U') (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap V)
      (γ' ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ≫ α')) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (γ' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryUnitHomMap
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (F ≫ G)).symm η) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap U) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap V) α')
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U' (V ≫ G))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryUnitHomMap_naturality_left _ γ' α')

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
