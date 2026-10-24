module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitHomFormula

/-!
概要：指定単位の Hom 比較の始域側の自然性を h Fun で表す。
方針：双圏の単位 Hom 写像の自然性を二胞体表示同値で移す。
規約：単位の普遍性や余単位は不要。
使われ方：B1 の右三角恒等式から左 zigzag の単位による像を計算する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories
local instance unitLeftNaturalityHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

/-- 概要：単位の Hom 比較は始域側の二胞体による前合成に自然。
方針：双圏の自然性を二胞体の表示同値で移す。
規約：U,U',V は任意の関手。
使われ方：左 zigzag の単位による像の計算。 -/
lemma qcatUnitHomMap_naturality_left {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    {U U' : A ⟶ X} {V : A ⟶ Y} (γ : FunctorHom U' U) (α : FunctorHom (U ≫ F) V) :
    qcatUnitHomMap η U' V ((hoFunctor.map ((ihom A).map F)).toFunctor.map γ ≫ α) =
      γ ≫ qcatUnitHomMap η U V α := by
  obtain ⟨γ', rfl⟩ := (qcatCellEquiv U' U).surjective γ
  obtain ⟨α', rfl⟩ := (qcatCellEquiv (U ≫ F) V).surjective α
  rw [← qcatCell_whiskerRight γ' F]
  change qcatCellEquiv _ _ (bicategoryUnitHomMap
      ((qcatCellEquiv (𝟙 X) (F ≫ G)).symm η) (qcatMap U') (qcatMap V)
      (γ' ▷ qcatMap F ≫ α')) =
    qcatCellEquiv _ _ (γ' ≫ bicategoryUnitHomMap
      ((qcatCellEquiv (𝟙 X) (F ≫ G)).symm η) (qcatMap U) (qcatMap V) α')
  exact congrArg (qcatCellEquiv U' (V ≫ G))
    (bicategoryUnitHomMap_naturality_left _ γ' α')

end SerrePositivity.InfinityCategories
