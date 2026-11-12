module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# 相対圏の元の指定射の圏とその厳密な関手性

概要：元の指定射だけからなる wide 部分圏を相対圏の関手として構成する。
方針：元の相対関手の射作用と指定性の保存をそのまま使う。
規約：指定射の乗法性以外の条件を要求しない。
使われ方：DK2.4に渡す元の指定部分圏の単体的解像。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

def markedCategoryMap {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    WideSubcategory C.weakEquivalences ⥤ WideSubcategory D.weakEquivalences where
  obj X := ⟨F.functor.obj X.obj⟩
  map f := ⟨F.functor.map f.hom, F.map f.hom f.property⟩
  map_id X := by apply WideSubcategory.hom_ext; exact F.functor.map_id X.obj
  map_comp f g := by apply WideSubcategory.hom_ext; exact F.functor.map_comp f.hom g.hom

def markedCategoryFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} ⥤ Cat.{u, u} where
  obj C := Cat.of (WideSubcategory C.weakEquivalences)
  map F := (markedCategoryMap F).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
