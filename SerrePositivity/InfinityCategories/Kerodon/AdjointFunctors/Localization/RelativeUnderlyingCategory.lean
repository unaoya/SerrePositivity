module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory

/-!
# 元の相対圏の底の圏の関手

概要：元の指定射の条件を忘れ、同じ全対象・全射の圏を返す。
方針：元の相対関手の functor を Cat の射として使う。
規約：恒等と合成を厳密に保持する。
使われ方：元の自由相対解像の底の Hom の弱比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

def underlyingCategoryFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} ⥤ Cat.{u, u} where
  obj C := C.category
  map F := F.functor.toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
