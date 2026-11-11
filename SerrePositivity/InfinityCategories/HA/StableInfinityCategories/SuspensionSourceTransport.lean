module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonComposition
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionAmbientHom

/-! # Suspension の指定始点の表示変更と対象比較

概要：指定始点を等号に沿って変えた suspension の対象比較同型を計算する。
方針：等号を消去し、元の四角形の対象比較と懸垂関手の恒等射の保存へ帰着する。
規約：四角形自体は保つ。使われ方：D7 の cofiber 接続射と mapTriangle の第三射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {x y : X _⦋0⦌}

/-- 始点表示変更後の対象比較の順方向。 -/
lemma SuspensionSquare.changeSource_objIso_hom (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (h : x = y) :
    (s.changeSource h).suspensionFunctorObjIso.hom =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map (eqToHom (congrArg SSet.HomotopyCategory.mk h.symm)) ≫
        s.suspensionFunctorObjIso.hom := by
  cases h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- 始点表示変更後の対象比較の逆方向。 -/
lemma SuspensionSquare.changeSource_objIso_inv (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (h : x = y) :
    (s.changeSource h).suspensionFunctorObjIso.inv =
      s.suspensionFunctorObjIso.inv ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map (eqToHom (congrArg SSet.HomotopyCategory.mk h)) := by
  cases h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
