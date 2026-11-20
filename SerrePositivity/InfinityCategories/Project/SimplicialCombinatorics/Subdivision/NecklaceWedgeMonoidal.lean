module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeCoherence
public import Mathlib.CategoryTheory.Monoidal.Category

/-! # 元の全 necklace 射を持つ native wedge のモノイダル圏
概要：実単体的写像の wedge と元の一点・構造同型を一つのモノイダル圏に束ねる。
方針：二変数関手、全射の自然性、五角と三角の検証を使う。
規約：単体的写像も全高次単体も保持。使われ方：cubical rigidification の合成。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の全 necklace 射と元の wedge のモノイダルな構造データ。 -/
instance necklaceMonoidalStruct : MonoidalCategoryStruct _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} where
  tensorObj := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge
  tensorHom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap
  whiskerLeft X {_ _} f := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap (𝟙 X) f
  whiskerRight {_ _} f Y := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f (𝟙 Y)
  tensorUnit := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint
  associator := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator
  leftUnitor := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor
  rightUnitor := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor

/-- 元の全端点保存単体的写像を持つ necklace のモノイダル圏。 -/
instance necklaceMonoidal : MonoidalCategory _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_comp f f' g g').symm)
    (associator_naturality := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_naturality)
    (leftUnitor_naturality := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor_naturality)
    (rightUnitor_naturality := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor_naturality)
    (pentagon := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_pentagon)
    (triangle := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_triangle)

/-- 元のモノイダルな tensor 関手は、既存の wedge の二変数関手そのもの。 -/
lemma necklaceMonoidal_tensor :
    MonoidalCategory.tensor _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeFunctor := rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
