module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceWedgeCoherence
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
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の全 necklace 射と元の wedge のモノイダルな構造データ。 -/
instance necklaceMonoidalStruct : MonoidalCategoryStruct Necklace.{u} where
  tensorObj := necklaceWedge
  tensorHom := necklaceWedgeMap
  whiskerLeft X {_ _} f := necklaceWedgeMap (𝟙 X) f
  whiskerRight {_ _} f Y := necklaceWedgeMap f (𝟙 Y)
  tensorUnit := necklacePoint
  associator := necklaceAssociator
  leftUnitor := necklaceLeftUnitor
  rightUnitor := necklaceRightUnitor

/-- 元の全端点保存単体的写像を持つ necklace のモノイダル圏。 -/
instance necklaceMonoidal : MonoidalCategory Necklace.{u} :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := necklaceWedgeMap_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' => (necklaceWedgeMap_comp f f' g g').symm)
    (associator_naturality := necklaceAssociator_naturality)
    (leftUnitor_naturality := necklaceLeftUnitor_naturality)
    (rightUnitor_naturality := necklaceRightUnitor_naturality)
    (pentagon := necklaceAssociator_pentagon)
    (triangle := necklaceAssociator_triangle)

/-- 元のモノイダルな tensor 関手は、既存の wedge の二変数関手そのもの。 -/
lemma necklaceMonoidal_tensor :
    MonoidalCategory.tensor Necklace.{u} = necklaceWedgeFunctor := rfl

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceMonoidal (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceMonoidal := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceMonoidal

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceMonoidalStruct (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceMonoidalStruct := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceMonoidalStruct

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceMonoidal_tensor := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceMonoidal_tensor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceMonoidal._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceMonoidal._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceMonoidal._proof_2 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceMonoidal._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceMonoidal._proof_3 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceMonoidal._proof_3
