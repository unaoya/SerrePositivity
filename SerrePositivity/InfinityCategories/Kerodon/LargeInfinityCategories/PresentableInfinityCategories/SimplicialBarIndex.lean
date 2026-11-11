module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertexNaturality
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：任意の小さい単体集合を、その全単体の次数ごとの bar 添字へ展開する。
方針：単体次数の宇宙を合わせた型値図式の要素圏を取る。
規約：元の全単体と全作用素を保持する。
使われ方：小余積と幾何学的実現からの全小余極限の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：小さい単体集合の全単体を、宇宙を合わせた次数上の型値図式とする。
方針：次数の持ち上げを忘れる二つの関手を元の単体集合へ合成する。
規約：元の面と退化の作用を変更しない。
使われ方：次数ごとの左 Kan 延長の要素圏。 -/
def simplicialBarSimplexFamily (K : SSet.{u}) :
    ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ) ⥤ Type u :=
  ULiftHom.down ⋙ ULift.downFunctor ⋙ K

/-- 概要：全単体の要素圏から元の transport 単体圏への比較。
方針：次数の宇宙持ち上げを忘れ、元の要素と作用素を使う。
規約：元の単体の選び直しは行わない。
使われ方：元の単体集合への初頂点写像の接続。 -/
def simplicialBarToTransport (K : SSet.{u}) :
    (simplicialBarSimplexFamily K).Elements ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory K where
  obj s := ULiftHom.objUp (K.elementsMk s.obj.objDown.down s.val)
  map f := ⟨{ hom := f.hom.down, map_val := f.map_val }⟩

/-- 概要：元の transport 単体を同じ bar 添字へ戻す。
方針：次数を持ち上げ、同じ単体を使う。
規約：元の全射を保持する。
使われ方：全単体の添字の宇宙比較の逆。 -/
def simplicialBarFromTransport (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory K ⥤ (simplicialBarSimplexFamily K).Elements where
  obj s := (simplicialBarSimplexFamily K).elementsMk
    (ULiftHom.objUp (ULift.up s.objDown.obj)) s.objDown.val
  map f := { hom := ULift.up f.down.hom, map_val := f.down.map_val }

/-- 概要：bar 添字の nerve と元の単体圏の nerve の厳密な同型。
方針：同じ全単体と全作用素を保持する二つの逆関手を使う。
規約：順方向は元の transport 比較に固定する。
使われ方：展開した図式から元の小さい全図式への余錐の回収。 -/
def simplicialBarIndexNerveIso (K : SSet.{u}) :
    nerve (simplicialBarSimplexFamily K).Elements ≅ nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory K) where
  hom := nerveMap (simplicialBarToTransport K)
  inv := nerveMap (simplicialBarFromTransport K)
  hom_inv_id := by rfl
  inv_hom_id := by rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
