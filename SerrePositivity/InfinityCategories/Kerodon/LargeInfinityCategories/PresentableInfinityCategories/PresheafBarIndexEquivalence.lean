module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafBarIndex

/-!
概要：bar 添字と元の elements 単体圏の厳密な宇宙比較。
方針：次数の二つの持ち上げを入れ直す逆関手を構成する。
規約：同じ要素と元の単体作用素を保持する。
使われ方：初頂点局所化による密度余極限の比較。

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

variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 概要：元の transport 単体を同じ bar 添字へ戻す。
方針：次数を持ち上げ、元の要素と全射を使う。
規約：次数や単体の選び直しは行わない。
使われ方：元の bar 比較の厳密な逆。 -/
def presheafBarFromTransport : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F) ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafBarIndex F where
  obj s := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarSimplexFamily F).elementsMk
    (ULiftHom.objUp (ULift.up s.objDown.obj)) s.objDown.val
  map f := { hom := ULift.up f.down.hom, map_val := f.down.map_val }

/-- 概要：bar 添字の nerve と元の transport 単体圏の nerve は厳密に同型。
方針：元の単体と作用素を保持する二つの逆関手を nerve に移す。
規約：初頂点写像と合成する順方向を元の比較に固定する。
使われ方：元の密度全余錐の bar 入力への移送。 -/
def presheafBarIndexNerveIso : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafBarIndex F) ≅
    nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F)) where
  hom := nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarToTransport F)
  inv := nerveMap (presheafBarFromTransport F)
  hom_inv_id := by rfl
  inv_hom_id := by rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
