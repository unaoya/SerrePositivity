module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafBarIndex

/-!
概要：bar 添字と元の elements 単体圏の厳密な宇宙比較。
方針：次数の二つの持ち上げを入れ直す逆関手を構成する。
規約：同じ要素と元の単体作用素を保持する。
使われ方：初頂点局所化による密度余極限の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 概要：元の transport 単体を同じ bar 添字へ戻す。
方針：次数を持ち上げ、元の要素と全射を使う。
規約：次数や単体の選び直しは行わない。
使われ方：元の bar 比較の厳密な逆。 -/
def presheafBarFromTransport : TransportSimplexCategory (smallRightUnstraightening F) ⥤
    PresheafBarIndex F where
  obj s := (presheafBarSimplexFamily F).elementsMk
    (ULiftHom.objUp (ULift.up s.objDown.obj)) s.objDown.val
  map f := { hom := ULift.up f.down.hom, map_val := f.down.map_val }

/-- 概要：bar 添字の nerve と元の transport 単体圏の nerve は厳密に同型。
方針：元の単体と作用素を保持する二つの逆関手を nerve に移す。
規約：初頂点写像と合成する順方向を元の比較に固定する。
使われ方：元の密度全余錐の bar 入力への移送。 -/
def presheafBarIndexNerveIso : nerve (PresheafBarIndex F) ≅
    nerve (TransportSimplexCategory (smallRightUnstraightening F)) where
  hom := nerveMap (presheafBarToTransport F)
  inv := nerveMap (presheafBarFromTransport F)
  hom_inv_id := by rfl
  inv_hom_id := by rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
