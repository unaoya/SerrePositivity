module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanModelNativeComparison

/-!
概要：実模型から切断模型への合成の左脚を、native な同じ指定左脚と比較する。
方針：元の左脚の指定同型に、元の全 path を持ち上げた指定同型を合成する。
規約：同型を選び直さない。使われ方：二脚と指定 path の最後の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "ql" => vertexFiberMap pX pZ (coherentTransformationTotalMap X Z C.fromLeft)
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "qr" => vertexFiberMap pY pZ (coherentTransformationTotalMap Y Z C.fromRight)
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local notation "fl" => vertexFiberMap pF pX (coherentTransformationTotalMap F X C.toLeft)
  (coherentTransformationTotalMap_projection F X C.toLeft) b
local notation "η" => coherentCospanNativeFiberCospanComparison F X Y Z C b
local notation "n" => coherentCospanNormalizedModelFiberComparison F X Y Z C b
local instance : HomotopicalAlgebra.Fibration f :=
  relativeCospanLeftTarget_fibration pointedSpaceProjection d

/-- 同じ native な左脚を、元の全 path で厳密化した実模型比較の左射影へ接続する同型。 -/
def coherentCospanModelNativeLeftIso :
    FunctorIso (coherentCospanNativeSectionPullback F X Y Z C b ≫ pullback.fst f g)
      (coherentCospanModelNativeComparison F X Y Z C b ≫ pullback.fst f g) := by
  let a := (SSet.uliftFunctor.{u + 1, u}).map n ≫
    (SSet.uliftFunctor.{u + 1, u}).map (pullback.fst (intervalReplacementEndpoint ql) qr)
  let e := (liftedIntervalCospanLeftIso ql f ((η).app WalkingCospan.left)
    ((η).app WalkingCospan.one) ((η).naturality WalkingCospan.Hom.inl)).precomp a
  refine coherentCospanNativeLeftFiberSectionsIso F X Y Z C b ≪≫ functorIsoOfEq e ?_ ?_
  · change a ≫ ((SSet.uliftFunctor.{u + 1, u}).map
      (pullback.snd ((intervalEndpointNatTrans 0).app (vertexFiber pZ b)) ql) ≫
      coherentCospanNativeLeftFiberEdgeSections F X Y Z C b) = _
    have hh : (n ≫ pullback.fst (intervalReplacementEndpoint ql) qr) ≫
        pullback.snd ((intervalEndpointNatTrans 0).app (vertexFiber pZ b)) ql = fl :=
      (Category.assoc _ _ _).trans
        (coherentCospanNormalizedModelFiberComparison_left F X Y Z C b)
    have hm : a ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (pullback.snd ((intervalEndpointNatTrans 0).app (vertexFiber pZ b)) ql) =
        (SSet.uliftFunctor.{u + 1, u}).map fl := by
      calc
        _ = (SSet.uliftFunctor.{u + 1, u}).map
          ((n ≫ pullback.fst (intervalReplacementEndpoint ql) qr) ≫
            pullback.snd ((intervalEndpointNatTrans 0).app (vertexFiber pZ b)) ql) := by
              simp only [a, Functor.map_comp]
        _ = _ := congrArg
          (fun k : vertexFiber pF b ⟶ vertexFiber pX b =>
            (SSet.uliftFunctor.{u + 1, u}).map k) hh
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ coherentCospanNativeLeftFiberEdgeSections F X Y Z C b) hm)
  · exact (coherentCospanModelNativeComparison_left F X Y Z C b).symm

end SerrePositivity.InfinityCategories.F2
