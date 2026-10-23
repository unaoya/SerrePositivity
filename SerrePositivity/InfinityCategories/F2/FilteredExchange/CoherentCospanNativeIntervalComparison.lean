module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeFiberCospanEnd
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.LiftedIntervalPullbackComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeCospanSectionFibrations

/-!
概要：元の実 fiber の interval 引き戻しから native 切断の厳密な引き戻しへの比較同値。
方針：構成済みの元の cospan の三成分を、全 path を持ち上げる比較へ適用する。
規約：元の小さい模型を持ち上げる。使われ方：元の実模型 fiber 比較への普遍性の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
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
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "ql" => vertexFiberMap pX pZ (coherentTransformationTotalMap X Z C.fromLeft)
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "qr" => vertexFiberMap pY pZ (coherentTransformationTotalMap Y Z C.fromRight)
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local notation "η" => coherentCospanNativeFiberCospanComparison F X Y Z C b
local instance : KanComplex (vertexFiber pX b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (vertexFiber pY b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (vertexFiber pZ b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : Fibration f := relativeCospanLeftTarget_fibration pointedSpaceProjection d

/-- 実 fiber の元の小さい interval 模型から、元の二辺の切断の厳密な引き戻しへの比較。 -/
def coherentCospanNativeIntervalComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (intervalPullback ql qr) ⟶ pullback f g :=
  liftedIntervalPullbackComparison ql qr f g
    ((η).app WalkingCospan.left) ((η).app WalkingCospan.right) ((η).app WalkingCospan.one)
    ((η).naturality WalkingCospan.Hom.inl) ((η).naturality WalkingCospan.Hom.inr)

/-- 元の指定 path を持ち上げる実際の比較は、単体的ホモトピー同値。 -/
lemma coherentCospanNativeIntervalComparison_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (coherentCospanNativeIntervalComparison F X Y Z C b) :=
  liftedIntervalPullbackComparison_homotopyEquivalence ql qr f g
    ((η).app WalkingCospan.left) ((η).app WalkingCospan.right) ((η).app WalkingCospan.one)
    ((η).naturality WalkingCospan.Hom.inl) ((η).naturality WalkingCospan.Hom.inr)
    (coherentCospanNativeFiberCospanComparison_app_homotopyEquivalence F X Y Z C b _)
    (coherentCospanNativeFiberCospanComparison_app_homotopyEquivalence F X Y Z C b _)
    (coherentCospanNativeFiberCospanComparison_app_homotopyEquivalence F X Y Z C b _)

end SerrePositivity.InfinityCategories.F2
