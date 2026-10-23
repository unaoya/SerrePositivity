module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeIntervalComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNormalizedModelFiberComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeFiberSectionsIso

/-!
概要：元の実模型 fiber 比較を native 切断の厳密な引き戻しへ合成する。
方針：元の比較を正規化し、同じ全 path を持ち上げた比較を後合成する。
規約：実際の元の比較を使う。使われ方：native な指定二脚との最終整合。
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
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "ql" => vertexFiberMap pX pZ (coherentTransformationTotalMap X Z C.fromLeft)
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "qr" => vertexFiberMap pY pZ (coherentTransformationTotalMap Y Z C.fromRight)
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local notation "fr" => vertexFiberMap pF pY (coherentTransformationTotalMap F Y C.toRight)
  (coherentTransformationTotalMap_projection F Y C.toRight) b
local notation "η" => coherentCospanNativeFiberCospanComparison F X Y Z C b
local notation "n" => coherentCospanNormalizedModelFiberComparison F X Y Z C b
local instance : KanComplex (vertexFiber pX b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (vertexFiber pY b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (vertexFiber pZ b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : HomotopicalAlgebra.Fibration f :=
  relativeCospanLeftTarget_fibration pointedSpaceProjection d
/-- 元の模型比較を持ち上げ、元の同じ切断の引き戻しへ合成した実際の射。 -/
def coherentCospanModelNativeComparison : coherentNativeTriangleFiberParameters F b ⟶
    pullback f g :=
  (SSet.uliftFunctor.{u + 1, u}).map n ≫ coherentCospanNativeIntervalComparison F X Y Z C b
/-- 左射影は元の第一段の射影と、同じ指定 path で厳密化した左成分との合成。 -/
lemma coherentCospanModelNativeComparison_left :
    coherentCospanModelNativeComparison F X Y Z C b ≫ pullback.fst f g =
      ((SSet.uliftFunctor.{u + 1, u}).map n ≫
        (SSet.uliftFunctor.{u + 1, u}).map (pullback.fst (intervalReplacementEndpoint ql) qr)) ≫
      liftedIntervalCospanLeft ql f ((η).app WalkingCospan.left) ((η).app WalkingCospan.one)
        ((η).naturality WalkingCospan.Hom.inl) := by
  rw [coherentCospanModelNativeComparison, Category.assoc]
  change (SSet.uliftFunctor.{u + 1, u}).map n ≫
    (liftedIntervalPullbackComparison ql qr f g
      ((η).app WalkingCospan.left) ((η).app WalkingCospan.right) ((η).app WalkingCospan.one)
      ((η).naturality WalkingCospan.Hom.inl) ((η).naturality WalkingCospan.Hom.inr) ≫
        pullback.fst f g) = _
  have h := liftedIntervalPullbackComparison_left ql qr f g
    ((η).app WalkingCospan.left) ((η).app WalkingCospan.right) ((η).app WalkingCospan.one)
    ((η).naturality WalkingCospan.Hom.inl) ((η).naturality WalkingCospan.Hom.inr)
  exact (congrArg (fun a => (SSet.uliftFunctor.{u + 1, u}).map n ≫ a) h).trans
    (Category.assoc _ _ _).symm
/-- 合成の右射影は、元の実際の右 fiber 射と同じ辺の切断比較との合成。 -/
lemma coherentCospanModelNativeComparison_right :
    coherentCospanModelNativeComparison F X Y Z C b ≫ pullback.snd f g =
      (SSet.uliftFunctor.{u + 1, u}).map fr ≫
        coherentCospanNativeRightFiberEdgeSections F X Y Z C b := by
  rw [coherentCospanModelNativeComparison, Category.assoc]
  change (SSet.uliftFunctor.{u + 1, u}).map n ≫
    (liftedIntervalPullbackComparison ql qr f g
      ((η).app WalkingCospan.left) ((η).app WalkingCospan.right) ((η).app WalkingCospan.one)
      ((η).naturality WalkingCospan.Hom.inl) ((η).naturality WalkingCospan.Hom.inr) ≫
        pullback.snd f g) = _
  have hk := liftedIntervalPullbackComparison_right ql qr f g
    ((η).app WalkingCospan.left) ((η).app WalkingCospan.right) ((η).app WalkingCospan.one)
    ((η).naturality WalkingCospan.Hom.inl) ((η).naturality WalkingCospan.Hom.inr)
  have h := congrArg
    (fun a : vertexFiber pF b ⟶ vertexFiber pY b =>
      (SSet.uliftFunctor.{u + 1, u}).map a ≫
        coherentCospanNativeRightFiberEdgeSections F X Y Z C b)
    (coherentCospanNormalizedModelFiberComparison_right F X Y Z C b)
  apply (congrArg (fun a => (SSet.uliftFunctor.{u + 1, u}).map n ≫ a) hk).trans
  change (SSet.uliftFunctor.{u + 1, u}).map n ≫
    (SSet.uliftFunctor.{u + 1, u}).map (intervalPullbackRight ql qr) ≫
      coherentCospanNativeRightFiberEdgeSections F X Y Z C b = _
  simpa only [Functor.map_comp, Category.assoc] using h
/-- 同じ native な右脚の指定同型は、この実際の合成の右射影との同型である。 -/
def coherentCospanModelNativeRightIso :
    FunctorIso (coherentCospanNativeSectionPullback F X Y Z C b ≫ pullback.snd f g)
      (coherentCospanModelNativeComparison F X Y Z C b ≫ pullback.snd f g) :=
  functorIsoOfEq (coherentCospanNativeRightFiberSectionsIso F X Y Z C b) rfl
    (coherentCospanModelNativeComparison_right F X Y Z C b).symm

end SerrePositivity.InfinityCategories.F2
