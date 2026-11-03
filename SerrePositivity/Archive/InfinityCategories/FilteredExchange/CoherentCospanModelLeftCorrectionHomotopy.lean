module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanModelNativeLeftIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNormalizedModelPathLift
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.LiftedIntervalCospanPathImage

/-!
概要：実模型の左脚の厳密化を元の模型で制限し、その共通終点像を元の全 path へ戻す。
方針：指定持ち上げの全円柱の射影と、共通点同型の往復の相殺を使う。
規約：全円柱を保持。使われ方：実模型比較の二脚の指定像の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "ql" => vertexFiberMap pX pZ (coherentTransformationTotalMap X Z C.fromLeft)
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "qr" => vertexFiberMap pY pZ (coherentTransformationTotalMap Y Z C.fromRight)
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local notation "η" => coherentCospanNativeFiberCospanComparison F X Y Z C b
local notation "I" => coherentCospanNativeCommonPointFiberIso F X Y Z C b
local notation "n" => coherentCospanNormalizedModelFiberComparison F X Y Z C b
local notation "pr" =>
  pullback.snd (NatTrans.app (intervalEndpointNatTrans 0) (vertexFiber pZ b)) ql
local instance : HomotopicalAlgebra.Fibration f :=
  relativeCospanLeftTarget_fibration pointedSpaceProjection d

/-- 元の模型比較から、小さい第一段 interval 置換への射影の持ち上げ。 -/
def coherentCospanModelLeftCorrectionParameter :=
  (SSet.uliftFunctor.{u + 1, u}).map n ≫
    (SSet.uliftFunctor.{u + 1, u}).map (pullback.fst (intervalReplacementEndpoint ql) qr)
local notation "a" => coherentCospanModelLeftCorrectionParameter F X Y Z C b
local notation "H" => liftedIntervalCospanHomotopy ql f
  (NatTrans.app η WalkingCospan.left) (NatTrans.app η WalkingCospan.one)
  (NatTrans.naturality η WalkingCospan.Hom.inl)

/-- 同じ元の全 path を持ち上げて得た左脚の補正円柱を、元の模型で制限する。 -/
def coherentCospanModelLeftCorrectionHomotopy :=
  functorHomotopyPrecomp (kanHomotopyRectificationHomotopy f
    ((SSet.uliftFunctor.{u + 1, u}).map pr ≫ (η).app WalkingCospan.left)
    ((SSet.uliftFunctor.{u + 1, u}).map (intervalReplacementEndpoint ql) ≫
      (η).app WalkingCospan.one) H) a

/-- 元の模型の補正円柱の共通点像は、元の正規化した全 path の持ち上げ。 -/
lemma coherentCospanModelLeftCorrectionHomotopy_image :
    (coherentCospanModelLeftCorrectionHomotopy F X Y Z C b).h ≫ f ≫ (I).hom =
      (uliftSimplicialHomotopy.{u, u + 1}
        (coherentCospanNormalizedModelPathHomotopy F X Y Z C b)).h := by
  let R := kanHomotopyRectificationHomotopy f
    ((SSet.uliftFunctor.{u + 1, u}).map pr ≫ (η).app WalkingCospan.left)
    ((SSet.uliftFunctor.{u + 1, u}).map (intervalReplacementEndpoint ql) ≫
      (η).app WalkingCospan.one) H
  have hp := kanHomotopyRectificationHomotopy_image f
    ((SSet.uliftFunctor.{u + 1, u}).map pr ≫ (η).app WalkingCospan.left)
    ((SSet.uliftFunctor.{u + 1, u}).map (intervalReplacementEndpoint ql) ≫
      (η).app WalkingCospan.one) H
  change ((a ▷ (Δ[1] : SSet.{u + 1})) ≫ R.h) ≫ f ≫ (I).hom = _
  calc
    _ = (a ▷ (Δ[1] : SSet.{u + 1})) ≫ (R.h ≫ f) ≫ (I).hom := by
      simp only [Category.assoc]
    _ = (a ▷ (Δ[1] : SSet.{u + 1})) ≫ (H).h ≫ (I).hom :=
      congrArg (fun k => (a ▷ (Δ[1] : SSet.{u + 1})) ≫ k ≫ (I).hom) hp
    _ = (a ▷ (Δ[1] : SSet.{u + 1})) ≫
        (uliftSimplicialHomotopy.{u, u + 1} (intervalReplacementPathHomotopy ql (𝟙 _))).h := by
      change _ ≫ (_ ≫ (I).inv) ≫ (I).hom = _
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by
      apply SSet.hom_ext
      intro k
      apply ConcreteCategory.hom_ext
      intro z
      rfl

end SerrePositivity.InfinityCategories.F2
