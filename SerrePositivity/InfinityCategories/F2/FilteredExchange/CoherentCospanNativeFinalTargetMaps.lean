module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeFiberCospanComparison

/-!
概要：native 二脚の共通点像の終点を、元の小さい fiber 二作用の合成へ明示して同定する。
方針：元の辺の切断の厳密な終点式と、宇宙持ち上げの合成則を使う。
規約：端点の射を具体的に比較。使われ方：元の指定同型の合成式の輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
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
local notation "fl" => vertexFiberMap pF pX (coherentTransformationTotalMap F X C.toLeft)
  (coherentTransformationTotalMap_projection F X C.toLeft) b
local notation "fr" => vertexFiberMap pF pY (coherentTransformationTotalMap F Y C.toRight)
  (coherentTransformationTotalMap_projection F Y C.toRight) b
local notation "ql" => vertexFiberMap pX pZ (coherentTransformationTotalMap X Z C.fromLeft)
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "qr" => vertexFiberMap pY pZ (coherentTransformationTotalMap Y Z C.fromRight)
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local notation "L" => coherentCospanNativeLeftFiberEdgeSections F X Y Z C b
local notation "R" => coherentCospanNativeRightFiberEdgeSections F X Y Z C b
local notation "I" => coherentCospanNativeCommonPointFiberIso F X Y Z C b

/-- 元の左 fiber 射と辺の切断比較を共通点で評価すると、元の二作用の合成になる。 -/
lemma coherentCospanNativeLeftFinalTargetMap :
    (((SSet.uliftFunctor.{u + 1, u}).map fl ≫ L) ≫ f) ≫ (I).hom =
      (SSet.uliftFunctor.{u + 1, u}).map (fl ≫ ql) := by
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map fl ≫ (L ≫ f ≫ (I).hom) := by
      simp only [Category.assoc]
    _ = _ := (congrArg (fun k => (SSet.uliftFunctor.{u + 1, u}).map fl ≫ k)
      (coherentCospanNativeLeftFiberEdgeSections_target F X Y Z C b)).trans
        ((SSet.uliftFunctor.{u + 1, u}).map_comp fl ql).symm

/-- 右側でも同じ元の二作用と同じ共通点を保持する。 -/
lemma coherentCospanNativeRightFinalTargetMap :
    (((SSet.uliftFunctor.{u + 1, u}).map fr ≫ R) ≫ g) ≫ (I).hom =
      (SSet.uliftFunctor.{u + 1, u}).map (fr ≫ qr) := by
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map fr ≫ (R ≫ g ≫ (I).hom) := by
      simp only [Category.assoc]
    _ = _ := (congrArg (fun k => (SSet.uliftFunctor.{u + 1, u}).map fr ≫ k)
      (coherentCospanNativeRightFiberEdgeSections_target F X Y Z C b)).trans
        ((SSet.uliftFunctor.{u + 1, u}).map_comp fr qr).symm

end SerrePositivity.InfinityCategories.F2
