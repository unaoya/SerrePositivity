module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanModelNativeComparison
public import SerrePositivity.InfinityCategories.F2.CoherentCospanNativeFinalTargetMaps

/-!
概要：元の実模型比較を切断側へ合成した二脚の共通点像を、元の右 fiber 二作用へ同定する。
方針：元の右脚の式と厳密な引き戻し条件を使う。
規約：二脚の終点は実射の等式で揃える。使われ方：指定同型の合成式の端点補正。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
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
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "fr" => vertexFiberMap pF pY (coherentTransformationTotalMap F Y C.toRight)
  (coherentTransformationTotalMap_projection F Y C.toRight) b
local notation "qr" => vertexFiberMap pY pZ (coherentTransformationTotalMap Y Z C.fromRight)
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local notation "M" => coherentCospanModelNativeComparison F X Y Z C b
local notation "I" => coherentCospanNativeCommonPointFiberIso F X Y Z C b

/-- 元の右脚を共通点で評価した射は、元の右 fiber 二作用の合成の持ち上げ。 -/
lemma coherentCospanModelRightFinalTargetMap :
    ((M ≫ pullback.snd f g) ≫ g) ≫ (I).hom =
      (SSet.uliftFunctor.{u + 1, u}).map (fr ≫ qr) := by
  have h := congrArg (fun k => (k ≫ g) ≫ (I).hom)
    (coherentCospanModelNativeComparison_right F X Y Z C b)
  exact h.trans (coherentCospanNativeRightFinalTargetMap F X Y Z C b)

/-- 左脚の終点も、元の厳密な引き戻し条件で同じ右二作用の合成に一致する。 -/
lemma coherentCospanModelLeftFinalTargetMap :
    ((M ≫ pullback.fst f g) ≫ f) ≫ (I).hom =
      (SSet.uliftFunctor.{u + 1, u}).map (fr ≫ qr) := by
  have h : (M ≫ pullback.fst f g) ≫ f = (M ≫ pullback.snd f g) ≫ g := by
    simp only [Category.assoc, pullback.condition]
  exact (congrArg (fun k => k ≫ (I).hom) h).trans
    (coherentCospanModelRightFinalTargetMap F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
