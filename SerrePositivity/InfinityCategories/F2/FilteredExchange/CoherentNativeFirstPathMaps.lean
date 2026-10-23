module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanCommonPathClasses

/-!
概要：native 候補の第一置換 path の両端を、元の二つの native 合成射へ同定する。
方針：元の入力射影の式と引き戻し条件、元の候補の第二脚を使う。
規約：元の射の等式を明示。使われ方：指定逆 path の像の端点を保持して比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "nf" => coherentTotalMapNativeValueDown X Z
  (coherentTransformationTotalMap X Z C.fromLeft)
local notation "ng" => coherentTotalMapNativeValueDown Y Z
  (coherentTransformationTotalMap Y Z C.fromRight)
local notation "n" => coherentCospanConeNativeComparison F X Y Z C

/-- 第一置換 path の始端は元の native 左二射の合成。 -/
lemma coherentCospanNativeFirstPathSourceMap :
    (n ≫ pullback.fst (intervalReplacementEndpoint nf) ng) ≫
      (pullback.snd ((intervalEndpointNatTrans 0).app
        (spaceInfinityObject (coherentDiagramTotalVertex Z)).obj) nf ≫ nf) =
          coherentTotalMapNativeValueDown F X
            (coherentTransformationTotalMap F X C.toLeft) ≫ nf := by
  rw [← Category.assoc, coherentCospanNativeFirstInput]

/-- 第一置換 path の終端は元の native 右二射の合成。 -/
lemma coherentCospanNativeFirstPathTargetMap :
    (n ≫ pullback.fst (intervalReplacementEndpoint nf) ng) ≫ intervalReplacementEndpoint nf =
      coherentTotalMapNativeValueDown F Y (coherentTransformationTotalMap F Y C.toRight) ≫ ng := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  change (n ≫ intervalPullbackRight nf ng) ≫ ng = _
  rw [coherentCospanConeNativeComparison_right]

end SerrePositivity.InfinityCategories.F2
