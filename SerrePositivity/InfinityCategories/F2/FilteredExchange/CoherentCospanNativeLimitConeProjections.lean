module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeLimitConeLeg
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanIntervalConeProjectionIsos

/-!
概要：余極限後の native 極限錐の二脚を、元の native 余極限写像へ指定同型で比較する。
方針：元の全錐円柱の脚比較と区間錐の射影比較を合成し、元の座標式で終点を戻す。
規約：元の脚・比較・指定値を保持。使われ方：一般 coherent 図式の引き戻し交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
  (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b))
local notation "f" => coherentCospanNativeLeftKanMap F X Y Z C
local notation "g" => coherentCospanNativeRightKanMap F X Y Z C
local notation "n" => coherentCospanConeNativeComparison F X Y Z C
local notation "left" => AsSmall.up.obj WalkingCospan.left
local notation "right" => AsSmall.up.obj WalkingCospan.right

/-- 左脚の指定比較を、元の比較と元の第一射影の合成まで続ける。 -/
def coherentCospanNativeLimitConeLeftCompositeIso :
    FunctorIso (coherentCospanNativeLimitConeKanLeg F X Y Z C hc left)
      (n ≫ intervalPullbackLeft (show _ from f) (show _ from g)) :=
  coherentCospanNativeLimitConeLegIso F X Y Z C hc left ≪≫
    (intervalPullbackConeFstIso f g).precomp n

/-- 右脚の指定比較を、元の比較と元の第二射影の合成まで続ける。 -/
def coherentCospanNativeLimitConeRightCompositeIso :
    FunctorIso (coherentCospanNativeLimitConeKanLeg F X Y Z C hc right)
      (n ≫ intervalPullbackRight (show _ from f) (show _ from g)) :=
  coherentCospanNativeLimitConeLegIso F X Y Z C hc right ≪≫
    (intervalPullbackConeSndIso f g).precomp n

/-- 元の native 左内脚への、同じ指定三角形からの脚比較。 -/
def coherentCospanNativeLimitConeFstIso :
    FunctorIso (coherentCospanNativeLimitConeKanLeg F X Y Z C hc left)
      (coherentTotalMapNativeValueDown F X (coherentTransformationTotalMap F X C.toLeft)) :=
  functorIsoOfEq (coherentCospanNativeLimitConeLeftCompositeIso F X Y Z C hc) rfl
    (coherentCospanConeNativeComparison_left F X Y Z C)

/-- 元の native 右内脚への、同じ指定三角形からの脚比較。 -/
def coherentCospanNativeLimitConeSndIso :
    FunctorIso (coherentCospanNativeLimitConeKanLeg F X Y Z C hc right)
      (coherentTotalMapNativeValueDown F Y (coherentTransformationTotalMap F Y C.toRight)) :=
  functorIsoOfEq (coherentCospanNativeLimitConeRightCompositeIso F X Y Z C hc) rfl
    (coherentCospanConeNativeComparison_right F X Y Z C)

end SerrePositivity.InfinityCategories.F2
