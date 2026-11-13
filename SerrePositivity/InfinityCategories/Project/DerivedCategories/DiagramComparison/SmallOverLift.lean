module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SmallBousfieldKanWeight
/-!
概要：指定AsSmall.downに対するover圏の同じ持ち上げを明示する。
方針：元の対象・射・構造射にULift.upを入れ、両合成の等式を確認する。
規約：IS-W2 A12の持ち上げ照合の証明分割。別の同値を選ばない。
使われ方：HA 1.2.4、元の小さいBK重みから係数環の宇宙への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {J : Type} [SmallCategory J]
/-- 元のover対象の構造射を同じAsSmallの対象へ持ち上げる。 -/
def smallOverLift (j : AsSmall.{u} J) : Over ((AsSmall.down : AsSmall.{u} J ⥤ J).obj j) ⥤ Over j where
  obj f := Over.mk (show ((AsSmall.up : J ⥤ AsSmall.{u} J).obj f.left) ⟶ j from
    (AsSmall.up : J ⥤ AsSmall.{u} J).map f.hom)
  map a := Over.homMk ((AsSmall.up : J ⥤ AsSmall.{u} J).map a.left) (by apply ULift.ext; exact Over.w a)
  map_id f := by apply Over.OverMorphism.ext; rfl
  map_comp a b := by apply Over.OverMorphism.ext; rfl
/-- 指定持ち上げを元のdownで戻すと同じover図式になる。 -/
theorem smallOverLift_down (j : AsSmall.{u} J) :
    smallOverLift j ⋙ Over.post (AsSmall.down : AsSmall.{u} J ⥤ J) = 𝟭 _ := by
  rfl
/-- downの後で指定持ち上げをすると元のover図式になる。 -/
theorem smallOverDown_lift (j : AsSmall.{u} J) :
    Over.post (AsSmall.down : AsSmall.{u} J ⥤ J) ⋙ smallOverLift j = 𝟭 _ := by
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
