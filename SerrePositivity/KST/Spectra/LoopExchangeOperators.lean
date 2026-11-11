module

public import SerrePositivity.KST.Spectra.CircleClassMap
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange
public import SerrePositivity.KST.Spectra.PointedMappingNaturality

/-!
概要：二重 loop の交換と符号反転の元の点つき作用射。
方針：Kan 円の交換と整数次数 -1 の前合成を明示する。
規約：区間選択を含めない。使われ方：普遍的交換区間と従来の比較の共通下位界面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.LoopExchangePaths

/-- 元の同じ Kan 円による二重 loop 空間。 -/
abbrev doubleLoop (Y : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.basedHom CirclePower.space.{u} (PointedObject.basedHom CirclePower.space.{u} Y)

/-- 元の二つの Kan 円の交換射。 -/
def swap (Y : PointedSimplicialSet.{u}) : doubleLoop Y ⟶ doubleLoop Y :=
  (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Y).hom

/-- 元の内側の Kan 円の符号反転。 -/
def reversal (Y : PointedSimplicialSet.{u}) : doubleLoop Y ⟶ doubleLoop Y :=
  PointedObject.basedHomMap CirclePower.space.{u}
    (Y := PointedObject.basedHom CirclePower.space.{u} Y)
    (Z := PointedObject.basedHom CirclePower.space.{u} Y)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Y)

end SerrePositivity.KST.Spectra.LoopExchangePaths
