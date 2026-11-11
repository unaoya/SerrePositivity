module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedSuspensionNaturality
public import SerrePositivity.KST.Spectra.SuspensionComposition

/-! # 元の円を固定する標準点つき suspension の厳密豊穣関手
概要：同じ元の suspension と全 basedHom 作用を、専用の標準点つき対象へ束ねる。
方針：元の suspensionHom の単位・全合成保存をそのまま使う。
規約：大域の豊穣 instance は変更しない。使われ方：Ex∞ suspension 比較の厳密自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 元の同じ円と全単体的写像族を保持する、標準点つき suspension の厳密豊穣関手。 -/
def pointedSSetSuspensionEnrichedFunctor :
    EnrichedFunctor SSet.{u} PointedSSetObject.{u} PointedSSetObject.{u} where
  obj := pointedSSetSuspensionObject
  map X Y := (Spectra.suspensionHom X.obj Y.obj).right
  map_id X := Spectra.suspensionHom_simplicial_id X.obj
  map_comp X Y Z := Spectra.suspensionHom_simplicial_comp X.obj Y.obj Z.obj

/-- suspension の実値は、元の円との同じ smash。 -/
lemma pointedSSetSuspensionEnrichedFunctor_obj (X : PointedSSetObject.{u}) :
    (pointedSSetSuspensionEnrichedFunctor.obj X).obj = _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj := rfl

/-- 全 Hom 作用は、元の suspensionHom そのもの。 -/
lemma pointedSSetSuspensionEnrichedFunctor_map (X Y : PointedSSetObject.{u}) :
    pointedSSetSuspensionEnrichedFunctor.map X Y =
      (Spectra.suspensionHom X.obj Y.obj).right := rfl

end SerrePositivity.KST.SConstruction
