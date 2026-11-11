module
public import SerrePositivity.KST.SConstruction.PointedLoopEnrichment
public import SerrePositivity.KST.SConstruction.PointedSSetObject

/-! # 同じ loop の標準点つき厳密豊穣関手
概要：元の circle 内部 Hom を標準点つき対象上の厳密豊穣関手として保持する。
方針：元の全 basedHom 作用と検証済みの単位・合成則を同じ対象型へ移す。
規約：大域 instance を変更しない。使われ方：BF の零段 ΩB₀。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra

/-- 元の loop 対象と全 Hom を持つ、標準点つき厳密豊穣関手。 -/
def pointedStandardLoopEnrichedFunctor :
    EnrichedFunctor SSet.{u} PointedSSetObject.{u} PointedSSetObject.{u} where
  obj X := ⟨_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X.obj⟩
  map X Y := (pointedLoopHom X.obj Y.obj).right
  map_id X := pointedLoopHom_simplicial_id X.obj
  map_comp X Y Z := pointedLoopHom_simplicial_comp X.obj Y.obj Z.obj

/-- 同じ元の通常射の loop を、標準点つき対象の射として保持する。 -/
def pointedStandardLoopMap {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    pointedStandardLoopEnrichedFunctor.obj X ⟶ pointedStandardLoopEnrichedFunctor.obj Y :=
  (ihom PointedSimplicialSet.circle.{u}).map (show X.obj ⟶ Y.obj from f)

/-- 通常射では、全 Hom 作用が元の同じ loop 射を厳密に回収する。 -/
lemma pointedStandardLoopEnrichedFunctor_hom {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    eHomEquiv SSet f ≫ pointedStandardLoopEnrichedFunctor.map X Y =
      eHomEquiv SSet (pointedStandardLoopMap f) := by
  apply ((PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X.obj) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj)).right.unitHomEquiv).injective
  exact pointedLoopHom_vertex (show X.obj ⟶ Y.obj from f)

end SerrePositivity.KST.SConstruction
