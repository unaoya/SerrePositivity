module
public import SerrePositivity.KST.SConstruction.PointedSSetSuspensionFunctor
public import SerrePositivity.KST.SConstruction.PointedSuspensionCoherentDiagram

/-! # 標準点つき suspension 豊穣関手の元の通常射の回収
概要：全写像空間への suspension 作用が、同じ元の通常の suspension 射を回収する。
方針：単位からの射を零単体で検出し、元の頂点の回収式を使う。
規約：元の円を固定する。使われ方：隣接段 span の左脚の実成分。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 通常の点つき射では、同じ元の円との suspension 射を全 Hom 作用から回収する。 -/
lemma pointedSSetSuspensionEnrichedFunctor_hom {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    eHomEquiv SSet f ≫ pointedSSetSuspensionEnrichedFunctor.map X Y =
      eHomEquiv SSet (pointedSSetSuspensionMap f) := by
  apply ((PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y.obj)).right.unitHomEquiv).injective
  exact suspensionHom_vertex (show X.obj ⟶ Y.obj from f)

end SerrePositivity.KST.SConstruction
