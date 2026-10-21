module
public import SerrePositivity.KST.SConstruction.SimplicialDiagramDiagonalLaws

/-! # 元の対角実現の厳密単体的豊穣関手
概要：全 native パラメータを保持し、図式全体から元の対角単体集合へ送る。
方針：実対角作用を curry し、元の単位・合成と通常射を回収する。
規約：Kan 置換は後続。使われ方：反復実現から厳密豊穣 K への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 元の同じ対角実現を与える、標準 end からの厳密単体的豊穣関手。 -/
def simplicialSSetDiagramDiagonalEnrichedFunctor :
    EnrichedFunctor SSet.{u} SimplicialSSetDiagram.{u} SSetInternalObject.{u} where
  obj X := ⟨simplicialSSetDiagramDiagonal X⟩
  map X Y := curry (simplicialSSetDiagramDiagonalAction X Y)
  map_id X := by
    change eId SSet.{u} X ≫ curry (simplicialSSetDiagramDiagonalAction X X) =
      MonoidalClosed.id (simplicialSSetDiagramDiagonal X)
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, MonoidalClosed.id_eq,
      uncurry_curry, ← id_tensorHom]
    exact simplicialSSetDiagramDiagonalAction_unit X
  map_comp X Y Z :=
    (rightActionCurry_comp _ _ _ _ (simplicialSSetDiagramDiagonalAction_comp X Y Z)).symm

/-- 元の通常の図式射では、元の同じ対角射の curry を厳密に回収する。 -/
lemma simplicialSSetDiagramDiagonalEnrichedFunctor_hom
    {X Y : SimplicialSSetDiagram.{u}} (f : X ⟶ Y) :
    eHomEquiv SSet.{u} f ≫ simplicialSSetDiagramDiagonalEnrichedFunctor.map X Y =
      curry' (simplicialSSetDiagramDiagonalMap f) := by
  change eHomEquiv SSet.{u} f ≫ curry (simplicialSSetDiagramDiagonalAction X Y) = _
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, curry', uncurry_curry]
  simpa only [id_tensorHom] using simplicialSSetDiagramDiagonalAction_hom f

end SerrePositivity.KST.SConstruction
