module
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # 点つき全写像空間の成分から局所化した実射への写像
概要：基点固定写像空間の同じ連結成分は、anodyne を反転する任意の関手で同じ実射になる。
方針：各辺を元の点つき区間ホモトピーへ戻し、全成分の商へ降ろす。
規約：源・標的の Kan 性は要求しない。使われ方：suspension と span 左脚の弱同値性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra.PointedMapping SerrePositivity.SimplicialModel
open scoped Simplicial
variable {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
  (hL : anodyneExtensions.IsInvertedBy L)
include hL

/-- 元の全写像空間の辺は、戻した二つの通常射の局所化像を等しくする。 -/
lemma pointedMappingImage_edge (X Y : PointedSimplicialSet.{u})
    {v w : (PointedObject.basedHom X Y).right _⦋0⦌}
    (e : (PointedObject.basedHom X Y).right.Edge v w) :
    L.map (familyMap X Y v).right = L.map (familyMap X Y w).right := by
  have e' : (PointedObject.basedHom X Y).right.Edge
      (familyVertex (familyMap X Y v)) (familyVertex (familyMap X Y w)) := by
    simpa only [familyVertex_familyMap] using e
  exact AnodyneHomotopy.map_homotopy_eq L hL (homotopyOfEdge e')

/-- 基点固定写像の全連結成分から、同じ元の基礎射の局所化像への実写像。 -/
def pointedMappingImage (X Y : PointedSimplicialSet.{u}) :
    π₀ (PointedObject.basedHom X Y).right → (L.obj X.right ⟶ L.obj Y.right) :=
  π₀.lift (fun v => L.map (familyMap X Y v).right) (by
    intro v w e
    exact pointedMappingImage_edge L hL X Y e)

/-- 元の通常射の成分は、同じ元の基礎射の局所化像を回収する。 -/
lemma pointedMappingImage_mk {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    pointedMappingImage L hL X Y (π₀.mk (familyVertex f)) = L.map f.right := by
  change L.map (familyMap X Y (familyVertex f)).right = _
  rw [familyMap_familyVertex]

/-- 元の基点固定写像が同じ成分なら、Kan 性なしに同じ局所化像を持つ。 -/
lemma pointedMappingImage_eq_of_component {X Y : PointedSimplicialSet.{u}}
    {f g : X ⟶ Y} (h : componentOf f = componentOf g) : L.map f.right = L.map g.right := by
  have hm := congrArg (pointedMappingImage L hL X Y) h
  simpa only [componentOf, pointedMappingImage_mk] using hm

end SerrePositivity.KST.SConstruction
