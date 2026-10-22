module
public import SerrePositivity.KST.SConstruction.PointedTensorCylinderCurry
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-! # 同じ実円柱の両端を結ぶ基点固定ホモトピー
概要：任意の元の円柱射の両端は、同じ実写像空間の辺と基点固定ホモトピーで結ばれる。
方針：同じ閉 curry の区間族の両面を元のパラメータ族と照合する。
規約：標的の Kan 性は不要。使われ方：BF 構造射と原組み立ての随伴比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra.PointedMapping
open scoped Simplicial

/-- 同じ元の区間族の始点は、元の零端の点つき射のパラメータ族。 -/
lemma pointedTensorCylinderFamily_zero {X Y : PointedSimplicialSet.{u}}
    (h : pointedTensorInterval.{u} ⊗ X ⟶ Y) :
    stdSimplex.δ (1 : Fin 2) ≫ pointedTensorCylinderFamily h =
      pointFamily (pointedTensorCylinderEndMap 0 X ≫ h) := by
  have hd : stdSimplex.δ (1 : Fin 2) = PointedSimplicialSet.deltaZeroUnitIso.hom ≫
      SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm 0) := by
    rw [stdSimplex.δ_one_eq_const, SSet.comp_const]
  rw [hd, Category.assoc]
  erw [pointedTensorCylinderFamily_end, pointFamily_closed]

/-- 同じ元の区間族の終点は、元の一端の点つき射のパラメータ族。 -/
lemma pointedTensorCylinderFamily_one {X Y : PointedSimplicialSet.{u}}
    (h : pointedTensorInterval.{u} ⊗ X ⟶ Y) :
    stdSimplex.δ (0 : Fin 2) ≫ pointedTensorCylinderFamily h =
      pointFamily (pointedTensorCylinderEndMap 1 X ≫ h) := by
  have hd : stdSimplex.δ (0 : Fin 2) = PointedSimplicialSet.deltaZeroUnitIso.hom ≫
      SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm 1) := by
    rw [stdSimplex.δ_zero_eq_const, SSet.comp_const]
  rw [hd, Category.assoc]
  erw [pointedTensorCylinderFamily_end, pointFamily_closed]

/-- 同じ実円柱の両端の点つき射を結ぶ、元の全写像空間の実際の辺。 -/
def pointedTensorCylinderEdge {X Y : PointedSimplicialSet.{u}}
    (h : pointedTensorInterval.{u} ⊗ X ⟶ Y) :
    (PointedObject.basedHom X Y).right.Edge
      (familyVertex (pointedTensorCylinderEndMap 0 X ≫ h))
      (familyVertex (pointedTensorCylinderEndMap 1 X ≫ h)) :=
  SSet.Edge.mk (SSet.yonedaEquiv (pointedTensorCylinderFamily h))
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, pointedTensorCylinderFamily_zero]; rfl)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, pointedTensorCylinderFamily_one]; rfl)

/-- 同じ元の円柱の両端を結ぶ実際のホモトピー。 -/
def pointedTensorCylinderHomotopy {X Y : PointedSimplicialSet.{u}}
    (h : pointedTensorInterval.{u} ⊗ X ⟶ Y) :
    SSet.Homotopy (pointedTensorCylinderEndMap 0 X ≫ h).right
      (pointedTensorCylinderEndMap 1 X ≫ h).right :=
  homotopyOfEdge (pointedTensorCylinderEdge h)

/-- 同じ円柱のホモトピーは、元の基点を全区間で固定する。 -/
lemma pointedTensorCylinderHomotopy_base {X Y : PointedSimplicialSet.{u}}
    (h : pointedTensorInterval.{u} ⊗ X ⟶ Y) :
    X.hom ▷ (Δ[1] : SSet.{u}) ≫ (pointedTensorCylinderHomotopy h).h =
      CartesianMonoidalCategory.toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom :=
  homotopyOfEdge_base (pointedTensorCylinderEdge h)

/-- 同じ元の実円柱の両端は、元の点つき写像空間で同じ成分。 -/
lemma pointedTensorCylinderEnd_component {X Y : PointedSimplicialSet.{u}}
    (h : pointedTensorInterval.{u} ⊗ X ⟶ Y) :
    componentOf (pointedTensorCylinderEndMap 0 X ≫ h) =
      componentOf (pointedTensorCylinderEndMap 1 X ≫ h) :=
  π₀.sound (pointedTensorCylinderEdge h)

end SerrePositivity.KST.SConstruction
