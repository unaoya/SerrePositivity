module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalCoconeValuePre

/-!
概要：元の余錐頂点と元の全空間頂点の厳密な表示変更を、Kan 値の射へ移す。
方針：既存の値比較を頂点の等式で輸送し、同じ source 値比較の式を回収する。
規約：元の表示等式を保持。使われ方：native 区間値と a6 の同じ始域での比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の値比較は、同じ頂点の等式による fiber と Kan 値の表示変更で厳密に可換。 -/
lemma pointedValueObject_transport {x y : SpaceInfinity.{u} _⦋0⦌} (h : x = y) :
    eqToHom (congrArg (vertexFiber pointedSpaceProjection) h) ≫
        (pointedSpaceFiberValueEquivalence y).hom =
      (pointedSpaceFiberValueEquivalence x).hom ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (eqToHom (congrArg (fun z => (spaceInfinityObject z).obj) h)) := by
  subst y
  simp only [eqToHom_refl, Category.id_comp]
  exact ((congrArg (fun m => (pointedSpaceFiberValueEquivalence x).hom ≫ m)
    ((SSet.uliftFunctor.{u + 1, u}).map_id (spaceInfinityObject x).obj)).trans
      (Category.comp_id _)).symm

variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 元の余錐頂点の Kan 値から元の全空間頂点の Kan 値への厳密な表示変更。 -/
def coherentColimitSourceObjectMap :
    (spaceInfinityObject (coherentDiagramTotalCocone F).vertex).obj ⟶
      (spaceInfinityObject (coherentDiagramTotalVertex F)).obj :=
  eqToHom (congrArg (fun z => (spaceInfinityObject z).obj) (coherentDiagramTotalCocone_vertex F))

/-- 元の source 値比較は、元の余錐の値比較の後で同じ Kan 値の表示を変えたもの。 -/
lemma coherentColimitSourceValueMap_eq : coherentTotalSourceValueMap F =
    (pointedSpaceFiberValueEquivalence (coherentDiagramTotalCocone F).vertex).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map (coherentColimitSourceObjectMap F) :=
  pointedValueObject_transport (coherentDiagramTotalCocone_vertex F)

end SerrePositivity.InfinityCategories.F2
