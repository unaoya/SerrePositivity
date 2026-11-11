module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.CompositionTriangleSpace
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.TriangleBoundaryGluing

/-!
概要：指定した三辺を、そのまま三角形の境界へ貼る。
方針：既存の二辺のホーンと境界の pushout を使い、三面と最後の頂点を照合する。
規約：三辺を変更しない。使われ方：部分極限間の比較三角形の相対充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X : SSet.{u}} {x y z : X _⦋0⦌}
  (e : X.Edge x y) (f : X.Edge y z) (g : X.Edge x z)

/-- 指定した前辺・後辺・対角辺を三角形の境界へ貼った元の図式。 -/
def specifiedEdgeTriangleBoundary : (boundary 2 : SSet.{u}) ⟶ X :=
  triangleBoundaryDiagram (composableEdgeHorn e f) (SSet.yonedaEquiv.symm g.edge) (by
    rw [composableEdgeHorn_first]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact g.src_eq.trans e.src_eq.symm) (by
    rw [composableEdgeHorn_last]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact g.tgt_eq.trans f.tgt_eq.symm)

/-- 第 0 面は元の後辺。 -/
lemma specifiedEdgeTriangleBoundary_zero :
    boundary.ι (0 : Fin 3) ≫ specifiedEdgeTriangleBoundary e f g =
      SSet.yonedaEquiv.symm f.edge := by
  rw [specifiedEdgeTriangleBoundary, triangleBoundaryDiagram_face_zero, composableEdgeHorn_last]

/-- 第 1 面は元の指定対角辺。 -/
lemma specifiedEdgeTriangleBoundary_one :
    boundary.ι (1 : Fin 3) ≫ specifiedEdgeTriangleBoundary e f g =
      SSet.yonedaEquiv.symm g.edge := triangleBoundaryDiagram_face_one _ _ _ _

/-- 第 2 面は元の前辺。 -/
lemma specifiedEdgeTriangleBoundary_two :
    boundary.ι (2 : Fin 3) ≫ specifiedEdgeTriangleBoundary e f g =
      SSet.yonedaEquiv.symm e.edge := by
  rw [specifiedEdgeTriangleBoundary, triangleBoundaryDiagram_face_two, composableEdgeHorn_first]

/-- 貼った境界の最後の頂点は元の共通終点。 -/
lemma specifiedEdgeTriangleBoundary_last :
    boundaryVertex 1 (Fin.last 2) ≫ specifiedEdgeTriangleBoundary e f g =
      SSet.yonedaEquiv.symm z := by
  have hv : boundaryVertex.{u} 1 (Fin.last 2) =
      stdSimplex.δ (0 : Fin 2) ≫ boundary.ι (0 : Fin 3) := by
    apply (cancel_mono (boundary 2).ι).1
    apply SSet.yonedaEquiv.injective
    decide
  rw [hv, Category.assoc, specifiedEdgeTriangleBoundary_zero]
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact f.tgt_eq

end SerrePositivity.InfinityCategories.F2
