module

public import SerrePositivity.KST.Spectra.EnrichedParameterCylinderTriangle
public import SerrePositivity.KST.Spectra.EndpointCircle

/-!
概要：単体的円の生成辺と、それが二対象の評価円柱に与える三角形。
方針：境界の商の生成一単体を取り、両端が実際に基点であることを商の条件で検査する。
規約：二つの長辺は同じ基点パラメータの辺。使われ方：零三角形とのホーン貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 円の基点の頂点。 -/
def circleBasepoint : PointedSimplicialSet.circle.{u}.right _⦋0⦌ :=
  SSet.unitHomEquiv _ PointedSimplicialSet.circle.hom

/-- 境界の各頂点は、円の商で実際の基点へ送られる。 -/
lemma circleQuotient_vertex (j : Fin 2) :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm j) = circleBasepoint := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (PointedObject.cofiberQuotient_condition (boundary.{u} 1).ι)
      (Opposite.op ⦋0⦌)) (intervalBoundaryVertex j)
  exact h

/-- 元の円の商写像の生成一単体で、両端は基点そのもの。 -/
def circleGeneratingEdge : PointedSimplicialSet.circle.{u}.right.Edge
    circleBasepoint circleBasepoint :=
  SSet.Edge.mk (SSet.yonedaEquiv (PointedObject.cofiberQuotient (boundary.{u} 1).ι))
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, stdSimplex.δ_one_eq_const,
        SSet.const_comp, SSet.yonedaEquiv_const]
      exact circleQuotient_vertex 0)
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, stdSimplex.δ_zero_eq_const,
        SSet.const_comp, SSet.yonedaEquiv_const]
      exact circleQuotient_vertex 1)

/-- 円の生成辺が与える、二対象の評価円柱内の coherent な三角形。 -/
def circleParameterTriangle : (Δ[2] : SSet.{max u v}) ⟶
    SimplicialNerve
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object PointedSimplicialSet.circle.{u}.right
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v}) :=
  EnrichedParameterCylinder.parameterTriangle circleGeneratingEdge

/-- 円の三角形の 1–2 辺は実際の基点評価の辺。 -/
lemma circleParameterTriangle_target :
    stdSimplex.δ (0 : Fin 3) ≫ circleParameterTriangle.{u, v} =
      EnrichedParameterCylinder.parameterEdge PointedSimplicialSet.circle.hom := by
  rw [circleParameterTriangle, EnrichedParameterCylinder.parameterTriangle_target,
    circleBasepoint, Equiv.symm_apply_apply]

/-- 円の三角形の 0–2 辺も、同じ実際の基点評価の辺。 -/
lemma circleParameterTriangle_source :
    stdSimplex.δ (1 : Fin 3) ≫ circleParameterTriangle.{u, v} =
      EnrichedParameterCylinder.parameterEdge PointedSimplicialSet.circle.hom := by
  rw [circleParameterTriangle, EnrichedParameterCylinder.parameterTriangle_source,
    circleBasepoint, Equiv.symm_apply_apply]

/-- 円の三角形の 0–1 辺は左端の恒等辺。 -/
lemma circleParameterTriangle_identity :
    stdSimplex.δ (2 : Fin 3) ≫ circleParameterTriangle.{u, v} =
      SSet.const (EnrichedParameterCylinder.leftVertex PointedSimplicialSet.circle.right) :=
  EnrichedParameterCylinder.parameterTriangle_identity circleGeneratingEdge

end SerrePositivity.KST.Spectra
