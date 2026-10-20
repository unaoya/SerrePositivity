module

public import SerrePositivity.InfinityCategories.F2.KanIntervalConeReadback
public import SerrePositivity.InfinityCategories.F2.SpaceTriangleConstantFaces
public import SerrePositivity.InfinityCategories.F2.KanConeNatTransComparison

/-!
概要：区間引き戻しの脚と切断の合成を元の置換錐の射影へ指定同型で比較する。
方針：同じ全円柱の上下三角形を合成し、成分・射影の厳密な式で端点を戻す。
規約：存在命題から比較を選び直さない。使われ方：元の区間 path の二次の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {X Y Z : KanObject.{u}}

/-- 概要：同じ全錐円柱から元の脚と切断の合成を置換錐の射影へ比較する。
方針：指定上下三角形を合成して両端だけ輸送。
規約：元の指定同型の値を保持。使われ方：二射影と指定 path の同時照合。 -/
def intervalPullbackConeLegSectionIso (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    FunctorIso (intervalPullbackConeKanLeg f g i ≫ (intervalCospanSection f g).app i)
      ((kanPullbackCone (intervalReplacementKanEndpoint f) g).π.app i) :=
  functorIsoOfEq
    (kanConeLegComparisonIso (intervalPullbackKanConeHomotopy f g) _ _
      ((intervalPullbackCone_vertex f g).trans (spaceInfinityVertex_eq_coherent _))
      (intervalPullbackKanConeTarget_vertex f g) (𝟙 (intervalPullbackKanObject f g))
      (intervalPullbackConeHomotopy_apexEdge f g) i)
    (by
      change intervalPullbackConeKanLeg f g i ≫
        kanConeDiagramComponent (intervalPullbackKanConeHomotopy f g) i = _
      rw [intervalPullbackKanCone_component]
      rfl)
    (by
      rw [intervalPullbackKanCone_targetLeg]
      exact Category.id_comp _)

/-- 概要：端点の正規化は元の全円柱の脚比較の指定値を保持する。
方針：端点の等式の輸送。規約：型付きの一致。使われ方：元の三角形の自然性。 -/
lemma intervalPullbackConeLegSectionIso_heq (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    HEq (intervalPullbackConeLegSectionIso f g i)
      (kanConeLegComparisonIso (intervalPullbackKanConeHomotopy f g) _ _
        ((intervalPullbackCone_vertex f g).trans (spaceInfinityVertex_eq_coherent _))
        (intervalPullbackKanConeTarget_vertex f g) (𝟙 (intervalPullbackKanObject f g))
        (intervalPullbackConeHomotopy_apexEdge f g) i) :=
  functorIsoOfEq_heq _ _ _

/-- 概要：置換錐の元の指定三角形の同型は通常の錐の等式から来る。
方針：strict 錐の豊穣精密化は定値。規約：指定二単体。使われ方：自然性の簡約。 -/
lemma intervalPullbackKanCone_targetTriangle_isFunctorEqIso (f : X ⟶ Y) (g : Z ⟶ Y)
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    IsFunctorEqIso (kanNativeConeTriangleIso
      (spacePullbackCone (intervalReplacementKanEndpoint f) g) _
      (intervalPullbackKanConeTarget_vertex f g) a) := by
  apply isFunctorEqIso_spaceInfinityTriangleIso_of_faces
  exact isConstantCoherentTriangle_strictCone
    (kanPullbackCone (intervalReplacementKanEndpoint f) g) (ULift.up (nerve.edgeMk a).edge)

/-- 概要：元の図式の二次比較は切断の自然性等式から来る同型。
方針：元の strict な切断円柱を評価。規約：指定値。使われ方：自然性の簡約。 -/
lemma intervalPullbackKanCone_diagramComparison_isFunctorEqIso (f : X ⟶ Y) (g : Z ⟶ Y)
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    IsFunctorEqIso (kanConeDiagramComparisonIso (intervalPullbackKanConeHomotopy f g) a) :=
  kanConeDiagramComparisonIso_natTrans_isFunctorEqIso (intervalPullbackKanConeHomotopy f g)
    (intervalCospanSection f g) (intervalPullbackConeHomotopy_diagram f g) a

end SerrePositivity.InfinityCategories.F2
