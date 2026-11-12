module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeNativeCommutativity
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoChainTransport

/-!
概要：区間錐の端点を正規化する前の指定脚比較と比較先三角形。
方針：同じ全円柱の指定値を読み戻した射の表示で保つ。
規約：元の頂点は恒等比較。使われ方：切断の自然性の式への輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {X Y Z : KanObject.{u}}

/-- 概要：正規化前の置換錐への脚は通常の射影と厳密に一致する。
方針：脚の読み戻しと頂点の恒等射。規約：射の等式。使われ方：終点の輸送。 -/
lemma intervalPullbackKanCone_targetLeg_id (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    𝟙 (intervalPullbackKanObject f g) ≫
      kanNativeConeLeg (spacePullbackCone (intervalReplacementKanEndpoint f) g) _
        (intervalPullbackKanConeTarget_vertex f g) i =
      (kanPullbackCone (intervalReplacementKanEndpoint f) g).π.app i := by
  rw [intervalPullbackKanCone_targetLeg]
  exact Category.id_comp _

/-- 概要：同じ全円柱の正規化前の指定脚比較。
方針：元の上下三角形を合成。規約：指定値。使われ方：自然性の端点の輸送。 -/
def intervalPullbackConeRawLegIso (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :=
  kanConeLegComparisonIso (intervalPullbackKanConeHomotopy f g) _ _
    ((intervalPullbackCone_vertex f g).trans (spaceInfinityVertex_eq_coherent _))
    (intervalPullbackKanConeTarget_vertex f g) (𝟙 (intervalPullbackKanObject f g))
    (intervalPullbackConeHomotopy_apexEdge f g) i

/-- 概要：比較先の元の三角形を恒等頂点で前合成した指定値。
方針：strict 錐の二単体。規約：元の値。使われ方：自然性の終域の輸送。 -/
def intervalPullbackConeRawTargetIso (f : X ⟶ Y) (g : Z ⟶ Y)
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :=
  (kanNativeConeTriangleIso (spacePullbackCone (intervalReplacementKanEndpoint f) g) _
    (intervalPullbackKanConeTarget_vertex f g) a).precomp
      (𝟙 (intervalPullbackKanObject f g).obj)

/-- 概要：正規化前の指定脚比較の自然性。
方針：三つの四面体の合成則。規約：元の値。使われ方：strict な自然性への輸送。 -/
lemma intervalPullbackConeRawLegIso_naturality (f : X ⟶ Y) (g : Z ⟶ Y)
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    (intervalPullbackConeTriangleIso f g a).postcomp
        (kanConeDiagramComponent (intervalPullbackKanConeHomotopy f g) j) ≪≫
      (kanConeDiagramComparisonIso (intervalPullbackKanConeHomotopy f g) a).precomp
        (show (intervalPullbackKanObject f g).obj ⟶ ((kanPullbackDiagram f g).obj i).obj from
          intervalPullbackConeKanLeg f g i) ≪≫
      (intervalPullbackConeRawLegIso f g i).postcomp
        ((kanPullbackDiagram (intervalReplacementKanEndpoint f) g).map a) =
    intervalPullbackConeRawLegIso f g j ≪≫ intervalPullbackConeRawTargetIso f g a :=
  kanConeLegComparisonIso_naturality (intervalPullbackKanConeHomotopy f g) _ _
    ((intervalPullbackCone_vertex f g).trans (spaceInfinityVertex_eq_coherent _))
    (intervalPullbackKanConeTarget_vertex f g) (𝟙 (intervalPullbackKanObject f g))
    (intervalPullbackConeHomotopy_apexEdge f g) a

end SerrePositivity.InfinityCategories.F2
