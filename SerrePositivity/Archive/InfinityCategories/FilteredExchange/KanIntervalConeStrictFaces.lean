module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeRawComparison

/-!
概要：区間錐の指定自然性に現れる二つの strict な面を元の等式へ輸送する。
方針：定値な三角形の指定同型と成分・射影の厳密な同定。
規約：型を含む元の値を保持。使われ方：切断・通常の錐の自然性による表示。
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

/-- 概要：元の図式面の指定値は切断の自然性等式からの同型。
方針：成分を元の切断へ移す。規約：型付きの一致。使われ方：中央の strict な面。 -/
lemma intervalPullbackConeDiagramPreIso_heq (f : X ⟶ Y) (g : Z ⟶ Y)
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    HEq (functorEqIso (congrArg
      (fun k => (show (intervalPullbackKanObject f g).obj ⟶
        ((kanPullbackDiagram f g).obj i).obj from intervalPullbackConeKanLeg f g i) ≫ k)
      ((intervalCospanSection f g).naturality a)))
      ((kanConeDiagramComparisonIso (intervalPullbackKanConeHomotopy f g) a).precomp
        (show (intervalPullbackKanObject f g).obj ⟶ ((kanPullbackDiagram f g).obj i).obj from
          intervalPullbackConeKanLeg f g i)) := by
  apply functorEqIso_heq_of_isFunctorEqIso _
    ((intervalPullbackKanCone_diagramComparison_isFunctorEqIso f g a).precomp
      (show (intervalPullbackKanObject f g).obj ⟶ ((kanPullbackDiagram f g).obj i).obj from
        intervalPullbackConeKanLeg f g i))
  · rw [intervalPullbackKanCone_component]
    rfl
  · rw [intervalPullbackKanCone_component]
    rfl

/-- 概要：元の比較先の錐面の指定値は通常の錐の可換等式からの同型。
方針：元の射影を保ち恒等頂点を消す。規約：型付きの一致。使われ方：終域の面。 -/
lemma intervalPullbackConeTargetIso_heq (f : X ⟶ Y) (g : Z ⟶ Y)
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    HEq (functorEqIso ((kanPullbackCone (intervalReplacementKanEndpoint f) g).w a).symm)
      (intervalPullbackConeRawTargetIso f g a) := by
  apply functorEqIso_heq_of_isFunctorEqIso _
    ((intervalPullbackKanCone_targetTriangle_isFunctorEqIso f g a).precomp
      (𝟙 (intervalPullbackKanObject f g).obj))
  · exact intervalPullbackKanCone_targetLeg_id f g j
  · change (𝟙 (intervalPullbackKanObject f g) ≫
      kanNativeConeLeg (spacePullbackCone (intervalReplacementKanEndpoint f) g) _
        (intervalPullbackKanConeTarget_vertex f g) i) ≫
          (kanPullbackDiagram (intervalReplacementKanEndpoint f) g).map a = _
    rw [intervalPullbackKanCone_targetLeg_id]

end SerrePositivity.InfinityCategories.F2
