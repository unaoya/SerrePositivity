module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoChainTransport

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeStrictFaces

/-!
概要：区間錐の指定脚比較の自然性を元の切断と通常の錐の可換等式で表示する。
方針：五端点と二つの strict な面の指定同型を同時に輸送する。
規約：元の三角形と全円柱の比較を保持。使われ方：元の path の最終整合。
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

/-- 概要：元の指定脚比較は切断の自然性・通常の錐の等式に対して整合。
方針：三整合式からの自然性と strict な二面の指定値を輸送。
規約：指定された同型の合成の等式。使われ方：二射影と元の path の同時照合。 -/
lemma intervalPullbackConeLegSectionIso_strict_naturality (f : X ⟶ Y) (g : Z ⟶ Y)
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    (intervalPullbackConeTriangleIso f g a).postcomp ((intervalCospanSection f g).app j) ≪≫
      functorEqIso (congrArg
        (fun k => (show (intervalPullbackKanObject f g).obj ⟶
          ((kanPullbackDiagram f g).obj i).obj from intervalPullbackConeKanLeg f g i) ≫ k)
        ((intervalCospanSection f g).naturality a)) ≪≫
      (intervalPullbackConeLegSectionIso f g i).postcomp
        ((kanPullbackDiagram (intervalReplacementKanEndpoint f) g).map a) =
    intervalPullbackConeLegSectionIso f g j ≪≫
      functorEqIso ((kanPullbackCone (intervalReplacementKanEndpoint f) g).w a).symm := by
  refine functorIso_chain_transport
    ((intervalPullbackConeTriangleIso f g a).postcomp
      (kanConeDiagramComponent (intervalPullbackKanConeHomotopy f g) j))
    ((kanConeDiagramComparisonIso (intervalPullbackKanConeHomotopy f g) a).precomp
      (show (intervalPullbackKanObject f g).obj ⟶ ((kanPullbackDiagram f g).obj i).obj from
        intervalPullbackConeKanLeg f g i))
    ((intervalPullbackConeRawLegIso f g i).postcomp
      ((kanPullbackDiagram (intervalReplacementKanEndpoint f) g).map a))
    (intervalPullbackConeRawLegIso f g j) (intervalPullbackConeRawTargetIso f g a)
    _ _ _ _ _ (intervalPullbackConeRawLegIso_naturality f g a)
    ?_ ?_ ?_ ?_ ?_
    (functorIso_postcomp_heq_of_map_eq _ (intervalPullbackKanCone_component f g j))
    (intervalPullbackConeDiagramPreIso_heq f g a) ?_
    (intervalPullbackConeLegSectionIso_heq f g j) (intervalPullbackConeTargetIso_heq f g a)
  · rw [intervalPullbackKanCone_component]
  · rw [intervalPullbackKanCone_component]
  · rw [intervalPullbackKanCone_component]
    rfl
  · change (𝟙 (intervalPullbackKanObject f g) ≫
      kanNativeConeLeg (spacePullbackCone (intervalReplacementKanEndpoint f) g) _
        (intervalPullbackKanConeTarget_vertex f g) i) ≫
          (kanPullbackDiagram (intervalReplacementKanEndpoint f) g).map a = _
    rw [intervalPullbackKanCone_targetLeg_id]
    rfl
  · exact intervalPullbackKanCone_targetLeg_id f g j
  · apply functorIso_postcomp_heq_of_heq _ _ _ _
      (intervalPullbackConeLegSectionIso_heq f g i)
    · rw [intervalPullbackKanCone_component]
      rfl
    · exact intervalPullbackKanCone_targetLeg_id f g i

end SerrePositivity.InfinityCategories.F2
