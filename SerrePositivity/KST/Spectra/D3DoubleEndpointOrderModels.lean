module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointOrderFaces

/-!
概要：全四次元比較の各実面で、保持した左右模型・始点表示の同じ指定値を回収する。
方針：元の指定終点比較を終点評価の充満忠実性で反映し、同じ切断単位を貼る。
規約：模型・単位を選び直さない。使われ方：保持した補正の四次元始点作用への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 同じ外側面比較を左指定模型へ貼ると、元の同じ右指定模型比較を回収する。 -/
lemma d3DoubleEndpointOrderFaceIso_model (i j : Fin 2) :
    d3DoubleEndpointLeftModelIso.{u} i j ≪≫ d3DoubleEndpointOrderFaceIso i j =
      d3DoubleEndpointRightModelIso i j := by
  let := d3PointedKanLoopEvaluation_trivial.{u}
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).postcomp_functorIso_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans]
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq
    (d3KanCanonicalLoopFamily_target
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj.{u} (i, j))))).symm rfl rfl
    (d3DoubleEndpointLeftTargetIso i j)
    ((d3DoubleEndpointLeftTargetIso i j).symm ≪≫ d3DoubleEndpointRightTargetIso i j)
    ((d3DoubleEndpointLeftModelIso i j).postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
    ((d3DoubleEndpointOrderFaceIso i j).postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
    (d3KanLoopDiagramIsoOverTarget_target_heq _ _ _) (d3DoubleEndpointOrderFaceIso_target i j)
  rw [Iso.self_symm_id_assoc] at h
  exact eq_of_heq (h.trans (d3KanLoopDiagramIsoOverTarget_target_heq _ _ _).symm)

/-- 同じ外側面比較の始点を、元の左右テンソル実面の厳密表示へ揃える。 -/
def d3DoubleEndpointOrderFaceSourceIso (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom
      (endpointCircle.{u} ⊗ d3EndpointParameterObj (i, j))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom
        (d3EndpointParameterObj (i, j) ⊗ endpointCircle))) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3DoubleEndpointOrderFaceIso i j).postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (d3DoubleEndpointLeftLoopFamily_corner i j 0 0)
    (d3DoubleEndpointRightLoopFamily_corner i j 0 0)

private lemma source_pasting (i j : Fin 2) :
    d3KanLoopDiagramSourceIsoOverTarget (d3DoubleEndpointLeftLoopFamily.{u} i j) _
      (d3DoubleEndpointLeftTargetIso i j) ≪≫
      (d3DoubleEndpointOrderFaceIso i j).postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    d3KanLoopDiagramSourceIsoOverTarget (d3DoubleEndpointRightLoopFamily i j) _
      (d3DoubleEndpointRightTargetIso i j) := by
  have hm := congrArg (fun e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)) (d3DoubleEndpointOrderFaceIso_model.{u} i j)
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans] at hm
  have ht := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq (Category.assoc _ _ _) rfl rfl
    ((d3DoubleEndpointLeftModelIso i j).postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    ((d3DoubleEndpointOrderFaceIso i j).postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3DoubleEndpointLeftModelIso i j).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)) (Category.assoc _ _ _) rfl)
    ((d3DoubleEndpointOrderFaceIso i j).postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _) (HEq.rfl)
  have hn := eq_of_heq (ht.trans ((heq_of_eq hm).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq
    ((d3DoubleEndpointRightModelIso i j).postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (Category.assoc _ _ _) rfl).symm))
  exact (Iso.trans_assoc _ _ _).trans
    (congrArg (fun e ↦ d3PointedKanLoopSection_sourceIso.precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj.{u} (i, j)))) ≪≫ e) hn)

/-- 全四次元比較の同じ始点面を貼ると、元の左右始点表示の同じ指定値が一致する。 -/
lemma d3DoubleEndpointOrderFaceSourceIso_pasting (i j : Fin 2) :
    d3DoubleEndpointLeftSourceIso.{u} i j ≪≫ d3DoubleEndpointOrderFaceSourceIso i j =
      d3DoubleEndpointRightSourceIso i j := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq rfl
    (d3DoubleEndpointLeftLoopFamily_corner i j 0 0)
    (d3DoubleEndpointRightLoopFamily_corner i j 0 0)
    (d3KanLoopDiagramSourceIsoOverTarget (d3DoubleEndpointLeftLoopFamily i j) _
      (d3DoubleEndpointLeftTargetIso i j))
    ((d3DoubleEndpointOrderFaceIso i j).postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (d3DoubleEndpointLeftSourceIso i j) (d3DoubleEndpointOrderFaceSourceIso i j)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)
  rw [source_pasting] at h
  exact eq_of_heq (h.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
