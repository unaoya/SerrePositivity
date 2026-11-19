module

public import SerrePositivity.KST.Spectra.D3CurryEvaluationProjection
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoPastingTransport

/-!
概要：共同模型の指定始点比較を角へ制限し、以前の同じ実面始点比較を回収する。
方針：元の厳密切断の始点表示と、全模型比較の角制限を値を保って貼り合わせる。
規約：全関手空間で比較し、成分ごとの自由な選択で代用しない。
使われ方：二方向比較の指定単位三角形を、元の実面模型へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

section
variable {A B : SSet.{u + 1}} (F : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity.{u})
  (g : A ⟶ PointedKanInfinity.{u})
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
  (r : B ⟶ A) (F' : B ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity.{u})
  (g' : B ⟶ PointedKanInfinity.{u})
  (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g' (F' ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
  (hg : r ≫ g = g') (hF : r ≫ F = F')
  (hmodel : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3KanLoopDiagramIsoOverTarget F g e).precomp r)
    (by rw [← Category.assoc, hg]) hF = d3KanLoopDiagramIsoOverTarget F' g' e')

include hg hF hmodel in
/-- 指定全模型比較の制限が一致すれば、同じ始点表示との貼合せの制限も一致する。 -/
lemma d3KanLoopDiagramSourceIsoOverTarget_precomp_heq :
    HEq ((d3KanLoopDiagramSourceIsoOverTarget F g e).precomp r)
      (d3KanLoopDiagramSourceIsoOverTarget F' g' e') := by
  have he := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIso_precomp_precomp_heq d3PointedKanLoopSection_sourceIso g r).trans
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq d3PointedKanLoopSection_sourceIso hg)
  have hm := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq_of_eq _ _ _ _ hmodel
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)).symm
  have hd := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_precomp_heq
    (d3KanLoopDiagramIsoOverTarget F g e)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) (Category.assoc _ _ _) rfl r).trans
      (hm.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ (Category.assoc _ _ _) rfl).symm)
  unfold d3KanLoopDiagramSourceIsoOverTarget
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans]
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq
    (by rw [← Category.assoc, hg])
    (by simpa only [Category.assoc] using (congrArg
          (fun m ↦ (m ≫ d3PointedKanLoopSection) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)
          hg.symm))
    (by rw [← Category.assoc, hF]) _ _ _ _ he hd
end

/-- 元の共同左始点比較の角制限は、以前の同じ左実面始点比較そのもの。 -/
lemma d3DoubleEndpointJointLeftSourceIso_face (k l : Fin 2) :
    HEq (d3DoubleEndpointJointLeftSourceIso.{u}.precomp
      (lift (𝟙 PointedKanInfinity)
        (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))))
      (d3DoubleEndpointLeftSourceIso k l) := by
  have h := d3KanLoopDiagramSourceIsoOverTarget_precomp_heq
    d3DoubleEndpointJointLeftLoopFamily _ d3DoubleEndpointJointLeftTargetIso
    (lift (𝟙 PointedKanInfinity)
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)))
    (d3DoubleEndpointLeftLoopFamily k l) _ (d3DoubleEndpointLeftTargetIso k l)
    (d3EndpointParameterJoint_stage k l) (d3DoubleEndpointJointLeftLoopFamily_face k l)
    (d3DoubleEndpointJointLeftUnitModelIso_face k l)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ rfl
    (d3DoubleEndpointLeftLoopFamily_corner k l 0 0)).symm

/-- 共同右始点比較も、以前の同じ右実面始点比較の指定値を保持する。 -/
lemma d3DoubleEndpointJointRightSourceIso_face (k l : Fin 2) :
    HEq (d3DoubleEndpointJointRightSourceIso.{u}.precomp
      (lift (𝟙 PointedKanInfinity)
        (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))))
      (d3DoubleEndpointRightSourceIso k l) := by
  have h := d3KanLoopDiagramSourceIsoOverTarget_precomp_heq
    d3DoubleEndpointJointRightLoopFamily _ d3DoubleEndpointJointRightTargetIso
    (lift (𝟙 PointedKanInfinity)
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)))
    (d3DoubleEndpointRightLoopFamily k l) _ (d3DoubleEndpointRightTargetIso k l)
    (d3EndpointParameterJoint_stage k l) (d3DoubleEndpointJointRightLoopFamily_face k l)
    (d3DoubleEndpointJointRightUnitModelIso_face k l)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ rfl
    (d3DoubleEndpointRightLoopFamily_corner k l 0 0)).symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
