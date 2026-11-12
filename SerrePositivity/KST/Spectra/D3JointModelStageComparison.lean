module

public import SerrePositivity.KST.Spectra.D3JointUnitStageComparison

/-!
概要：指定単位を保つ共同全図式比較の角制限を、以前の実面模型比較へ厳密に戻す。
方針：同じ指定終点の回収を使い、loop 終点評価の充満忠実性で全図式の値を反映する。
規約：比較を選び直さず、全関手空間で一致を証明する。保持済み模型補正は未照合。
使われ方：二方向共同模型と既存の実面模型を、全 Hom・全単体の比較として接続する。
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

/-- 元の指定比較の終点像は、端点表示を除いて同じ指定同型そのもの。 -/
lemma d3KanLoopDiagramIsoOverTarget_target_heq :
    HEq ((d3KanLoopDiagramIsoOverTarget F g e).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) e :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm.trans
    (heq_of_eq (d3KanLoopDiagramIsoOverTarget_target F g e))

/-- 同じ指定模型比較の前合成も、同じ指定終点比較の前合成を厳密回収する。 -/
lemma d3KanLoopDiagramIsoOverTarget_precomp_target_heq (r : B ⟶ A) :
    HEq (((d3KanLoopDiagramIsoOverTarget F g e).precomp r).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) (e.precomp r) := by
  let := d3PointedKanLoopEvaluation_trivial.{u}
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsFullyFaithful.preimageNormalizedFunctorIso_precomp_postcomp_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (g ≫ d3PointedKanLoopSection) F e (d3KanCanonicalLoopFamily_target g).symm rfl r
end

/-- 元の共同端点パラメータ作用を角へ制限すると、同じ内部 Hom 作用に厳密一致。 -/
lemma d3EndpointParameterJoint_stage (k l : Fin 2) :
    lift (𝟙 PointedKanInfinity.{u})
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) ≫
      (d3PointedKanSquarePair ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram d3EndpointParameter)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj.{u} (k, l))) := by
  rw [← Category.assoc, d3PointedKanSquarePair_corner, d3ParameterDiagram_stage_map]
  rfl

/-- 指定単位を保つ共同模型の角制限の始点は、以前の同じ実面模型の始点。 -/
lemma d3EndpointParameterJointModel_stage_source (k l : Fin 2) :
    lift (𝟙 PointedKanInfinity.{u})
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) ≫
      ((d3PointedKanSquarePair ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram d3EndpointParameter)) ≫
          d3PointedKanLoopSection) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj.{u} (k, l))) ≫
      d3PointedKanLoopSection := by
  rw [← Category.assoc, d3EndpointParameterJoint_stage]

/-- 共同左模型の角制限は、以前の同じ指定実面模型比較に全図式で一致。 -/
lemma d3DoubleEndpointJointLeftUnitModelIso_face (k l : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3DoubleEndpointJointLeftUnitModelIso.{u}.precomp
      (lift (𝟙 PointedKanInfinity)
        (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))))
      (d3EndpointParameterJointModel_stage_source k l)
      (d3DoubleEndpointJointLeftLoopFamily_face k l) = d3DoubleEndpointLeftModelIso k l := by
  let := d3PointedKanLoopEvaluation_trivial.{u}
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).postcomp_functorIso_injective
  apply eq_of_heq
  refine (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  exact (d3KanLoopDiagramIsoOverTarget_precomp_target_heq _ _ _ _).trans
    ((d3DoubleEndpointJointLeftTargetIso_face k l).trans
      (d3KanLoopDiagramIsoOverTarget_target_heq _ _ _).symm)

/-- 共同右模型についても、以前の同じ全実面比較の指定値を厳密回収する。 -/
lemma d3DoubleEndpointJointRightUnitModelIso_face (k l : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3DoubleEndpointJointRightUnitModelIso.{u}.precomp
      (lift (𝟙 PointedKanInfinity)
        (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))))
      (d3EndpointParameterJointModel_stage_source k l)
      (d3DoubleEndpointJointRightLoopFamily_face k l) = d3DoubleEndpointRightModelIso k l := by
  let := d3PointedKanLoopEvaluation_trivial.{u}
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).postcomp_functorIso_injective
  apply eq_of_heq
  refine (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  exact (d3KanLoopDiagramIsoOverTarget_precomp_target_heq _ _ _ _).trans
    ((d3DoubleEndpointJointRightTargetIso_face k l).trans
      (d3KanLoopDiagramIsoOverTarget_target_heq _ _ _).symm)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
