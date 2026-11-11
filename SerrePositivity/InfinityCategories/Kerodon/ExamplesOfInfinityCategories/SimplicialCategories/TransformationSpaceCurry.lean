module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.EndpointPairDiagramTensorCurry
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.EndpointPairTransformationIso

/-!
概要：積の底上の coherent な変換の比較を元の底上の変換の族の関手同型へ移す。
方針：固定境界図式の厳密な同型を経由して族を curry する。
規約：同型はパラメーター空間全体にわたる。
使われ方：表現空間の比較から写像空間比較の左逆の整合性へ戻す。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：積の底上の変換空間から元の底の変換空間への関手の空間への射。
方針：固定境界図式へ戻してパラメーターを curry する。
規約：底とパラメーターは任意。
使われ方：変換空間内の同型を族の同型へ写す。 -/
def coherentTransformationSpaceCurry (B K : SSet.{u + 1}) (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace (fst B K ≫ F) (fst B K ≫ G) ⟶
      (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.transformationEndpointPairDiagramMap (fst B K ≫ F) (fst B K ≫ G) ≫
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.endpointPairDiagramTensorCurry B K F G

/-- 概要：変換空間の curry は頂点で実際の prism の族の curry を回収する。
方針：固定境界の図式へ戻す頂点公式と積の図式の頂点公式を使う。
規約：両端と全体の図式を厳密に保持する。
使われ方：具体的な二つの変換の族を同定する。 -/
lemma coherentTransformationSpaceCurry_vertex {B K : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (B ⊗ K) ≫ H = fst B K ≫ F)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (B ⊗ K) ≫ H = fst B K ≫ G)
    (hH : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair (B ⊗ K) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G)) :
    (coherentTransformationSpaceCurry B K F G).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorEdgeFromPrism H h₀ h₁)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.coherentTransformationFamilyCurry F G H h₀ h₁) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.endpointPairDiagramTensorCurry B K F G).app _
    ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.transformationEndpointPairDiagramMap (fst B K ≫ F) (fst B K ≫ G)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorEdgeFromPrism H h₀ h₁))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.transformationEndpointPairDiagramMap_vertex _ _ H h₀ h₁ hH,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.endpointPairDiagramTensorCurry_vertex F G H h₀ h₁ hH]

/-- 概要：積の底上の二つの変換の同型はパラメーター族全体の関手同型を与える。
方針：変換空間の curry で同型を写して二つの頂点公式で回収する。
規約：各パラメーターで別々に選択しない。
使われ方：写像空間比較の左逆の関手同型。 -/
def coherentTransformationFamilyIsoOfSpaceIso {B K : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (H H' : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (B ⊗ K) ≫ H = fst B K ≫ F)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (B ⊗ K) ≫ H = fst B K ≫ G)
    (h₀' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (B ⊗ K) ≫ H' = fst B K ≫ F)
    (h₁' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (B ⊗ K) ≫ H' = fst B K ≫ G)
    (hH : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair (B ⊗ K) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G))
    (hH' : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair (B ⊗ K) ≫ H' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorEdgeFromPrism H h₀ h₁))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorEdgeFromPrism H' h₀' h₁'))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.coherentTransformationFamilyCurry F G H h₀ h₁)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.coherentTransformationFamilyCurry F G H' h₀' h₁') := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (coherentTransformationSpaceCurry B K F G)
  have er := coherentTransformationSpaceCurry_vertex F G H h₀ h₁ hH
  have et := coherentTransformationSpaceCurry_vertex F G H' h₀' h₁' hH'
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk er)).symm ≪≫ h ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk et)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
