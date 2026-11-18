module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DiagramDerivedVertex
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DerivedNatTransIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.HomotopyEvaluationEndpointTransport

/-!
# 元の通常複体自然変換の全二胞体と同じ成分辺

概要：同じ全円柱の二胞体の頂点評価を、元の成分射の導来像へ照合する。
方針：元の図式頂点の零単体輸送と元の全円柱の成分式を使う。
規約：二胞体・成分射・端点等式を保つ。
使われ方：元の導来単位の全族公式への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] {I : Type (u + 1)} [Category.{u} I]
  {F G : I ⥤ Complex A} (η : F ⟶ G)

def complexOrdinaryDerivedNatTransHom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
    (nerveMap F ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) (nerveMap G ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) :=
  Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHomotopy A η))

lemma complexOrdinaryDerivedNatTransHom_component (i : I) :
    (_root_.SerrePositivity.ComplexLimits.complexDiagramDerivedVertexIso A F i).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A η) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) ≫
      (_root_.SerrePositivity.ComplexLimits.complexDiagramDerivedVertexIso A G i).hom =
    Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk (η.app i)).map (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated := by
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomEvaluate_homotopy_transport
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHomotopy A η) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)
    (_root_.SerrePositivity.ComplexLimits.complexDiagramDerived_vertex A F i) (_root_.SerrePositivity.ComplexLimits.complexDiagramDerived_vertex A G i)
    ((nerve.edgeMk (η.app i)).map (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHomotopy_component A η i)

end SerrePositivity.ComplexLimits
