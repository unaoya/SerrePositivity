module

public import SerrePositivity.EInfinity.ComplexLimits.DiagramDerivedVertex
public import SerrePositivity.EInfinity.ComplexLimits.DerivedNatTransIso
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] {I : Type (u + 1)} [Category.{u} I]
  {F G : I ⥤ Complex A} (η : F ⟶ G)

def complexOrdinaryDerivedNatTransHom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
    (nerveMap F ≫ complexOrdinaryDerivedSource A) (nerveMap G ≫ complexOrdinaryDerivedSource A) :=
  Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (complexOrdinaryDerivedNatTransHomotopy A η))

lemma complexOrdinaryDerivedNatTransHom_component (i : I) :
    (complexDiagramDerivedVertexIso A F i).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (complexOrdinaryDerivedNatTransHom A η) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) ≫
      (complexDiagramDerivedVertexIso A G i).hom =
    Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk (η.app i)).map (complexOrdinaryDerivedSource A)).toTruncated := by
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomEvaluate_homotopy_transport
    (complexOrdinaryDerivedNatTransHomotopy A η) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)
    (complexDiagramDerived_vertex A F i) (complexDiagramDerived_vertex A G i)
    ((nerve.edgeMk (η.app i)).map (complexOrdinaryDerivedSource A)).toTruncated
    (complexOrdinaryDerivedNatTransHomotopy_component A η i)

end SerrePositivity.EInfinity.ComplexLimits
