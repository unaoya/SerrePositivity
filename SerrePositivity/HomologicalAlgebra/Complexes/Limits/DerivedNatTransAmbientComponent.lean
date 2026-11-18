module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DerivedNatTransComponent
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedAmbientEdges

/-!
概要：元の全自然変換の成分を、同じ閉辺の半自由分解像に同定する。
方針：同じ図式頂点の輸送と同じ通常辺の輸送を合成する。
規約：元の全円柱・成分射・指定端点を保持する。
使われ方：正規化単体の大域実屋根と元の局所実評価族の照合。
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

def complexDiagramAmbientVertexIso (F : I ⥤ Complex A) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((nerveMap F ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))
    ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj i))) :=
  _root_.SerrePositivity.ComplexLimits.complexDiagramDerivedVertexIso A F i ≪≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbientVertexIso A (F.obj i)

lemma complexOrdinaryDerivedNatTransAmbient_component {F G : I ⥤ Complex A}
    (η : F ⟶ G) (i : I) :
    (_root_.SerrePositivity.ComplexLimits.complexDiagramAmbientVertexIso A F i).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A η) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) ≫
        (_root_.SerrePositivity.ComplexLimits.complexDiagramAmbientVertexIso A G i).hom =
    (hoFunctor.map (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)).toFunctor.map
      (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (η.app i)))) := by
  have h := congrArg (fun f => (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbientVertexIso A (F.obj i)).inv ≫ f ≫
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbientVertexIso A (G.obj i)).hom)
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom_component A η i)
  simpa only [_root_.SerrePositivity.ComplexLimits.complexDiagramAmbientVertexIso, Iso.trans_inv, Iso.trans_hom,
    Category.assoc] using h.trans (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbient_hom A (η.app i))

end SerrePositivity.ComplexLimits
