module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedUnit
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedAmbientEdges
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DerivedNatTransComponent

/-!
# 元の自由 probe 単位二胞体の同じ閉辺による成分表示

概要：元の単位二胞体の評価を、同じ自由単位の閉 dg 辺の導来像へ照合する。
方針：元の全円柱の頂点成分式と端点の等式輸送を合成する。
規約：別の単位辺や別の二胞体を選ばない。
使われ方：正規化 Hom 全族の単位辺を既存の導来単位へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

def freeProbeUnitOrdinaryHom (X : Complex A) :
    (HomotopyCategory.mk ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X))) :
        hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) ⟶
      HomotopyCategory.mk ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((freeProbeFunctor A).obj X).carrier)) :=
  (_root_.SerrePositivity.ComplexLimits.complexDiagramDerivedVertexIso A
    (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A) X).inv ≫
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (freeProbeUnitHom A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) ≫
      (_root_.SerrePositivity.ComplexLimits.complexDiagramDerivedVertexIso A
        (freeProbeFunctor A ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)) X).hom

lemma freeProbeUnitHom_component (X : Complex A) :
    freeProbeUnitOrdinaryHom A X =
    Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk ((freeProbeUnitNatTrans A).app X)).map
        (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated :=
  _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom_component A (freeProbeUnitNatTrans A) X

lemma freeProbeUnitHom_ambient (X : Complex A) :
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbientVertexIso A
      ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)).inv ≫
      freeProbeUnitOrdinaryHom A X ≫
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbientVertexIso A
        ((freeProbeFunctor A).obj X).carrier).hom =
    (hoFunctor.map (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)).toFunctor.map
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A)
        ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
          ((operad A).freeAlgebraAdjunction.unit.app
            ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X))))) := by
  rw [freeProbeUnitHom_component]
  exact _root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbient_hom A ((freeProbeUnitNatTrans A).app X)

end SerrePositivity.EInfinity.BarrattEccles
