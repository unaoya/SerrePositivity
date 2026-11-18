module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedUnitRecoveryComponent

/-!
# 同じ導来単位の成分を全複体の分解値の間で読む

概要：元の導来単位の成分を元の全比較と端点等式で輸送する。
方針：同じ回収成分を前後で輸送し、元の自由単位辺の像との一致を使う。
規約：元の導来単位・probe・比較を保つ。
使われ方：正規化 Hom の全族を標準導来単位の前合成へ同定する。
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

def freeProbeDerivedUnitAmbientHom (X : Complex A) :
    (HomotopyCategory.mk ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X))) :
        hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) ⟶
      HomotopyCategory.mk ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((freeProbeFunctor A).obj X).carrier)) :=
  (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbientVertexIso A
    ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)).inv ≫
    freeProbeDerivedUnitRecoveredHom A X ≫
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbientVertexIso A
        ((freeProbeFunctor A).obj X).carrier).hom

lemma freeProbeDerivedUnitAmbientHom_eq (X : Complex A) :
    freeProbeDerivedUnitAmbientHom A X =
    (hoFunctor.map (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)).toFunctor.map
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A)
        ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
          ((operad A).freeAlgebraAdjunction.unit.app
            ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X))))) := by
  dsimp only [freeProbeDerivedUnitAmbientHom]
  rw [freeProbeDerivedUnitRecoveredHom_eq]
  exact freeProbeUnitHom_ambient A X

end SerrePositivity.EInfinity.BarrattEccles
