module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeUnitAmbientComponent
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation

/-!
# 同じ導来単位二胞体の成分の回収

概要：元の全比較で同じ導来単位の成分を戻すと元の自由単位の成分になる。
方針：既存の全回収等式を同じ頂点で評価する。
規約：導来単位や比較を選び直さない。
使われ方：正規化 Hom の全族公式に元の導来単位を明示する。
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

def freeProbeDerivedUnitRecoveredHom (X : Complex A) :
    (HomotopyCategory.mk ((ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((ComplexLimits.framedLimitProbeFunctor A).obj X))) :
        hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) ⟶
      HomotopyCategory.mk ((ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((freeProbeFunctor A).obj X).carrier)) :=
  (ComplexLimits.complexDiagramDerivedVertexIso A
    (ComplexLimits.framedLimitProbeFunctor A) X).inv ≫
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate ((ComplexLimits.complexProbeDerivedSourceIso A).hom ≫
      freeProbeDerivedUnit A ≫ (freeProbeUnderlyingDerivedSourceIso A).hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) ≫
      (ComplexLimits.complexDiagramDerivedVertexIso A
        (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) X).hom

lemma freeProbeDerivedUnitRecoveredHom_eq (X : Complex A) :
    freeProbeDerivedUnitRecoveredHom A X = freeProbeUnitOrdinaryHom A X := by
  dsimp only [freeProbeDerivedUnitRecoveredHom]
  rw [freeProbeDerivedUnit_recovery]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
