module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeElementColumn
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Resolution
/-! 概要：元の正規化 Hom の同じ要素圏上に自由 E∞ frame の列を構成する。
方針：同じ次数図式と元の随伴 Hom 同型から augmentation・評価を作る。
規約：全列と同じ単位を保持。使われ方：標準導来単位比較の全族三角形。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A] (X : Complex A) (B : (operad A).Algebra)
lemma freeProbeElementColumnEvaluation_unit (s : freeProbeElementIndex A X B) :
    (operad A).freeAlgebraAdjunction.unit.app
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val).obj s) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)).map ((freeProbeElementColumnEvaluation A X B).app s) =
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val).app s ≫
        _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A B.carrier := by
  exact ((operad A).freeAlgebraAdjunction.homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)
open CategoryTheory.Limits HomotopicalAlgebra SerrePositivity.Reedy
lemma freeProbeElementColumnAugmentation_unit (s : freeProbeElementIndex A X B) :
    (operad A).freeAlgebraAdjunction.unit.app
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val).obj s) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)).map ((freeProbeElementColumnAugmentation A X B).app s) =
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val).app s ≫
        (operad A).freeAlgebraAdjunction.unit.app ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) := by
  exact ((operad A).freeAlgebraAdjunction.unit.naturality
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val).app s)).symm

lemma freeProbeElementColumnAugmentation_weak (s : freeProbeElementIndex A X B) :
    let := modelCategory A
    weakEquivalences (operad A).Algebra ((freeProbeElementColumnAugmentation A X B).app s) :=
  freeNormalizedProbeAugmentation_weak A X
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDegree A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val).obj s)

lemma freeProbeElementColumn_map_weak {s t : freeProbeElementIndex A X B} (f : s ⟶ t) :
    let := modelCategory A
    weakEquivalences (operad A).Algebra ((freeProbeElementColumn A X B).map f) :=
  freeNormalizedProbeFrame_homotopicallyConstant A X
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDegree A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val).map f)

lemma freeProbeElementColumn_cofibrant (s : freeProbeElementIndex A X B) :
    let := modelCategory A
    IsCofibrant ((freeProbeElementColumn A X B).obj s) := by
  let := modelCategory A
  let n := (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDegree A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
    (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val).obj s
  have hi : Cofibration ((initial.to ((freeNormalizedProbeFrame A).obj X)).app n) :=
    ⟨cofibration_app simplex (initial.to ((freeNormalizedProbeFrame A).obj X))
      (freeNormalizedProbeFrame_cofibrant A X) n⟩
  exact (isCofibrant_iff_of_isInitial ((initial.to ((freeNormalizedProbeFrame A).obj X)).app n)
    (initialIsInitial.isInitialObj
      ((evaluation SimplexCategory (operad A).Algebra).obj n)
      (⊥_ (SimplexCategory ⥤ (operad A).Algebra)))).mpr hi

end SerrePositivity.EInfinity.BarrattEccles
