module
public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedProbeFrameProperties
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementDiagram
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedProbeTargetReplacement
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
open ComplexLimits
variable (A : Type u) [CommRing A] (X : Complex A) (B : (operad A).Algebra)
abbrev freeProbeElementIndex : Type (u + 1) :=
  normalizedTensorElementIndex A
  ((framedLimitProbeFunctor A).obj X) (complexSemifreeResolutionValue A B.carrier).val

def freeProbeElementColumn : freeProbeElementIndex A X B ⥤ (operad A).Algebra :=
  normalizedTensorElementDegree A ((framedLimitProbeFunctor A).obj X)
    (complexSemifreeResolutionValue A B.carrier).val ⋙ (freeNormalizedProbeFrame A).obj X

def freeProbeElementColumnAugmentation : freeProbeElementColumn A X B ⟶
    (Functor.const _).obj ((freeProbeFunctor A).obj X) :=
  Functor.whiskerLeft (normalizedTensorElementDegree A ((framedLimitProbeFunctor A).obj X)
    (complexSemifreeResolutionValue A B.carrier).val) ((freeNormalizedProbeAugmentation A).app X)

def freeProbeElementColumnEvaluation : freeProbeElementColumn A X B ⟶
    (Functor.const _).obj B where
  app s := ((operad A).freeAlgebraAdjunction.homEquiv _ _).symm
    ((normalizedTensorElementEvaluation A ((framedLimitProbeFunctor A).obj X)
      (complexSemifreeResolutionValue A B.carrier).val).app s ≫
        complexSemifreeResolutionValueAugmentation A B.carrier)
  naturality s t f := by
    change (operad A).freeAlgebraFunctor.map
      ((normalizedTensorElementDiagram A ((framedLimitProbeFunctor A).obj X)
        (complexSemifreeResolutionValue A B.carrier).val).map f) ≫
      ((operad A).freeAlgebraAdjunction.homEquiv _ B).symm
        ((normalizedTensorElementEvaluation A ((framedLimitProbeFunctor A).obj X)
          (complexSemifreeResolutionValue A B.carrier).val).app t ≫
            complexSemifreeResolutionValueAugmentation A B.carrier) =
      ((operad A).freeAlgebraAdjunction.homEquiv _ B).symm
        ((normalizedTensorElementEvaluation A ((framedLimitProbeFunctor A).obj X)
          (complexSemifreeResolutionValue A B.carrier).val).app s ≫
            complexSemifreeResolutionValueAugmentation A B.carrier) ≫ 𝟙 B
    rw [Category.comp_id]
    apply ((operad A).freeAlgebraAdjunction.homEquiv _ B).injective
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hn := (normalizedTensorElementEvaluation A ((framedLimitProbeFunctor A).obj X)
      (complexSemifreeResolutionValue A B.carrier).val).naturality f
    simp only [Functor.const_obj_map] at hn
    rw [← Category.assoc, hn]
    exact congrArg (fun h => h ≫ complexSemifreeResolutionValueAugmentation A B.carrier)
      (Category.comp_id ((normalizedTensorElementEvaluation A
        ((framedLimitProbeFunctor A).obj X)
        (complexSemifreeResolutionValue A B.carrier).val).app s))

end SerrePositivity.EInfinity.BarrattEccles
