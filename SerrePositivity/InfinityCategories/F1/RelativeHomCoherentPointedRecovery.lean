module

public import SerrePositivity.InfinityCategories.F1.RelativeHomIdentityEvaluation
public import SerrePositivity.InfinityCategories.F1.CoherentUnstraighteningMappingEquivalence

/-!
概要：任意の coherent な Hom 変換を、実際の恒等点で pointed fiber へ回収する。
方針：既存の実際の unstraightening 写像空間比較に恒等点評価と同じ fiber 同型を合成する。
規約：全変換空間に一つの射を定義する。元の Kan 値の回収との照合は別に行う。
使われ方：coherent 比較の充満忠実性を、元の恒等射での回収そのものへ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 実際の unstraightening と恒等点評価を通して、全 coherent 変換を pointed fiber へ回収する。 -/
def relativeHomCoherentPointedRecovery {B : SSet.{u}} (a q : LeftFibrationObject B) :
    pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
      (functorVertex (leftFibrationCoherentEvaluation a.val)) ⟶
        vertexFiber pointedSpaceProjection
          (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation a.val).obj q)) :=
  leftUnstraighteningPinchedMappingSpaceMap (leftFibrationCoherentEvaluation q.val)
    (leftFibrationCoherentEvaluation a.val) ≫
    relativeHomIdentityEvaluate q
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation a.val)) ≫
      (relativeHomUnstraighteningFiberIso a q).hom

/-- 全 coherent 変換の実際の恒等点での pointed 回収は、同じ射そのものが同値。 -/
lemma relativeHomCoherentPointedRecovery_isQCatEquivalence {B : SSet.{u}}
    (a q : LeftFibrationObject B) :
    IsQCatEquivalence (relativeHomCoherentPointedRecovery a q) := by
  have : KanComplex (vertexFiber
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation a.val))
        (coherentNerveVertex q)) := vertexFiber_kanComplex_of_leftFibration _ _
  have : KanComplex (vertexFiber pointedSpaceProjection
      (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation a.val).obj q))) :=
    vertexFiber_kanComplex_of_leftFibration _ _
  exact (leftUnstraighteningPinchedMappingSpaceMap_isQCatEquivalence
    (leftFibrationCoherentEvaluation q.val) (leftFibrationCoherentEvaluation a.val)).comp
    ((relativeHomIdentityEvaluate_isQCatEquivalence q
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation a.val))).comp
      (qCatEquivalenceOfIso (relativeHomUnstraighteningFiberIso a q)).isQCatEquivalence)

end SerrePositivity.InfinityCategories
