module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientSourceValue
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeConstantValueIso

/-!
概要：元の全評価の係数制限の始点固定作用を、同じ復元による標準値作用へ比較する。
方針：同じ反対底上の相対同型を始点固定の族へ制限し、定値底の fiber 内で読む。
規約：元の係数評価そのものを固定。使われ方：指定 native 余錐への弱同値性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I) (x : C _⦋0⦌)
local notation "Q" => weightedLeftCoefficientDiagram (F ⋙ rightFibrationOppositeOrdinary C) i
abbrev weightedCoefficientProjection := (F.obj i).val.hom
local notation "σ" => pullback.fst (edgewiseRight C) (weightedCoefficientProjection F i) ≫ edgewiseLeft C
local notation "a" => twistedSourceElementsComparison (weightedCoefficientProjection F i) x

/-- 元の係数評価の始点固定制限は、同じ指定始点を被覆する。 -/
lemma weightedCoefficientSource_projection :
    (a ≫ weightedCoefficientEvaluation F i) ≫ smallLeftUnstraighteningProjection Q =
      SSet.const (SSet.opObjEquiv.symm x) := by
  rw [Category.assoc, weightedCoefficientEvaluation_projection]
  have h := twistedSourceElementsSourceMap_projection (F.obj i).val.hom x
  rw [twistedSourceElementsSourceMap, Category.assoc, twistedArrowSourceLift_projection] at h
  exact h

/-- 元の全評価を係数と始点に制限して得る、同じ値 fiber への実際の射。 -/
def weightedCoefficientSourceValue : twistedSourceElements (F.obj i).val.hom x ⟶
    vertexFiber (smallLeftUnstraighteningProjection Q) (SSet.opObjEquiv.symm x) :=
  vertexFiberLift _ _ (a ≫ weightedCoefficientEvaluation F i)
    (weightedCoefficientSource_projection F i x)

/-- 同じ値写像を全空間へ含めると、元の係数評価の同じ制限そのもの。 -/
lemma weightedCoefficientSourceValue_ι :
    weightedCoefficientSourceValue F i x ≫
      vertexFiberι (smallLeftUnstraighteningProjection Q) (SSet.opObjEquiv.symm x) =
        a ≫ weightedCoefficientEvaluation F i := vertexFiberLift_ι _ _ _ _

/-- 元の係数評価の実際の始点固定値写像は、元の標準評価の同じ復元像と関手同型。 -/
def weightedCoefficientSourceValue_canonicalIso :
    FunctorIso (weightedCoefficientSourceValue F i x)
      (weightedCoefficientCanonicalSourceValue F i x) := by
  have h₁ := relativeFunctorPre_vertex (smallLeftUnstraighteningProjection Q) σ a
    (weightedCoefficientEvaluation F i) (weightedCoefficientEvaluation_projection F i)
  have hR := weightedLeftCoefficientRecovery_projection
    (F ⋙ rightFibrationOppositeOrdinary C) i
  have h₂ := relativeFunctorPre_vertex (smallLeftUnstraighteningProjection Q) σ a
    (twistedArrowSourceLift (F.obj i).val.hom ≫
      weightedLeftCoefficientRecovery (F ⋙ rightFibrationOppositeOrdinary C) i)
    (by rw [Category.assoc, hR]; exact twistedArrowSourceLift_projection (F.obj i).val.hom)
  have e := eqToIso (congrArg HomotopyCategory.mk h₁.symm) ≪≫
    (weightedCoefficientEvaluation_canonicalIso F i).map
      (relativeFunctorPre (smallLeftUnstraighteningProjection Q) σ a) ≪≫
    eqToIso (congrArg HomotopyCategory.mk h₂)
  apply relativeConstantValueIso
  refine relativeEvaluationIsoOfEq ?_ (weightedCoefficientSourceValue_ι F i x).symm ?_ e
  · have h := twistedSourceElementsSourceMap_projection (F.obj i).val.hom x
    rw [twistedSourceElementsSourceMap, Category.assoc, twistedArrowSourceLift_projection] at h
    exact h
  · rw [weightedCoefficientCanonicalSourceValue_ι]

end SerrePositivity.InfinityCategories.F2.Ind
