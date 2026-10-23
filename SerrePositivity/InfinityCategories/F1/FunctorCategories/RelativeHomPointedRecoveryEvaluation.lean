module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeHomCoherentPointedRecovery
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-!
概要：pointed 回収を、既存の実際の unstraightening の普遍族の恒等点評価として計算する。
方針：正規化した相対評価の包含後の式を uncurry し、同じ普遍族への制限を取る。
規約：coherent 変換空間全体を保ち、元の普遍的な持ち上げを変更しない。
使われ方：元の Kan 値回収との比較を、同じ pointed 輸送の底と両端で照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 任意の相対関手の族の恒等点評価は、同じ展開済みの族の恒等点での制限。 -/
lemma relativeHomIdentityEvaluate_family_ι {B : SSet.{u}} (q : LeftFibrationObject B)
    {E P : SSet.{u + 1}} (p : E ⟶ LeftFibrationInfinity B)
    (f : P ⟶ relativeFunctorSpace p
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))) :
    f ≫ relativeHomIdentityEvaluate q p ≫ vertexFiberι p (coherentNerveVertex q) =
      lift (SSet.const (relativeHomUnstraighteningIdentity q).val) (𝟙 P) ≫
        relativeFunctorUncurry f := by
  rw [relativeHomIdentityEvaluate_ι]
  change (f ≫ vertexFiberι _ _) ≫
    evaluateFunctorAt (relativeHomUnstraighteningIdentity q).val = _
  rw [← curry_uncurry (f ≫ vertexFiberι _ _), curry_evaluateFunctorAt_vertex]
  rfl

/-- 実際の pointed 回収は、同じ unstraightening 普遍族の恒等点での終点そのもの。 -/
lemma relativeHomCoherentPointedRecovery_ι {B : SSet.{u}} (a q : LeftFibrationObject B) :
    relativeHomCoherentPointedRecovery a q ≫ vertexFiberι pointedSpaceProjection
      (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation a.val).obj q)) =
    lift (SSet.const (relativeHomUnstraighteningIdentity q).val)
      (pinchedHomToIntervalMappingSpace
        (functorVertex (leftFibrationCoherentEvaluation q.val))
        (functorVertex (leftFibrationCoherentEvaluation a.val))) ≫
      leftUnstraighteningMappingFamily (leftFibrationCoherentEvaluation q.val)
        (leftFibrationCoherentEvaluation a.val) ≫
      pullback.fst pointedSpaceProjection (leftFibrationCoherentEvaluation a.val) := by
  calc
    _ = (leftUnstraighteningPinchedMappingSpaceMap (leftFibrationCoherentEvaluation q.val)
        (leftFibrationCoherentEvaluation a.val) ≫ relativeHomIdentityEvaluate q
          (leftUnstraighteningProjection (leftFibrationCoherentEvaluation a.val)) ≫
        vertexFiberι (leftUnstraighteningProjection (leftFibrationCoherentEvaluation a.val))
          (coherentNerveVertex q)) ≫
        pullback.fst pointedSpaceProjection (leftFibrationCoherentEvaluation a.val) := by
      rw [relativeHomCoherentPointedRecovery, Category.assoc, Category.assoc,
        relativeHomUnstraighteningFiberIso_hom_ι]
      simp only [Category.assoc]
    _ = (lift (SSet.const (relativeHomUnstraighteningIdentity q).val) (𝟙 _) ≫
        relativeFunctorUncurry (leftUnstraighteningPinchedMappingSpaceMap
          (leftFibrationCoherentEvaluation q.val) (leftFibrationCoherentEvaluation a.val))) ≫
        pullback.fst pointedSpaceProjection (leftFibrationCoherentEvaluation a.val) :=
      congrArg (fun k ↦ k ≫ pullback.fst pointedSpaceProjection
        (leftFibrationCoherentEvaluation a.val)) (relativeHomIdentityEvaluate_family_ι q _ _)
    _ = _ := by
      rw [leftUnstraighteningPinchedMappingSpaceMap, relativeFunctorUncurry_naturality,
        leftUnstraighteningMappingSpaceMap_uncurry]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro t
      rfl

end SerrePositivity.InfinityCategories
