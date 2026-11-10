module

public import SerrePositivity.InfinityCategories.F2.Presentable.LeftFibrationPointEvaluation
public import SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.EquivalenceColimits
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityEquivalence
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.FunctorPointwiseColimitCriterion
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport

/-!
概要：底上の left fibrations の strict filtered 余極限全余錐は、元の ∞ 圏でも余極限である。
方針：元の分類同値で写し、全頂点の評価を有限な一点始域の相対 Hom と全自然比較する。
規約：元の同じ全余錐を判定する。頂点の存在だけや通常の余極限だけで結論しない。
使われ方：有限底上模型の filtered 全表示の native な普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：元の通常の底上の filtered 全余錐は、left fibration ∞ 圏で余極限である。
方針：分類同値の点ごとの評価を、有限な一点始域の相対 Hom と比較する。
規約：同じ指定余錐の全 join 射を保持する。
使われ方：有限底上模型の全表示の native な普遍性。 -/
lemma leftFibrationStrictCocone_isColimit {B : SSet.{u}} [Quasicategory B]
    {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ LeftFibrationObject B}
    (c : Cocone F) (hc : IsColimit ((leftFibrationObjectForget B).mapCocone c)) :
    IsColimitCone (strictNativeCocone c) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff (leftStraighteningInfinityMap_isQCatEquivalence B)
    (strictNativeCocone c)).mpr
  apply F2.isColimitCone_of_pointwise
  rintro ⟨b⟩
  let A : Over B := Over.mk (SSet.yonedaEquiv.symm b)
  have : A.left.Finite := inferInstanceAs (Δ[0] : SSet.{u}).Finite
  have hpoint := finiteRelativeHom_preserves_strictCocone
    A c hc
  have hfiber : IsColimitCone
      (mapJoinCocone (leftFibrationInfinityFiberEvaluation b) (strictNativeCocone c)) :=
    hpoint.of_functorIso
    ((leftFibrationPointEvaluationIso b).precomp (strictNativeCocone c).val)
  have heval : IsColimitCone (mapJoinCocone
      (leftStraighteningInfinityMap B ≫ evaluateFunctorAt (ULift.up b)) (strictNativeCocone c)) :=
    hfiber.of_functorIso
    ((leftStraighteningInfinityMap_evaluateIso b).precomp (strictNativeCocone c).val).symm
  exact (isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _).symm).mp heval

end SerrePositivity.InfinityCategories.F2.Presentable
