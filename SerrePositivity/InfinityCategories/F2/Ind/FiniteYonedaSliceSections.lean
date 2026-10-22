module

public import SerrePositivity.InfinityCategories.F2.Ind.OppositeUnstraighteningSections
public import SerrePositivity.InfinityCategories.F2.Ind.YonedaSliceOppositeComparison

/-!
概要：元の指定有限余極限に沿う Yoneda slice の全切断制限自身が同値。
方針：同じ反転全錐上で、元の小さい元の圏との実比較による後合成同値を消去する。
規約：交換入力は明示引数、指定元余錐・全比較・底射影を保持する。
使われ方：Ind Yoneda の同じ有限余極限全余錐の普遍性へ戻るための comma 側の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits

/-- 同じ Yoneda comma の反転上で、元の有限全余錐の同じ持ち上げによる切断制限は同値。 -/
lemma indPresheaf_finiteColimit_yonedaSliceSections_isQCatEquivalence
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {K C : SSet.{u}} [K.Finite] [Quasicategory C] {D : K ⟶ C}
    (c : JoinCocone D) (hc : IsColimitCone c)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (hF : IsIndVertex κ C (functorVertex F)) :
    IsQCatEquivalence (leftFibrationConeRestriction (oppositeYonedaSliceProjection F)
      (JoinCone.ulift.{u, u + 1} (F1B.kanCoconeReverseCone c))) :=
  (leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    ((SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (smallRightUnstraighteningProjection F)))
    (oppositeYonedaSliceProjection F) (oppositeElementsYonedaSliceComparison F)
    (oppositeElementsYonedaSliceComparison_projection F)
    (oppositeElementsYonedaSliceComparison_isPrecompositionEquivalence F)
    (JoinCone.ulift.{u, u + 1} (F1B.kanCoconeReverseCone c))).mp
      (indPresheaf_finiteColimit_liftedOppositeRightSections_isQCatEquivalence κ hκ hex c hc F hF)

end SerrePositivity.InfinityCategories.F2.Ind
