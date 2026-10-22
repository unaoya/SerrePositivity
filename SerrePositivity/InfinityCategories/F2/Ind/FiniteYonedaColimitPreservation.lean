module

public import SerrePositivity.InfinityCategories.F2.Ind.UliftCoconeReverse

/-!
概要：元の小さい有限余極限の全余錐を、Ind Yoneda が余極限へ送る。
方針：反転全錐の極限性を全射の等式と形状同型で通常形へ戻す。
規約：有限極限交換を明示入力に保つ。使われ方：Ind の有限余極限と安定性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits

/-- 明示交換入力のもとで、Ind Yoneda は元の指定有限余極限の同じ全余錐を保存。 -/
lemma indYoneda_finiteColimit_isColimit (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hex : IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]
    [Quasicategory C] {D : K ⟶ C} (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (indYoneda κ C) (JoinCocone.ulift.{u, u + 1} c)) := by
  let t := mapJoinCone (SSet.opFunctor.map (indYoneda κ C))
    (F1B.kanCoconeReverseCone (JoinCocone.ulift.{u, u + 1} c))
  have hval : (mapJoinCone (oppositeIndYoneda κ)
      (JoinCone.ulift.{u, u + 1} (F1B.kanCoconeReverseCone c))).val =
      (restrictJoinCone t (uliftOppositeIso K).hom).val := by
    have h := congrArg (fun f => f ≫ SSet.opFunctor.map (indYoneda κ C))
      (uliftCoconeReverse_val c)
    exact (Category.assoc _ _ _).symm.trans h
  have ht : IsLimitCone (restrictJoinCone t (uliftOppositeIso K).hom) :=
    (F2.isLimitCone_iff_of_cone_val_eq _ _ hval).mp
      (indYoneda_finiteOppositeCone_isLimit κ hκ hex c hc)
  exact (F2.isLimitCone_reverse_postcomp_iff _ _).mp
    ((F2.isLimitCone_restrict_iff_of_isIso t (uliftOppositeIso K).hom).mp ht)

end SerrePositivity.InfinityCategories.F2.Ind
