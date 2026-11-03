module

public import SerrePositivity.InfinityCategories.F2.Ind.YonedaLimitPreservation
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteYonedaColimitPreservation
public import SerrePositivity.InfinityCategories.Core.UniverseUniversalSquares

/-!
概要：元の小さい実普遍四角形を、同じ宇宙持ち上げと Ind Yoneda が保存する。
方針：元の全錐・全余錐の保存を標準ホーンの宇宙同型で読み替える。
規約：引き戻し側は交換不要、押し出し側だけ明示交換入力を使う。
使われ方：I-2 c の段ごとの bicartesian 性と Yoneda 包含の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ元の実引き戻し四角形を Ind Yoneda が保存する。 -/
lemma indYoneda_preservesPullbackSquare (κ : Cardinal.{u}) {C : SSet.{u}}
    [Quasicategory C] (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C)
    (hL : IsPullbackSquare L) :
    IsPullbackSquare (uliftSquare.{u, u + 1} L ≫ indYoneda κ C) := by
  let c := mapJoinCone (indYoneda κ C) (JoinCone.ulift.{u, u + 1} (pullbackCone L))
  have hc := indYoneda_isLimit κ (pullbackCone L) hL
  have hr := (isLimitCone_iff_reindexIso c (uliftHornIso.{u, u + 1} 2 2).symm).mp hc
  apply (F2.isLimitCone_iff_of_cone_val_eq _ _ ?_).mp hr
  have h := congrArg (fun z => z ≫ indYoneda κ C)
    (pullbackCone_ulift_reindex_val.{u, u + 1} L)
  change (joinMap (𝟙 Δ[0]) (uliftHornIso.{u, u + 1} 2 2).inv ≫
    (JoinCone.ulift.{u, u + 1} (pullbackCone L)).val) ≫ indYoneda κ C =
      (cospanConeSquareIso.hom ≫ uliftSquare L) ≫ indYoneda κ C at h
  change joinMap (𝟙 Δ[0]) (uliftHornIso.{u, u + 1} 2 2).inv ≫
    ((JoinCone.ulift.{u, u + 1} (pullbackCone L)).val ≫ indYoneda κ C) =
      cospanConeSquareIso.hom ≫ (uliftSquare L ≫ indYoneda κ C)
  simpa only [Category.assoc] using h

/-- 同じ元の実押し出し四角形を、明示交換のもとで Ind Yoneda が保存する。 -/
lemma indYoneda_preservesPushoutSquare (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hex : IndFiniteLimitExchangeInput.{u}) {C : SSet.{u}} [Quasicategory C]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C) (hL : IsPushoutSquare L) :
    IsPushoutSquare (uliftSquare.{u, u + 1} L ≫ indYoneda κ C) := by
  let c := mapJoinCocone (indYoneda κ C) (JoinCocone.ulift.{u, u + 1} (pushoutCocone L))
  have hc := indYoneda_finiteColimit_isColimit κ hκ hex (pushoutCocone L) hL
  have hr := (isColimitCone_iff_reindexIso c (uliftHornIso.{u, u + 1} 2 0).symm).mp hc
  apply (F2.isColimitCone_iff_of_coconeMap_eq _ _ ?_).mp hr
  have h := congrArg (fun z => z ≫ indYoneda κ C)
    (pushoutCocone_ulift_reindex_val.{u, u + 1} L)
  change (joinMap (uliftHornIso.{u, u + 1} 2 0).inv (𝟙 Δ[0]) ≫
    (JoinCocone.ulift.{u, u + 1} (pushoutCocone L)).val) ≫ indYoneda κ C =
      (spanCoconeSquareIso.hom ≫ uliftSquare L) ≫ indYoneda κ C at h
  change joinMap (uliftHornIso.{u, u + 1} 2 0).inv (𝟙 Δ[0]) ≫
    ((JoinCocone.ulift.{u, u + 1} (pushoutCocone L)).val ≫ indYoneda κ C) =
      spanCoconeSquareIso.hom ≫ (uliftSquare L ≫ indYoneda κ C)
  simpa only [Category.assoc] using h

end SerrePositivity.InfinityCategories.F2.Ind
