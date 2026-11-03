module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaHomWeightConeLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoYonedaLimitReflection
public import SerrePositivity.InfinityCategories.Core.Compact.UniverseCoconePostcomposition

/-!
概要：元の P_Σ Yoneda に沿う左 Kan 延長は、任意小 sifted 余極限を保存する。
方針：全自然変換空間族と持ち上げた延長の全 Hom 族を比較し、全 co-Yoneda で反映する。
規約：元の延長・指定単位・任意の指定余錐像を保持する。
使われ方：元の Yoneda 制限の本質的全射性と保存関手 ∞ 圏の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C] {E : SSet.{u + 1}} [Quasicategory E]
  {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ E} {G : SigmaPresheafInfinity C ⟶ E}
  (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G))
  (hβ : IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β)
include β hβ

/-- 概要：元の左 Kan 延長は任意小 sifted 図式の同じ指定余錐を余極限へ送る。
方針：同じ余錐の全 Hom 錐の自然比較で極限性を移し、全 co-Yoneda と宇宙変更で反映する。
規約：左 Kan 延長の保存性を追加入力にせず、元の指定単位の普遍性から導く。
使われ方：P_Σ の保存関手圏への左 Kan 延長の持ち上げ。 -/
lemma sigmaLeftKanExtension_preservesSmallSiftedColimits : PreservesSmallSiftedColimits G := by
  intro I hI p c hc
  let d := JoinCocone.ulift.{u + 1, u + 2} c
  have h := sigmaHomWeightFamily_map_isLimit F₀ p c hc
  have h' : IsLimitCone (mapJoinCone (sigmaLiftedHomFamily G)
      (JoinCone.ulift.{u + 2, u + 3} (F1B.coconeReverseCone d))) :=
    h.of_functorIso ((sigmaHomWeightFamily_liftedIso β hβ).precomp
      (JoinCone.ulift.{u + 2, u + 3} (F1B.coconeReverseCone d)).val)
  unfold sigmaLiftedHomFamily at h'
  rw [F2.Presentable.mapJoinCone_universe_comp] at h'
  have hlim := coyonedaInfinityMap_reflects_isLimit _ h'
  have hcol := (F2.isLimitCone_reverse_postcomp_iff d
    ((SSet.uliftFunctor.{u + 2, u + 1}).map G)).mp hlim
  apply (isColimitCone_iff_ulift (mapJoinCocone G c)).mpr
  apply (F2.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mp hcol
  exact (F2.Compact.ulift_mapJoinCocone_val G c).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
