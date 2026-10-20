module

public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfLeftOrdinaryComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfRightOrdinaryComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfDerivedLimits

/-!
概要：単体的 Quillen 随伴の元の cf nerve 上の ∞ 随伴と右導来関手の極限保存を集約する。
方針：同じ標準単位の随伴に、両側の通常置換比較と任意 coherent 図式の極限保存を結ぶ。
規約：固定 SM7 と豊穣随伴の合成互換を明示入力。使われ方：HTT 5.2.4.6、Sp、E2b。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

open HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Coherent
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C)
  {L : C ⥤ D} (adj : L ⊣ coherentEnrichedUnderlyingFunctor R)
  [SerrePositivity.Quillen.IsLeftQuillen L]
  (fibD : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations D) (fibrations D))
  (e : EnrichedAdjunctionHomComposition R adj)
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [FixedSimplicialPushoutProduct SC.tensor] [FixedSimplicialPushoutProduct SD.tensor]


variable (cofC : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))
include fibD e SC SD cofC in
/-- 元の cf 対応圏の両側輸送、標準単位を持つ ∞ 随伴、元の通常置換との比較と極限保存。 -/
lemma quillenCfDerivedAdjunctionWithComparisons_exists :
    letI := cofibrantFibrantObjects_nerve_quasicategory SC
    letI := cofibrantFibrantObjects_nerve_quasicategory SD
    ∃ H : SSet.Homotopy (𝟙 (SimplicialNerve (CofibrantFibrantObjects C)))
      (quillenCfLeftDerived R adj fibD e SC SD ≫ quillenCfRightDerived R adj SC SD cofC),
      ∃ a : QCatAdjunction (quillenCfLeftDerived R adj fibD e SC SD)
        (quillenCfRightDerived R adj SC SD cofC),
        a.unitHom = SSet.Truncated.HomotopyCategory.homMk
          (functorEdgeOfSimplicialHomotopy H) ∧
        CartesianFibration (quillenCfCollageProjection R) ∧
        CocartesianFibration (quillenCfCollageProjection R) ∧
        Nonempty (FunctorIso
          (nerveMap (quillenCfLeftReplacementFunctor R adj fibD) ≫
            nerveToCoherent (CofibrantFibrantObjects D))
          (nerveToCoherent (CofibrantFibrantObjects C) ≫
            quillenCfLeftDerived R adj fibD e SC SD)) ∧
        Nonempty (FunctorIso
          (nerveMap (quillenCfRightReplacementFunctor R adj cofC) ≫
            nerveToCoherent (CofibrantFibrantObjects C))
          (nerveToCoherent (CofibrantFibrantObjects D) ≫
            quillenCfRightDerived R adj SC SD cofC)) ∧
        ∀ (K : SSet.{max u v}) (p : K ⟶ SimplicialNerve (CofibrantFibrantObjects D))
          (c : JoinCone p), IsLimitCone c →
            IsLimitCone (mapJoinCone (quillenCfRightDerived R adj SC SD cofC) c) := by
  have := cofibrantFibrantObjects_nerve_quasicategory SC
  have := cofibrantFibrantObjects_nerve_quasicategory SD
  obtain ⟨H, a, ha⟩ := quillenCfDerivedAdjunction_exists R adj fibD e SC SD cofC
  exact ⟨H, a, ha,
    quillenCfCollageProjection_cartesianFibration R adj SC SD cofC,
    quillenCfCollageProjection_cocartesianFibration R adj fibD e SC SD,
    quillenCfLeftDerived_ordinaryComparison R adj fibD e SC SD,
    quillenCfRightDerived_ordinaryComparison R adj SC SD cofC,
    fun _ _ c hc ↦ mapJoinCone_isLimit_of_adjunction a c hc⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
