module

public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfDerivedAdjunction
public import SerrePositivity.InfinityCategories.HomotopyLimits.AdjunctionLimits

/-!
概要：元の cf nerve 間の導来右 Quillen 関手は、任意の coherent 極限錐を保つ。
方針：同じ cf 輸送から構成した ∞ 随伴を、native な極限保存定理へ適用する。
規約：simplicial SM7 と豊穣随伴の入力を保持する。使われ方：Sp・E2b への γ4 の提供。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
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
  (cofC : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))


include fibD e SC SD cofC in
/-- 元の導来右関手は、任意の coherent 図式の指定極限錐を native な意味で保つ。 -/
lemma quillenCfRightDerived_mapJoinCone_isLimit {K : SSet.{max u v}}
    {p : K ⟶ SimplicialNerve (CofibrantFibrantObjects D)}
    (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (quillenCfRightDerived R adj SC SD cofC) c) := by
  have := cofibrantFibrantObjects_nerve_quasicategory SC
  have := cofibrantFibrantObjects_nerve_quasicategory SD
  obtain ⟨_, a, _⟩ := quillenCfDerivedAdjunction_exists R adj fibD e SC SD cofC
  exact mapJoinCone_isLimit_of_adjunction a c hc

include fibD e SC SD cofC in
/-- 元の導来右関手は、任意の coherent 図式の極限の存在を保つ。 -/
lemma quillenCfRightDerived_hasLimit_postcomp {K : SSet.{max u v}}
    (p : K ⟶ SimplicialNerve (CofibrantFibrantObjects D)) (hp : HasLimit p) :
    HasLimit (p ≫ quillenCfRightDerived R adj SC SD cofC) := by
  obtain ⟨c, hc⟩ := hp
  exact ⟨mapJoinCone (quillenCfRightDerived R adj SC SD cofC) c,
    quillenCfRightDerived_mapJoinCone_isLimit R adj fibD e SC SD cofC c hc⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
