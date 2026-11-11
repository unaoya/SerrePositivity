module

public import SerrePositivity.KST.Spectra.ReedyWeightCornerLifting

/-!
概要：Reedy anodyne な重みの射への end の制限は全ての単射への RLP を持つ。
方針：二つの転置族を実際の corner 上で貼り、相対 latching の交換同型から Reedy 充填を行う。
規約：係数には実際の Reedy fibrancy を用い、各段の Kan 性だけで代用しない。
使われ方：Goerss–Jardine VII §4。重みの Reedy 置換単位から元の Tot 比較へ戻す。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.ReedyWeightRestrictionLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {F G : CosimplicialObject SSet.{u}}

/-- Reedy anodyne な重みへの制限の、任意の単射パラメーターの実際の持ち上げ。 -/
lemma hasLiftingProperty (θ : F ⟶ G) (hθ : reedyLeft simplex anodyneExtensions θ)
    (X : CosimplicialObject SSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp (terminal.from X))
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (Functor.whiskerLeft AsSmall.down θ)
      (AsSmall.down ⋙ X)) := by
  exact ReedyWeightCornerLifting.hasLiftingProperty θ X hX i
    (WeightCornerPushout.corner_reedy_anodyne θ i hθ)

/-- 係数の Reedy 条件の下で、重みの Reedy anodyne な制限は全単射 RLP。 -/
lemma rlp_monomorphisms (θ : F ⟶ G) (hθ : reedyLeft simplex anodyneExtensions θ)
    (X : CosimplicialObject SSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp (terminal.from X)) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (Functor.whiskerLeft AsSmall.down θ) (AsSmall.down ⋙ X)) := by
  intro A B i hi
  let : Mono i := hi
  exact hasLiftingProperty θ hθ X hX i

end
end SerrePositivity.KST.Spectra.ReedyWeightRestrictionLifting
