module

public import SerrePositivity.KST.Spectra.ReedyWeightCornerLifting

/-!
概要：Reedy 単射な重みへの end の制限は、Reedy fibrant な係数に対して Kan fibration。
方針：重みの相対 latching とパラメーターの pushout-product から anodyne corner を充填する。
規約：重みの各段の単射性だけで代用せず、実際の Reedy 単射条件を使う。
使われ方：Goerss–Jardine VIII §1。部分 Tot の塔の遷移を fibration にする界面。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.ReedyWeightRestrictionFibration
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F G : CosimplicialObject SSet.{u}}

/-- 重みの Reedy 単射への制限は、全ての anodyne なパラメーターを持ち上げる。 -/
lemma hasLiftingProperty (θ : F ⟶ G)
    (hθ : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) θ)
    (X : CosimplicialObject SSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp (terminal.from X))
    {A B : SSet.{u}} (i : A ⟶ B) (hi : anodyneExtensions i) :
    HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (Functor.whiskerLeft AsSmall.down θ)
      (AsSmall.down ⋙ X)) :=
  ReedyWeightCornerLifting.hasLiftingProperty θ X hX i
    (WeightCornerPushout.corner_reedy_anodyne_of_mono θ i hθ hi)

/-- 重みの Reedy 単射への end の制限は実際の Kan fibration。 -/
lemma fibration (θ : F ⟶ G)
    (hθ : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) θ)
    (X : CosimplicialObject SSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp (terminal.from X)) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (Functor.whiskerLeft AsSmall.down θ) (AsSmall.down ⋙ X)) := by
  let := CosimplicialHornFactorization.hornWeakFactorization.{u}
  apply (modelCategoryQuillen.fibration_iff _).mpr
  intro A B i hi
  have hai : anodyneExtensions i := by
    rw [anodyneExtensions_eq_llp_rlp]
    exact MorphismProperty.le_llp_rlp modelCategoryQuillen.J i hi
  exact hasLiftingProperty θ hθ X hX i hai

end
end SerrePositivity.KST.Spectra.ReedyWeightRestrictionFibration
