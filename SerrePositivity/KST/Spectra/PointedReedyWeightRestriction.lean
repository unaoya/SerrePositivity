module

public import SerrePositivity.KST.Spectra.ReedyWeightRestrictionFibration
public import SerrePositivity.KST.Spectra.PointedWeightedEndUnderlyingWeight

/-!
概要：重みの Reedy 単射への点つき enriched end の制限は基礎単体集合で fibration。
方針：二つの end の厳密同型と前合成の自然性を arrow 同型に束ねて持ち上げ性を移す。
規約：係数の Reedy 条件は基点を忘却した図式へ課す。
使われ方：Goerss–Jardine VIII §1。点つきの部分 Tot の塔の遷移。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.PointedWeightedEnd
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Reedy 単射な重みへの点つき end の制限は基礎単体集合で Kan fibration。 -/
lemma preMap_fibration {F G : CosimplicialObject SSet.{u}} (θ : F ⟶ G)
    (hθ : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) θ)
    (X : CosimplicialObject PointedSimplicialSet.{u})
    (hX : reedyRight simplex J.rlp (terminal.from (X ⋙ PointedSimplicialSet.forget))) :
    Fibration (preMap (Functor.whiskerLeft AsSmall.down θ) (AsSmall.down ⋙ X)).right := by
  let f := preMap (Functor.whiskerLeft AsSmall.down θ) (AsSmall.down ⋙ X)
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (Functor.whiskerLeft AsSmall.down θ)
    ((AsSmall.down ⋙ X) ⋙ PointedSimplicialSet.forget)
  let e : Arrow.mk f.right ≅ Arrow.mk g :=
    Arrow.isoMk (underlyingIso (AsSmall.down ⋙ G) (AsSmall.down ⋙ X))
      (underlyingIso (AsSmall.down ⋙ F) (AsSmall.down ⋙ X))
      (underlyingIso_preMap (Functor.whiskerLeft AsSmall.down θ) (AsSmall.down ⋙ X)).symm
  have hg : Fibration g :=
    ReedyWeightRestrictionFibration.fibration θ hθ (X ⋙ PointedSimplicialSet.forget) hX
  apply (modelCategoryQuillen.fibration_iff _).mpr
  exact (J.rlp.arrow_iso_iff e).mpr ((modelCategoryQuillen.fibration_iff g).mp hg)

end
end SerrePositivity.KST.Spectra.PointedWeightedEnd
