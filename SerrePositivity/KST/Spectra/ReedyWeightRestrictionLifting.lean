module

public import SerrePositivity.KST.Spectra.RelativeCornerProductCube
public import SerrePositivity.KST.Spectra.WeightedEndReedyKan
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedRestriction

/-!
概要：Reedy anodyne な重みの射への end の制限は全ての単射への RLP を持つ。
方針：二つの転置族を実際の corner 上で貼り、相対 latching の交換同型から Reedy 充填を行う。
規約：係数には実際の Reedy fibrancy を用い、各段の Kan 性だけで代用しない。
使われ方：Goerss–Jardine VII §4。重みの Reedy 置換単位から元の Tot 比較へ戻す。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.InfinityCategories.HomotopyLimits

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
    HasLiftingProperty i (weightedSectionsPre (Functor.whiskerLeft AsSmall.down θ)
      (AsSmall.down ⋙ X)) := by
  let := CosimplicialHornFactorization.hornWeakFactorization.{u}
  let P := WeightCornerPushout.corner θ i
  have hi := WeightCornerPushout.corner_reedy_anodyne θ i hθ
  let : ∀ j, HasLiftingProperty (relativeLatchingMap simplex j P.ι)
      (relativeMatchingMap simplex j (terminal.from X)) := fun j ↦
    MorphismProperty.hasLiftingProperty_of_wfs _ _ (hi j) (hX j)
  let : HasLiftingProperty P.ι (terminal.from X) := Lifting.hasLiftingProperty simplex
  constructor
  intro t s sq
  let t' := WeightedEndReedyKan.ordinaryFamily (weightedSectionsUncurry t)
  let s' := WeightedEndReedyKan.ordinaryFamily (weightedSectionsUncurry s)
  have hw : Functor.whiskerRight θ (tensorRight A) ≫ t' =
      WeightTensorLatching.map F i ≫ s' := by
    have h := congrArg weightedSectionsUncurry sq.w
    rw [weightedSectionsUncurry_comp_pre, weightedSectionsUncurry_precomp] at h
    apply NatTrans.ext
    funext j
    exact NatTrans.congr_app h (AsSmall.up.obj j)
  let a := P.isPushout.desc t' s' hw
  let q : CommSq a P.ι (terminal.from X) (terminal.from _) := ⟨terminal.hom_ext _ _⟩
  have ht : WeightTensorLatching.map G i ≫ q.lift = t' := by
    have h := congrArg (fun f ↦ P.inl ≫ f) q.fac_left
    rw [← Category.assoc, P.inl_ι, P.isPushout.inl_desc] at h
    exact h
  have hs : Functor.whiskerRight θ (tensorRight B) ≫ q.lift = s' := by
    have h := congrArg (fun f ↦ P.inr ≫ f) q.fac_left
    rw [← Category.assoc, P.inr_ι, P.isPushout.inr_desc] at h
    exact h
  refine CommSq.HasLift.mk' {
    l := weightedSectionsLift (WeightedEndReedyKan.smallFamily q.lift)
    fac_left := ?_
    fac_right := ?_ }
  · apply (weightedSectionsHomEquiv (AsSmall.down ⋙ G) (AsSmall.down ⋙ X) A).injective
    change weightedSectionsUncurry
      (i ≫ weightedSectionsLift (WeightedEndReedyKan.smallFamily q.lift)) = _
    rw [weightedSectionsUncurry_precomp, weightedSectionsUncurry_lift]
    apply NatTrans.ext
    funext j
    exact NatTrans.congr_app ht (AsSmall.down.obj j)
  · apply (weightedSectionsHomEquiv (AsSmall.down ⋙ F) (AsSmall.down ⋙ X) B).injective
    change weightedSectionsUncurry
      (weightedSectionsLift (WeightedEndReedyKan.smallFamily q.lift) ≫
        weightedSectionsPre (Functor.whiskerLeft AsSmall.down θ) (AsSmall.down ⋙ X)) = _
    rw [weightedSectionsUncurry_comp_pre, weightedSectionsUncurry_lift]
    apply NatTrans.ext
    funext j
    exact NatTrans.congr_app hs (AsSmall.down.obj j)

/-- 係数の Reedy 条件の下で、重みの Reedy anodyne な制限は全単射 RLP。 -/
lemma rlp_monomorphisms (θ : F ⟶ G) (hθ : reedyLeft simplex anodyneExtensions θ)
    (X : CosimplicialObject SSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp (terminal.from X)) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (weightedSectionsPre (Functor.whiskerLeft AsSmall.down θ) (AsSmall.down ⋙ X)) := by
  intro A B i hi
  let : Mono i := hi
  exact hasLiftingProperty θ hθ X hX i

end
end SerrePositivity.KST.Spectra.ReedyWeightRestrictionLifting
