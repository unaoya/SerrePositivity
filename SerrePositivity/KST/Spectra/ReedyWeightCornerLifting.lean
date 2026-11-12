module

public import SerrePositivity.KST.Spectra.RelativeCornerProductCube
public import SerrePositivity.KST.Spectra.WeightedEndReedyKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction

/-!
概要：重みの相対 corner の Reedy anodyne 性から end 制限の持ち上げを構成する。
方針：二つの転置族を corner で貼り、係数の Reedy 条件による充填を curry する。
規約：二つの pushout-product の anodyne 条件に共通の実際の充填。
使われ方：Goerss–Jardine VII §4。重みの anodyne 制限と単射制限の両方の共通部分。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet HomotopicalAlgebra
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.ReedyWeightCornerLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 相対 corner が Reedy anodyne なら、end の制限は指定したパラメーターを持ち上げる。 -/
lemma hasLiftingProperty {F G : CosimplicialObject SSet.{u}} (θ : F ⟶ G)
    (X : CosimplicialObject SSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp (terminal.from X))
    {A B : SSet.{u}} (i : A ⟶ B)
    (hi : reedyLeft simplex anodyneExtensions (WeightCornerPushout.corner θ i).ι) :
    HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (Functor.whiskerLeft AsSmall.down θ)
      (AsSmall.down ⋙ X)) := by
  let := CosimplicialHornFactorization.hornWeakFactorization.{u}
  let P := WeightCornerPushout.corner θ i
  let : ∀ j, HasLiftingProperty (relativeLatchingMap simplex j P.ι)
      (relativeMatchingMap simplex j (terminal.from X)) := fun j ↦
    MorphismProperty.hasLiftingProperty_of_wfs _ _ (hi j) (hX j)
  let : HasLiftingProperty P.ι (terminal.from X) := Lifting.hasLiftingProperty simplex
  constructor
  intro t s sq
  let t' := WeightedEndReedyKan.ordinaryFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry t)
  let s' := WeightedEndReedyKan.ordinaryFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry s)
  have hw : Functor.whiskerRight θ (tensorRight A) ≫ t' =
      WeightTensorLatching.map F i ≫ s' := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry sq.w
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_comp_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp] at h
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
    l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (WeightedEndReedyKan.smallFamily q.lift)
    fac_left := ?_
    fac_right := ?_ }
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv (AsSmall.down ⋙ G) (AsSmall.down ⋙ X) A).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry
      (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (WeightedEndReedyKan.smallFamily q.lift)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
    apply NatTrans.ext
    funext j
    exact NatTrans.congr_app ht (AsSmall.down.obj j)
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv (AsSmall.down ⋙ F) (AsSmall.down ⋙ X) B).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (WeightedEndReedyKan.smallFamily q.lift) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (Functor.whiskerLeft AsSmall.down θ) (AsSmall.down ⋙ X)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_comp_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
    apply NatTrans.ext
    funext j
    exact NatTrans.congr_app hs (AsSmall.down.obj j)

end
end SerrePositivity.KST.Spectra.ReedyWeightCornerLifting
