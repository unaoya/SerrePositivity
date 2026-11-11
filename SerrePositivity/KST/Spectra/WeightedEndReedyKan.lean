module

public import SerrePositivity.KST.Spectra.WeightTensorCofibrancy
public import SerrePositivity.KST.Spectra.CosimplicialHornFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor

/-!
概要：Reedy cofibrant な重みと Reedy fibrant な係数の weighted end は Kan。
方針：end のホーンを通常の余単体圏の tensor の族に戻し、Reedy の全次数の持ち上げを curry する。
規約：係数の各段の Kan 性だけでは代用しない。AsSmall は宇宙を合わせるために使う。
使われ方：Goerss–Jardine VII §4。置換した重みの比較を実際の π 同型へ移す。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.Reedy
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.WeightedEndReedyKan
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- パラメーター付きの余単体族を AsSmall 上へ付け替える。 -/
def smallFamily {W X : CosimplicialObject SSet.{u}} {A : SSet.{u}}
    (a : WeightTensorLatching.diagram W A ⟶ X) :
    (AsSmall.down ⋙ W) ⊗ (Functor.const _).obj A ⟶ AsSmall.down ⋙ X where
  app i := a.app (AsSmall.down.obj i)
  naturality _ _ f := a.naturality (AsSmall.down.map f)

/-- AsSmall 上のパラメーター付き族を元の余単体圏へ戻す。 -/
def ordinaryFamily {W X : CosimplicialObject SSet.{u}} {A : SSet.{u}}
    (a : (AsSmall.down ⋙ W) ⊗ (Functor.const _).obj A ⟶ AsSmall.down ⋙ X) :
    WeightTensorLatching.diagram W A ⟶ X where
  app j := a.app (AsSmall.up.obj j)
  naturality _ _ f := a.naturality (AsSmall.up.map f)

/-- 重みと係数の実際の Reedy 条件から全ての end のホーンを充填する。 -/
lemma kanComplex (W X : CosimplicialObject SSet.{u})
    (hW : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) (initial.to W))
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp (terminal.from X)) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (AsSmall.down ⋙ W) (AsSmall.down ⋙ X)) := by
  let := CosimplicialHornFactorization.hornWeakFactorization.{u}
  apply (isFibrant_iff _).mpr
  apply (modelCategoryQuillen.fibration_iff _).mpr
  intro A B i hi
  have hai : anodyneExtensions i := by
    rw [anodyneExtensions_eq_llp_rlp]
    exact MorphismProperty.le_llp_rlp modelCategoryQuillen.J i hi
  have hir := WeightTensorLatching.map_reedy_anodyne W hW i hai
  let : ∀ j, HasLiftingProperty (relativeLatchingMap simplex j (WeightTensorLatching.map W i))
      (relativeMatchingMap simplex j (terminal.from X)) := fun j ↦
    MorphismProperty.hasLiftingProperty_of_wfs _ _ (hir j) (hX j)
  let : HasLiftingProperty (WeightTensorLatching.map W i) (terminal.from X) :=
    Lifting.hasLiftingProperty simplex
  constructor
  intro a b sq
  let q : CommSq (ordinaryFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry a))
      (WeightTensorLatching.map W i) (terminal.from X) (terminal.from _) :=
    ⟨terminal.hom_ext _ _⟩
  refine CommSq.HasLift.mk' {
    l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (smallFamily q.lift)
    fac_left := ?_
    fac_right := terminal.hom_ext _ _ }
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv (AsSmall.down ⋙ W) (AsSmall.down ⋙ X) A).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (smallFamily q.lift)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
  apply NatTrans.ext
  funext j
  exact NatTrans.congr_app q.fac_left (AsSmall.down.obj j)

end
end SerrePositivity.KST.Spectra.WeightedEndReedyKan
