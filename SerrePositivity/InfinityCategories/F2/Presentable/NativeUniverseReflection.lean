module

public import SerrePositivity.InfinityCategories.F2.Presentable.FullyFaithfulConeReflection
public import SerrePositivity.InfinityCategories.F2.Presentable.NativeUniverseContinuity
public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalenceSmallLimits

/-!
概要：指定宇宙変更の充満忠実性から元の小さい空間値関手の保存性を回収する。
方針：指定全錐の像の普遍性を反映し、元の宇宙へ戻す。
規約：宇宙変更の充満忠実性は明示的な比較用入力で、ここでは存在を主張しない。
使われ方：Compact の反映界面から随伴関手定理の小さい Hom 保存性へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：指定宇宙変更後の κ-filtered 保存から元の関手の同じ保存性を反映する。
方針：元の全余錐の像を充満忠実な宇宙変更で反映し、持ち上げを戻す。
規約：同じ元の κ-filtered 形状と余錐を保持する。
使われ方：元の小さい Hom 関手の accessibility の判定。 -/
lemma isKappaAccessibleFunctor_of_spaceUniverse {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} {F : C ⟶ SpaceInfinity.{u}}
    (hU : IsFullyFaithful Compact.spaceUniverseDiagram.{u})
    (hF : Compact.PreservesKappaFilteredColimits.{u, u + 1} κ
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ Compact.spaceUniverseDiagram)) :
    IsKappaAccessibleFunctor κ F := by
  intro I hI hκ D c hc
  apply (isColimitCone_iff_ulift (mapJoinCocone F c)).mpr
  apply isColimitCone_of_fullyFaithful_image Compact.spaceUniverseDiagram hU
  have h := hF I D c hc
  rw [Compact.mapJoinCocone_universe_comp] at h
  exact h

/-- 概要：指定宇宙変更後の全小極限保存から元の空間値関手の保存性を反映する。
方針：元の全錐の像の普遍性を充満忠実性で反映して持ち上げを戻す。
規約：元の任意の小さい形状を保持する。
使われ方：元の小さい Hom 合成関手の極限保存性。 -/
lemma preservesSmallLimits_of_spaceUniverse
    {C : SSet.{u + 1}} {F : C ⟶ SpaceInfinity.{u}}
    (hU : IsFullyFaithful Compact.spaceUniverseDiagram.{u})
    (hF : ∀ (K : SSet.{u}) (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
      (c : JoinCone D), IsLimitCone c →
        IsLimitCone (mapJoinCone
          ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ Compact.spaceUniverseDiagram)
          (JoinCone.ulift c))) : PreservesSmallLimits F := by
  intro K D c hc
  apply (isLimitCone_iff_ulift (mapJoinCone F c)).mpr
  apply isLimitCone_of_fullyFaithful_image Compact.spaceUniverseDiagram hU
  have h := hF K D c hc
  rw [mapJoinCone_universe_comp] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable
