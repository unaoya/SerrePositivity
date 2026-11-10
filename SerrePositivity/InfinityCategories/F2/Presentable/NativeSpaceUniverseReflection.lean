module

public import SerrePositivity.InfinityCategories.F2.Presentable.NativeUniverseReflection
public import SerrePositivity.InfinityCategories.F2.Presentable.SpaceUniverseLimitReflection
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseColimitReflection

/-!
概要：元の小さい空間値関手の保存性を指定宇宙変更から無条件に反映する。
方針：各指定錐に小極限・小余極限の反映を適用する。
規約：充満忠実性の入力を使わず、元の関手と形状を保持する。
使われ方：随伴関手定理の小さい Hom の連続性と accessibility。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：宇宙変更後の κ-filtered 保存は元の関手の同じ保存を含意する。
方針：元の指定余錐の像の普遍性を反映する。
規約：元の κ と形状を保持する。使われ方：小さい Hom の accessibility。 -/
lemma isKappaAccessibleFunctor_of_spaceUniverse_image {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} {F : C ⟶ SpaceInfinity.{u}}
    (hF : Compact.PreservesKappaFilteredColimits.{u, u + 1} κ
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ Compact.spaceUniverseDiagram)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ F := by
  intro I hI hκ D c hc
  apply Compact.spaceUniverseDiagram_reflects_small_isColimit
  have h := hF I D c hc
  rw [Compact.mapJoinCocone_universe_comp] at h
  exact h

/-- 概要：宇宙変更後の全小極限保存は元の関手の全小極限保存を含意する。
方針：各元の指定全錐に小極限反映を適用する。
規約：形状の充填性を追加しない。使われ方：小さい Hom の連続性。 -/
lemma preservesSmallLimits_of_spaceUniverse_image
    {C : SSet.{u + 1}} {F : C ⟶ SpaceInfinity.{u}}
    (hF : ∀ (K : SSet.{u}) (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
      (c : JoinCone D), IsLimitCone c →
        IsLimitCone (mapJoinCone
          ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ Compact.spaceUniverseDiagram)
          (JoinCone.ulift c))) : PreservesSmallLimits F := by
  intro K D c hc
  apply spaceUniverseDiagram_reflects_small_isLimit
  have h := hF K D c hc
  rw [mapJoinCone_universe_comp] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable
