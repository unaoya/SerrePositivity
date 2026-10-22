module

public import SerrePositivity.InfinityCategories.Stable.UniverseLimits
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone

/-!
概要：同じ元の余錐への後合成と宇宙持ち上げの厳密な可換性。
方針：元の余錐形状同型と持ち上げた全写像の合成を計算する。
規約：元の指定余錐そのものの等式。
使われ方：評価と空間の宇宙変更の合成による Yoneda 像の compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の後合成された余錐の宇宙持ち上げは、持ち上げた同じ全写像の後合成。 -/
lemma ulift_mapJoinCocone_val {K X Y : SSet.{u}} {D : K ⟶ X}
    (f : X ⟶ Y) (c : JoinCocone D) :
    (JoinCocone.ulift.{u, v} (mapJoinCocone f c)).val =
      (JoinCocone.ulift.{u, v} c).val ≫ (SSet.uliftFunctor.{v, u}).map f := by
  change _ ≫ (SSet.uliftFunctor.{v, u}).map (c.val ≫ f) = (_ ≫ _) ≫ _
  rw [Functor.map_comp, Category.assoc]

/-- 二段の元の後合成と宇宙持ち上げは、指定余錐として厳密に可換。 -/
lemma mapJoinCocone_universe_comp {K X Y : SSet.{u}} {Z : SSet.{max u v}}
    {D : K ⟶ X} (f : X ⟶ Y) (g : (SSet.uliftFunctor.{v, u}).obj Y ⟶ Z)
    (c : JoinCocone D) :
    mapJoinCocone ((SSet.uliftFunctor.{v, u}).map f ≫ g) (JoinCocone.ulift.{u, v} c) =
      mapJoinCocone g (JoinCocone.ulift.{u, v} (mapJoinCocone f c)) := by
  apply Subtype.ext
  change (JoinCocone.ulift.{u, v} c).val ≫ (_ ≫ _) =
    (JoinCocone.ulift.{u, v} (mapJoinCocone f c)).val ≫ g
  rw [ulift_mapJoinCocone_val, Category.assoc]

end SerrePositivity.InfinityCategories.F2.Compact
