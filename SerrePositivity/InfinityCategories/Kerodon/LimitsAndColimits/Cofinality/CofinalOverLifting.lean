module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RightHornPullback
public import Mathlib.CategoryTheory.LiftingProperties.Over
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
概要：通常の slice 圏の持ち上げ性と単体集合の左右の持ち上げ性の接続。
方針：検査する正方形の底を下辺から指定し、必要なときは右辺を引き戻す。
規約：Over は通常の単体集合の圏の slice。∞ 圏の slice とは別。
使われ方：依存積との随伴により right anodyne 性を生成元から移送する。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：slice 内の全ての右ホーンに対する持ち上げ性から元の射は right fibration。
方針：単体集合の持ち上げ正方形を、下辺で指定した底上の正方形にする。
規約：底は任意の単体集合。
使われ方：引き戻しの右随伴が right fibration を保つことの生成元による検査。 -/
lemma cofinalRightFibration_of_over_lifting {B : SSet.{u}} {X Y : Over B} (q : X ⟶ Y)
    (hq : ∀ {A D : Over B} (i : A ⟶ D), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions i.left →
      HasLiftingProperty i q) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q.left := by
  constructor
  intro A D i hi
  constructor
  intro a b hs
  let D' : Over B := Over.mk (b ≫ Y.hom)
  let A' : Over B := Over.mk (i ≫ b ≫ Y.hom)
  let i' : A' ⟶ D' := Over.homMk i
  let a' : A' ⟶ X := Over.homMk a (by
    change a ≫ X.hom = i ≫ b ≫ Y.hom
    rw [← Over.w q, ← Category.assoc, hs.w, Category.assoc])
  let b' : D' ⟶ Y := Over.homMk b
  have := hq i' hi
  have hs' : CommSq a' i' q b' := ⟨by apply Over.OverMorphism.ext; exact hs.w⟩
  refine CommSq.HasLift.mk' { l := hs'.lift.left, fac_left := ?_, fac_right := ?_ }
  · exact congrArg (fun k ↦ k.left) hs'.fac_left
  · exact congrArg (fun k ↦ k.left) hs'.fac_right

/-- 概要：slice 内の全ての right fibration に対する持ち上げ性から元の射は right anodyne。
方針：任意の検査する right fibration を正方形の下辺へ引き戻して slice の射にする。
規約：単射性は別に仮定しない。
使われ方：依存積への随伴で得た slice 内の持ち上げ性を元の包含に戻す。 -/
lemma cofinalRightAnodyne_of_over_lifting {B : SSet.{u}} {A D : Over B} (i : A ⟶ D)
    (hi : ∀ {X Y : Over B} (q : X ⟶ Y), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q.left →
      HasLiftingProperty i q) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i.left := by
  intro X Z p hp
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p := ⟨hp⟩
  constructor
  intro a b hs
  let Q : Over B := Over.mk (pullback.snd p b ≫ D.hom)
  let q : Q ⟶ D := Over.homMk (pullback.snd p b)
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q.left :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_snd p b (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p))⟩
  let a' : A ⟶ Q := Over.homMk (pullback.lift a i.left hs.w) (by
    change pullback.lift a i.left hs.w ≫ (pullback.snd p b ≫ D.hom) = A.hom
    rw [← Category.assoc, pullback.lift_snd, Over.w i])
  have := hi q hq
  have hs' : CommSq a' i q (𝟙 D) := ⟨by
    apply Over.OverMorphism.ext
    change pullback.lift a i.left hs.w ≫ pullback.snd p b = i.left ≫ 𝟙 D.left
    rw [pullback.lift_snd, Category.comp_id]⟩
  refine CommSq.HasLift.mk' {
    l := hs'.lift.left ≫ pullback.fst p b
    fac_left := ?_
    fac_right := ?_ }
  · rw [← Category.assoc]
    have h := congrArg (fun k ↦ k.left) hs'.fac_left
    change i.left ≫ hs'.lift.left = pullback.lift a i.left hs.w at h
    rw [h, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    have h := congrArg (fun k ↦ k.left) hs'.fac_right
    change hs'.lift.left ≫ pullback.snd p b = 𝟙 D.left at h
    rw [h, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
