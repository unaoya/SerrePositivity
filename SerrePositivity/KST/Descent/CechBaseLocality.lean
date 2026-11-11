module

public import SerrePositivity.KST.Descent.CechRefinementDescent

/-!
# 実際の指定 Čech 降下の基底上の局所性

## 概要
二つの方向の各行の実降下から、元の被覆と基底を局所化する被覆の指定 Čech 降下を比較する。

## 方針
各行の降下による外側の反映を、指定増強を保持する混合 Čech の軸交換で結ぶ。

## 規約
二つの被覆の間の細分射や持ち上げを要求しない。各行は実際の底変換 Čech の比較である。

## 使われ方
論文 補題 3.2 の有限平坦射の変動 rank を局所自由 chart 上の実降下から貼り合わせる。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  (F : Cᵒᵖ ⥤ SSet.{0}) {X W Y : C} (f : X ⟶ Y) (g : W ⟶ Y)
  [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：両方向の全行が実際に降下すれば二つの元の被覆の実降下は同値（補題 3.2）。
方針：二つの外側の反映を指定軸交換で結ぶ。
規約：被覆間の細分射は不要。使われ方：基底の Zariski 局所化から元の降下を反映する。 -/
theorem cechSpaceDescent_locality_iff
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (hrows : ∀ n, HasCechSpaceDescent SimplexCategory I J
      ((mixedCechSpaceRows F f g).obj n))
    (hother : ∀ n, HasCechSpaceDescent SimplexCategory I J
      ((mixedCechSpaceRows F g f).obj n)) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace f F) ↔
      HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace g F) :=
  ((mixedDoubleCechSpace_descent_iff F f g I J hcof hrows).symm.trans
    ((mixedDoubleCechSpace_swap_descent_iff F f g I J hcof).trans
      (mixedDoubleCechSpace_descent_iff F g f I J hcof hother))).symm

/-- 概要：基底の被覆と各基底変更での降下から元の実際の Čech 降下を得る（補題 3.2）。
方針：実際の底変換 Čech の各行を指定同型で移し、両方向の局所性を使う。
規約：元の被覆の降下自体は入力にしない。使われ方：局所自由 chart の有限被覆による貼り合わせ。 -/
theorem cechSpaceDescent_of_baseCover
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (hlocal : ∀ n : SimplexCategory, HasCechSpaceDescent SimplexCategory I J
      (cechAugmentedPresheafSpace
        (pullback.snd f ((Arrow.mk g).augmentedCechNerve.hom.app (op n))) F))
    (hother : ∀ n : SimplexCategory, HasCechSpaceDescent SimplexCategory I J
      (cechAugmentedPresheafSpace
        (pullback.snd g ((Arrow.mk f).augmentedCechNerve.hom.app (op n))) F))
    (hg : HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace g F)) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace f F) :=
  (cechSpaceDescent_locality_iff F f g I J hcof
    (fun n ↦ (cechSpaceDescent_iso_iff SimplexCategory I J
      (mixedCechSpaceRowIso F f g n)).mpr (hlocal n))
    (fun n ↦ (cechSpaceDescent_iso_iff SimplexCategory I J
      (mixedCechSpaceRowIso F g f n)).mpr (hother n))).mpr hg

end SerrePositivity.KST.Descent
