module

public import SerrePositivity.KST.Descent.MixedCechRefinement
public import SerrePositivity.KST.Descent.DoubleCechDescentReflection
public import SerrePositivity.KST.Descent.SplitCechDescent

/-!
# 元の前層による混合 Čech の実際の二重増強空間図式

## 概要
幾何の混合 Čech を元の前層で写し、各行の増強元が変わる実際の二重増強空間図式にする。

## 方針
Mathlib の増強つき単体・余単体対象の反対圏の関手と前層による whiskering を使う。

## 規約
外側の全射についての自然性と元の基底からの指定増強を保持する。

## 使われ方
論文 補題 3.2・3.3 の混合 Čech の Fubini と細分。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ SSet.{0})

/-- 概要：元の前層で増強つき幾何図式を反変に写す実際の関手（補題 3.2）。
方針：増強つき単体対象を反対圏の余単体対象へ移し、同じ前層で写す。
規約：増強元と図式の全射を同時に写す。使われ方：混合 Čech の行の関手。 -/
def presheafAugmentedSpaces :
    (SimplicialObject.Augmented C)ᵒᵖ ⥤ AugmentedCechDiagram SimplexCategory :=
  simplicialToCosimplicialAugmented C ⋙
    CosimplicialObject.Augmented.whiskeringObj Cᵒᵖ SSet.{0} F

variable [HasFiniteLimits C] {X W Y : C} (f : X ⟶ Y) (g : W ⟶ Y)

/-- 概要：元の Čech 増強の像は切断に依存しない指定空間図式（補題 3.2）。
方針：指定基底射と前層の像の定義を検査する。
規約：全射と増強の指定同型。使われ方：各行の実降下への接続。 -/
def presheafAugmentedSpacesCechIso :
    (presheafAugmentedSpaces F).obj (op (Arrow.mk f).augmentedCechNerve) ≅
      cechAugmentedPresheafSpace f F := Iso.refl _

/-- 概要：混合 Čech の各行の実際の指定増強つき空間図式の関手（補題 3.2）。
方針：幾何の全行の関手を反対圏へ移し、同じ元の前層で写す。
規約：外側は g の Čech、内側は f の底変換の Čech。使われ方：実際の Fubini の行の入力。 -/
def mixedCechSpaceRows : SimplexCategory ⥤ AugmentedCechDiagram SimplexCategory :=
  (mixedAugmentedCech f g).rightOp ⋙ presheafAugmentedSpaces F

/-- 概要：元の前層による混合 Čech の実際の二重増強空間図式（補題 3.2）。
方針：各行の実際の関手へ、元の基底から g の Čech への指定増強を付加する。
規約：全体の増強元は元の基底の前層の値。使われ方：各行の実降下と外側の実降下の貼り合わせ。 -/
def mixedDoubleCechSpace : DoubleAugmentedCechDiagram SimplexCategory SimplexCategory where
  left := F.obj (op Y)
  right := mixedCechSpaceRows F f g
  hom := (cechAugmentedPresheafSpace g F).hom

/-- 概要：混合二重図式の外側は元の g の指定 Čech 図式（補題 3.2）。
方針：各行の増強元とその指定射は元の g の Čech の値であることを検査する。
規約：定義上の一致により指定増強も保つ。使われ方：外側の降下の入力と反映。 -/
def mixedDoubleCechSpaceOuterIso :
    DoubleAugmentedCechDiagram.outer SimplexCategory SimplexCategory (mixedDoubleCechSpace F f g) ≅
      cechAugmentedPresheafSpace g F := Iso.refl _

/-- 概要：混合図式の各行は実際の底変換被覆の指定 Čech 空間図式（補題 3.2）。
方針：底変換 Arrow と指定増強 Čech の定義を比較する。
規約：各行の増強元は元の g の Čech の段。使われ方：分裂降下と transfer の各行への適用。 -/
def mixedCechSpaceRowIso (n : SimplexCategory) :
    (mixedCechSpaceRows F f g).obj n ≅
      cechAugmentedPresheafSpace
        (pullback.snd f ((Arrow.mk g).augmentedCechNerve.hom.app (op n))) F := Iso.refl _

variable [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：細分する被覆の全 Čech 段で元の被覆の各行は実際に降下（補題 3.2・3.3）。
方針：零番目の射影からの実際の持ち上げで作った切断に、証明済みの分裂降下を適用する。
規約：切断を外側の全射に自然と仮定しない。使われ方：混合二重図式での外側の降下の反映。 -/
theorem mixedCechSpaceRows_descent_of_refinement (r : W ⟶ X) (hr : r ≫ f = g)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _) (n : SimplexCategory) :
    HasCechSpaceDescent SimplexCategory I J ((mixedCechSpaceRows F f g).obj n) :=
  (cechSpaceDescent_iso_iff SimplexCategory I J (mixedCechSpaceRowIso F f g n)).mpr
    (cechAugmentedPresheafSpace_descent_of_split _ F I J
      (mixedCechRefinementStageSplitEpi g f r hr (op n)) hcof)

/-- 概要：混合 Čech の全行が降下すれば積添字の実降下は元の外側 Čech の実降下と同値（補題 3.2・3.3）。
方針：実際の各行の関手と指定外側同型を、増強を保つ Fubini の反映へ渡す。
規約：外側の降下を先に仮定しない。使われ方：混合 Čech の両方向による細分の比較。 -/
theorem mixedDoubleCechSpace_descent_iff
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (hrows : ∀ n, HasCechSpaceDescent SimplexCategory I J
      ((mixedCechSpaceRows F f g).obj n)) :
    HasCechSpaceDescent (SimplexCategory × SimplexCategory) I J
        (DoubleAugmentedCechDiagram.flatten SimplexCategory SimplexCategory
          (mixedDoubleCechSpace F f g)) ↔
      HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace g F) :=
  (DoubleAugmentedCechDiagram.descent_iff_outer SimplexCategory SimplexCategory
    (mixedDoubleCechSpace F f g) I J hcof hrows).trans
    (cechSpaceDescent_iso_iff SimplexCategory I J (mixedDoubleCechSpaceOuterIso F f g))

/-- 概要：細分する被覆上の混合 Čech の実降下はその元の Čech の実降下と同値（補題 3.2・3.3）。
方針：細分射で各行の分裂降下を証明し、外側の実降下の反映へ渡す。
規約：分裂切断の外側自然性や各行の降下を追加仮定にしない。
使われ方：有限平坦な細分と元の被覆の二方向の比較。 -/
theorem mixedDoubleCechSpace_descent_iff_of_refinement (r : W ⟶ X) (hr : r ≫ f = g)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _) :
    HasCechSpaceDescent (SimplexCategory × SimplexCategory) I J
        (DoubleAugmentedCechDiagram.flatten SimplexCategory SimplexCategory
          (mixedDoubleCechSpace F f g)) ↔
      HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace g F) :=
  mixedDoubleCechSpace_descent_iff F f g I J hcof
    (mixedCechSpaceRows_descent_of_refinement F f g I J r hr hcof)

end SerrePositivity.KST.Descent
