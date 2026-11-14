module

public import SerrePositivity.Archive.KST.DescentConditional.MixedCechSpaceSwap

/-!
# 混合 Čech と実際の指定細分降下

## 概要
実際の混合 Čech の軸交換と両方向の Fubini を用い、細分から元の被覆の指定降下を反映する。

## 方針
細分射が与える側は各行の分裂降下を内部で証明し、他側の全行の実降下と比較する。

## 規約
τ 位相の層論を用いず、指定増強と独立なホモトピー極限の比較だけを使う。

## 使われ方
論文 補題 3.2・3.3 の有限平坦な細分・Zariski の細分・平坦化 blowup の接続。
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  (F : Cᵒᵖ ⥤ SSet.{0}) {X W Y : C} (f : X ⟶ Y) (g : W ⟶ Y)
  [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：二つの混合 Čech の軸交換で実際の指定降下は同値（補題 3.2・3.3）。
方針：指定増強を保つ空間同型と、積添字の交換同値の実際の添字随伴を使う。
規約：Tot の交換や降下の同値自体を追加仮定にしない。使われ方：細分の二方向の比較。 -/
theorem mixedDoubleCechSpace_swap_descent_iff
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _) :
    HasCechSpaceDescent (SimplexCategory × SimplexCategory) I J
        (DoubleAugmentedCechDiagram.flatten SimplexCategory SimplexCategory
          (mixedDoubleCechSpace F f g)) ↔
      HasCechSpaceDescent (SimplexCategory × SimplexCategory) I J
        (DoubleAugmentedCechDiagram.flatten SimplexCategory SimplexCategory
          (mixedDoubleCechSpace F g f)) :=
  (cechSpaceDescent_iso_iff (SimplexCategory × SimplexCategory) I J
    (mixedCechSpaceSwapIso F f g)).trans
    (CechReindex.descent_iff (SimplexCategory × SimplexCategory)
      (SimplexCategory × SimplexCategory) I J
      (CategoryTheory.Prod.braiding SimplexCategory SimplexCategory).toAdjunction hcof
      (DoubleAugmentedCechDiagram.flatten SimplexCategory SimplexCategory
        (mixedDoubleCechSpace F g f))).symm

/-- 概要：細分の全ての元の Čech 段での降下から両被覆の実降下を比較（補題 3.2・3.3）。
方針：細分上の分裂する各行、混合軸交換、他方向の全行の実降下の反映を合成する。
規約：他方向の各行の降下は入力に明示し、全体の降下を仮定に取り込まない。
使われ方：底変換後も降下する細分から元の実際の指定比較へ戻す。 -/
theorem cechSpaceDescent_refinement_iff (r : W ⟶ X) (hr : r ≫ f = g)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (hrows : ∀ n, HasCechSpaceDescent SimplexCategory I J
      ((mixedCechSpaceRows F g f).obj n)) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace g F) ↔
      HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace f F) :=
  (mixedDoubleCechSpace_descent_iff_of_refinement F f g I J r hr hcof).symm.trans
    ((mixedDoubleCechSpace_swap_descent_iff F f g I J hcof).trans
      (mixedDoubleCechSpace_descent_iff F g f I J hcof hrows))

/-- 概要：各基底変更で降下する細分の実降下から元の実際の Čech 降下（補題 3.2・3.3）。
方針：元の被覆の Čech 段への基底変更の降下を各行の指定同型で移す。
規約：要求する基底変更は元の Čech の全段。使われ方：有限平坦・Zariski 細分の適用。 -/
theorem cechSpaceDescent_of_refinement (r : W ⟶ X) (hr : r ≫ f = g)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (hbase : ∀ n : SimplexCategory,
      HasCechSpaceDescent SimplexCategory I J
        (cechAugmentedPresheafSpace
          (pullback.snd g ((Arrow.mk f).augmentedCechNerve.hom.app (Opposite.op n))) F))
    (hg : HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace g F)) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace f F) :=
  (cechSpaceDescent_refinement_iff F f g I J r hr hcof
    (fun n ↦ (cechSpaceDescent_iso_iff SimplexCategory I J
      (mixedCechSpaceRowIso F g f n)).mpr (hbase n))).mp hg

end SerrePositivity.KST.Descent
