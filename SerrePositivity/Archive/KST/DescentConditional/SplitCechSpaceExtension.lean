module

public import SerrePositivity.Archive.KST.DescentConditional.SplitCechExtension
public import SerrePositivity.Archive.KST.DescentConditional.InitialCechDescent

/-!
# 切断を持つ Čech の拡張図式の実際の降下

## 概要
切断を持つ射と元の空間値前層から、拡張添字上の実際の指定降下を証明する。

## 方針
指定増強を保持する空間図式を作り、始対象での指定基底同型と実際の始対象判定を使う。

## 規約
元の Čech への制限による降下の移行は別工程。拡張側の降下自体は仮定しない。

## 使われ方
論文 補題 3.2 の分裂余単体対象の実降下の拡張側。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen
open scoped Simplicial

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {X Y : C} (f : X ⟶ Y) (s : SplitEpi f) (F : Cᵒᵖ ⥤ SSet.{0})

/-- 概要：分裂 Čech の拡張と元の前層の値からの指定増強（補題 3.2）。
方針：構成済みの幾何拡張を元の前層で写して comma 圏へ束ねる。
規約：増強元は元の基底での前層の値。使われ方：実際のホモトピー比較の始対象判定。 -/
def splitCechAugmentedSpaceExtension : AugmentedCechDiagram BottomSimplex where
  left := F.obj (op Y)
  right := splitCechPresheafExtension f s F
  hom := splitCechPresheafExtensionAugmentation f s F

variable [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：分裂 Čech の拡張図式は実際の指定ホモトピー比較で降下（補題 3.2）。
方針：始対象での指定増強の同型性と、増強を保持する実際の重み変更を使う。
規約：元の図式の fibrancy や降下の追加入力は不要。
使われ方：添字変更の指定比較を介して元の Čech 降下へ戻す分裂側の証明。 -/
theorem splitCechAugmentedSpaceExtension_descent
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _) :
    HasCechSpaceDescent BottomSimplex I J (splitCechAugmentedSpaceExtension f s F) := by
  apply (cechSpaceDescent_initial_iff BottomSimplex ⟨⦋0⦌⟩ BottomSimplex.initial I J hcof _).mpr
  exact mem_weakEquivalences ((splitCechPresheafExtensionAugmentation f s F).app ⟨⦋0⦌⟩)

end SerrePositivity.KST.Descent
