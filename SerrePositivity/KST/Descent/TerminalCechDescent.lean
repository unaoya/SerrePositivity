module

public import SerrePositivity.KST.Descent.CechMapLocality
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# 終対象の実際の指定 Čech 降下

## 概要
終対象とその定数図式の指定比較が、実際のホモトピー錐に対して弱同値になることを証明する。

## 方針
右随伴である重みつき錐は終対象を保ち、終対象の図式は射影的 fibrant である。
指定比較を通常の錐への同型と fibrant 図式の置換比較に分ける。

## 規約
添字圏の可縮性は要求しない。単なる通常の極限を Tot と同一視しない。

## 使われ方
論文 公理 (1)、補題 3.2・3.3 の空被覆の降下。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K : Type u) [SmallCategory K]

/-- 概要：終対象とその定数図式の恒等増強（公理 (1)）。
方針：実際の終対象を使う comma 対象。
規約：任意の添字圏で定義。使われ方：空被覆の比較先。 -/
def terminalAugmentedCechSpace : AugmentedCechDiagram K where
  left := ⊤_ SSet.{u}
  right := (Functor.const K).obj (⊤_ SSet.{u})
  hom := 𝟙 _

local instance : IsLocallyPresentable.{u} SSet.{u} :=
  WeightedCones.simplicialSet_isLocallyPresentable

variable [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{u})]

/-- 概要：終対象の定数図式は指定ホモトピー比較に関して実際に降下（公理 (1)）。
方針：重みつき錐の終対象保存と、fibrant 図式上の置換比較の弱同値を合成する。
規約：重みつき比較そのものを検査する。使われ方：空被覆からの空対象の値の判定。 -/
theorem terminalAugmentedCechSpace_descent :
    HasCechSpaceDescent K I J (terminalAugmentedCechSpace K) := by
  let D := (Functor.const K).obj (⊤_ SSet.{u})
  let R := WeightedCones.coneSpace K (HomotopyCones.weight K I J)
  let : R.IsRightAdjoint := (WeightedCones.adjunction K _).isRightAdjoint
  have hd : IsTerminal D := Functor.isTerminalConst K terminalIsTerminal
  have ht : IsTerminal (R.obj D) := hd.isTerminalObj R D
  let a := (weightedCechAugmentation K (HomotopyCones.weight K I J)
    (HomotopyCones.weightComparison K I J)).app (terminalAugmentedCechSpace K)
  have : IsIso a := isIso_of_isTerminal terminalIsTerminal ht a
  have ha : weakEquivalences SSet.{u} a := mem_weakEquivalences a
  have hD : let := Projective.modelCategory K I J; IsFibrant D := by
    apply (cechDiagram_isFibrant_iff K I J D).mpr
    intro k
    change IsFibrant (⊤_ SSet.{u})
    exact (isFibrant_iff_of_isTerminal (𝟙 (⊤_ SSet.{u})) terminalIsTerminal).mpr
      inferInstance
  have hr := HomotopyCones.comparison_weakEquivalence_of_fibrant K I J D hD
  exact (weakEquivalences SSet.{u}).comp_mem a _ ha hr

/-- 概要：任意の増強つき図式から終対象の増強つき図式への指定射（公理 (1)）。
方針：増強元と各成分で終対象への一意射を使う。
規約：指定増強の可換性も保持。使われ方：空被覆の実降下から元の値の弱可縮性を反映。 -/
def augmentedCechSpaceToTerminal (A : AugmentedCechDiagram K) :
    A ⟶ terminalAugmentedCechSpace K where
  left := terminal.from A.left
  right := (Functor.isTerminalConst K terminalIsTerminal).from A.right
  w := by
    apply NatTrans.ext
    funext k
    apply terminalIsTerminal.hom_ext

/-- 概要：全ての成分が終対象である実降下から増強元の弱可縮性が従う（公理 (1)）。
方針：終対象の実降下との比較で、各成分の一意射の同型を使う。
規約：増強元が実際に終対象とは主張しない。使われ方：空スキーム上の値から終対象への弱同値。 -/
theorem cechSpaceSource_weak_of_descent_of_terminal_components
    (A : AugmentedCechDiagram K) (hA : HasCechSpaceDescent K I J A)
    (ht : ∀ k, IsTerminal (A.right.obj k)) :
    weakEquivalences SSet.{u} (terminal.from A.left) := by
  let a := augmentedCechSpaceToTerminal K A
  apply cechSpaceMap_left_weak_of_descent K I J a hA
    (terminalAugmentedCechSpace_descent K I J)
  intro k
  have : IsIso (a.right.app k) := isIso_of_isTerminal (ht k) terminalIsTerminal _
  exact mem_weakEquivalences (a.right.app k)

end SerrePositivity.KST.Descent
