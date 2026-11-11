module

public import SerrePositivity.KST.Descent.OverRankCharts
public import SerrePositivity.KST.Descent.TransferWeakCechDescent

/-!
# Zariski 局所 rank を持つ transfer による実 Čech 降下

## 概要
公理 (1) と、有限 chart 上の正 rank の transfer 合成公式から、元の指定 Čech 比較の弱同値を証明する。

## 方針
同じ有限 chart を全基底変更へ引き戻して Over 上の合成の弱同値を証明し、
自身による底変換の分裂降下から実際の指定比較を戻す。

## 規約
大域の共通 rank、有限非交和保存、単一の Zariski 被覆射の降下は前提にしない。
局所 rank の式を射影公式から供給する工程は明示した入力として区別する。

## 使われ方
論文 公理 (1)・(4)、補題 3.2 の有限平坦 transfer の実際の降下。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra AlgebraicGeometry
open SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S}
  (f : X ⟶ Y) {V : Type v} [Category.{w} V] [Preadditive V] [Linear ℚ V]
  (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ V) (U : V ⥤ SSet.{0})
  [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]
  [FiniteZariskiCechDescent I J (F ⋙ U)]

/-- 概要：chart ごとの正 rank の合成公式から元の実際の Čech 降下（補題 3.2）。
方針：Over の全対象での合成の弱同値と、自身による底変換の分裂降下を使う。
規約：rank は成分ごとに異なってよい。使われ方：公理 (4) の局所自明化後の公式の接続。 -/
theorem BaseChangeTransfer.cechDescent_of_rankCharts (tr : BaseChangeTransfer f F)
    (c : FiniteTypeZariskiCover Y)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (rank : c.Index → ℕ) (positive : ∀ i, 0 < rank i)
    (hlocal : ∀ (i : c.Index) (Z : Over Y) (_r : Z ⟶ Over.mk (c.inclusion i)),
      (baseChangePresheafPullback f F ≫ tr.transfer).app (op Z) =
        (rank i : ℚ) • 𝟙 ((overPresheaf (Y := Y) F).obj (op Z))) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace f (F ⋙ U)) :=
  BaseChangeTransfer.cechDescent_of_weakComposite f U I J tr
    (overZariskiAction_weak_everywhere_of_fixedRankCharts c F U
      (baseChangePresheafPullback f F ≫ tr.transfer) I J hcof rank positive hlocal) hcof

/-- 概要：実際の有限自由 chart 上の正基底の公式から有限平坦射の実降下（補題 3.2）。
方針：構成済みの被覆と元の正基底の本数を、変動 rank の実降下に渡す。
規約：transfer と局所式は明示した法則の入力。射影公式の実現の完成とは区別する。
使われ方：有限平坦な細分と主定理の平坦化段階への接続。 -/
theorem BaseChangeTransfer.cechDescent_of_finiteFreeChartRanks
    [IsFinite f.hom.left] [AlgebraicGeometry.Flat f.hom.left] [Surjective f.hom.left]
    [LocallyOfFinitePresentation f.hom.left] (tr : BaseChangeTransfer f F)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (hlocal : ∀ (i : finiteFreeChartIndices f.hom.left) (Z : Over Y)
      (_r : Z ⟶ Over.mk ((finiteFreeChartZariskiCover f).inclusion i)),
      (baseChangePresheafPullback f F ≫ tr.transfer).app (op Z) =
        ((finiteFreeChartFamily f.hom.left i.val).rank : ℚ) •
          𝟙 ((overPresheaf (Y := Y) F).obj (op Z))) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace f (F ⋙ U)) :=
  BaseChangeTransfer.cechDescent_of_rankCharts f F U I J tr (finiteFreeChartZariskiCover f)
    hcof (fun i ↦ (finiteFreeChartFamily f.hom.left i.val).rank)
    (fun i ↦ (finiteFreeChartFamily f.hom.left i.val).positive) hlocal

end SerrePositivity.KST.Descent
