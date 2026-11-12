module

public import SerrePositivity.KST.Descent.TransferBaseChangeComposite
public import SerrePositivity.KST.Descent.TransferRankChartDescent

/-!
# 同じ局所 rank の式から全底変換の実降下

## 概要
元の有限 chart の正 rank の transfer 合成公式だけから、任意の底変換した射の実際の Čech 降下を証明する。

## 方針
元の Over 上の全成分の合成の弱同値を構成し、底変換後の合成の指定一致を使う。

## 規約
底変換ごとに別の chart・transfer・rank 公式を選び直さない。

## 使われ方
論文 補題 3.2・3.3 の混合 Čech の全行と有限平坦な細分。
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

/-- 概要：元の chart の正 rank の合成公式から全底変換の実 Čech 降下（補題 3.2）。
方針：元の合成の全対象の弱同値を、指定された底変換 transfer の合成へ制限する。
規約：新しい rank 公式を仮定しない。使われ方：混合 Čech 図式の各行の実降下。 -/
theorem BaseChangeTransfer.cechDescent_everyBaseChange_of_rankCharts
    (tr : BaseChangeTransfer f F) (c : FiniteTypeZariskiCover Y)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (rank : c.Index → ℕ) (positive : ∀ i, 0 < rank i)
    (hlocal : ∀ (i : c.Index) (T : Over Y) (_r : T ⟶ Over.mk (c.inclusion i)),
      (baseChangePresheafPullback f F ≫ tr.transfer).app (op T) =
        (rank i : ℚ) • 𝟙 ((overPresheaf (Y := Y) F).obj (op T)))
    {Z : FiniteTypeSchemes S} (g : Z ⟶ Y) :
    HasCechSpaceDescent SimplexCategory I J
      (cechAugmentedPresheafSpace (pullback.snd f g) (F ⋙ U)) := by
  have hc := overZariskiAction_weak_everywhere_of_fixedRankCharts c F U
    (baseChangePresheafPullback f F ≫ tr.transfer) I J hcof rank positive hlocal
  exact BaseChangeTransfer.cechDescent_of_weakComposite (pullback.snd f g) U I J
    (BaseChangeTransfer.baseChange f g F tr)
    (BaseChangeTransfer.baseChange_composite_weak f g F U tr hc) hcof

/-- 概要：元の有限自由 chart の正基底の式から全底変換の実降下（補題 3.2）。
方針：元の実際の被覆と正 rank を全底変換の降下へ渡す。
規約：局所 rank の式は射影公式からの明示した入力。使われ方：有限平坦な細分の全 Čech 行。 -/
theorem BaseChangeTransfer.cechDescent_everyBaseChange_of_finiteFreeChartRanks
    [IsFinite f.hom.left] [AlgebraicGeometry.Flat f.hom.left] [Surjective f.hom.left]
    [LocallyOfFinitePresentation f.hom.left] (tr : BaseChangeTransfer f F)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (hlocal : ∀ (i : finiteFreeChartIndices f.hom.left) (T : Over Y)
      (_r : T ⟶ Over.mk ((finiteFreeChartZariskiCover f).inclusion i)),
      (baseChangePresheafPullback f F ≫ tr.transfer).app (op T) =
        ((finiteFreeChartFamily f.hom.left i.val).rank : ℚ) •
          𝟙 ((overPresheaf (Y := Y) F).obj (op T)))
    {Z : FiniteTypeSchemes S} (g : Z ⟶ Y) :
    HasCechSpaceDescent SimplexCategory I J
      (cechAugmentedPresheafSpace (pullback.snd f g) (F ⋙ U)) :=
  BaseChangeTransfer.cechDescent_everyBaseChange_of_rankCharts f F U I J tr
    (finiteFreeChartZariskiCover f) hcof
    (fun i ↦ (finiteFreeChartFamily f.hom.left i.val).rank)
    (fun i ↦ (finiteFreeChartFamily f.hom.left i.val).positive) hlocal g

end SerrePositivity.KST.Descent
