module

public import SerrePositivity.Archive.KST.DescentConditional.TransferRankChartDescent

/-!
# 局所 rank を持つ transfer から細分先の実降下

## 概要
正 rank の有限 chart の合成公式を持つ射が元の被覆へ持ち上がれば、その元の被覆も実際に降下する。

## 方針
Over の全対象での transfer 合成の弱同値を使い、持ち上げから底変換被覆の切断を構成する。

## 規約
元の被覆の降下や分裂後の降下を仮定しない。指定比較の弱同値を結論にする。

## 使われ方
論文 補題 3.2・3.3 の有限平坦な細分と平坦化 blowup 後の実際の Čech 比較。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra AlgebraicGeometry
open SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {W X Y : FiniteTypeSchemes S}
  (cover : W ⟶ Y) (f : X ⟶ Y) {V : Type v} [Category.{w} V] [Preadditive V] [Linear ℚ V]
  (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ V) (U : V ⥤ SSet.{0})
  [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]
  [FiniteZariskiCechDescent I J (F ⋙ U)]

/-- 概要：局所 rank の transfer を持つ射からの持ち上げで元の被覆の実降下（補題 3.2・3.3）。
方針：元の合成の全成分の弱同値と、持ち上げからの実際の底変換切断を使う。
規約：同じ元の前層と指定比較を保持。使われ方：有限平坦な細分の降下の移行。 -/
theorem BaseChangeTransfer.cechDescent_of_rankCharts_of_lift
    (tr : BaseChangeTransfer f F) (c : FiniteTypeZariskiCover Y)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (rank : c.Index → ℕ) (positive : ∀ i, 0 < rank i)
    (hlocal : ∀ (i : c.Index) (T : Over Y) (_r : T ⟶ Over.mk (c.inclusion i)),
      (baseChangePresheafPullback f F ≫ tr.transfer).app (op T) =
        (rank i : ℚ) • 𝟙 ((overPresheaf (Y := Y) F).obj (op T)))
    (lift : X ⟶ W) (comm : lift ≫ cover = f) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace cover (F ⋙ U)) :=
  BaseChangeTransfer.cechDescent_of_weakComposite_of_splitBaseChange cover f U I J tr
    (overZariskiAction_weak_everywhere_of_fixedRankCharts c F U
      (baseChangePresheafPullback f F ≫ tr.transfer) I J hcof rank positive hlocal)
    (baseChangeSplitEpi cover f lift comm) hcof

/-- 概要：有限自由 chart の元の rank の式から細分先の実 Čech 降下（補題 3.2・3.3）。
方針：元の有限平坦射の実際の被覆と正基底を、持ち上げによる実降下へ渡す。
規約：局所式の射影公式からの供給は明示した入力。使われ方：構成済みの有限平坦な細分との接続。 -/
theorem BaseChangeTransfer.cechDescent_of_finiteFreeChartRanks_of_lift
    [IsFinite f.hom.left] [AlgebraicGeometry.Flat f.hom.left] [Surjective f.hom.left]
    [LocallyOfFinitePresentation f.hom.left] (tr : BaseChangeTransfer f F)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (hlocal : ∀ (i : finiteFreeChartIndices f.hom.left) (T : Over Y)
      (_r : T ⟶ Over.mk ((finiteFreeChartZariskiCover f).inclusion i)),
      (baseChangePresheafPullback f F ≫ tr.transfer).app (op T) =
        ((finiteFreeChartFamily f.hom.left i.val).rank : ℚ) •
          𝟙 ((overPresheaf (Y := Y) F).obj (op T)))
    (lift : X ⟶ W) (comm : lift ≫ cover = f) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace cover (F ⋙ U)) :=
  BaseChangeTransfer.cechDescent_of_rankCharts_of_lift cover f F U I J tr
    (finiteFreeChartZariskiCover f) hcof
    (fun i ↦ (finiteFreeChartFamily f.hom.left i.val).rank)
    (fun i ↦ (finiteFreeChartFamily f.hom.left i.val).positive) hlocal lift comm

end SerrePositivity.KST.Descent
