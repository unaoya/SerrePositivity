module

public import SerrePositivity.KST.Descent.TransferBaseChange
public import SerrePositivity.Archive.KST.DescentConditional.TransferCechDescent

/-!
# 自然な正 rank transfer の全基底変更での実際の降下

## 概要
自然な transfer と一つの正 rank 公式から、任意の基底変更後の実際の指定 Čech 降下を証明する。

## 方針
実際に制限した transfer と証明済みの rank 保存を、分裂降下と retract の定理へ渡す。

## 規約
底変換後の transfer・rank 公式・降下を追加仮定にしない。元の前層を全ての基底変更で使う。

## 使われ方
論文 補題 3.2・3.3 の有限平坦な細分と局所自由 chart 上の各 Čech 段。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v w t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {V : Type w} [Category.{t} V] [Preadditive V] [Linear ℚ V]
  {X Y : C} (f : X ⟶ Y) (U : V ⥤ SSet.{0})
  [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：自然な正 rank transfer を持つ射の任意の基底変更は実際に Čech 降下（補題 3.2）。
方針：二重引き戻しの指定同型で transfer を制限し、同じ rank の保存と分裂降下を使う。
規約：元の一つの自然な rank 公式だけを入力する。使われ方：細分降下の他方向の全行の実降下。 -/
theorem BaseChangeTransfer.cechDescent_everyBaseChange
    {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (rank_identity : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F))
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    {Z : C} (g : Z ⟶ Y) :
    HasCechSpaceDescent SimplexCategory I J
      (cechAugmentedPresheafSpace (pullback.snd f g) (F ⋙ U)) :=
  BaseChangeTransfer.cechDescent_of_rank (pullback.snd f g) U I J
    (BaseChangeTransfer.baseChange f g F tr) rank positive
    (BaseChangeTransfer.baseChange_rank_identity f g F tr rank rank_identity) hcof

end SerrePositivity.KST.Descent
