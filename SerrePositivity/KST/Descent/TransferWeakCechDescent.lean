module

public import SerrePositivity.KST.Descent.CechBaseChangeSpaces
public import SerrePositivity.KST.Descent.CechWeakTransfer

/-!
# 全対象で弱同値な transfer の合成による実際の降下

## 概要
Over 上の pullback と transfer の合成が全対象で弱同値なら、分裂した底変換から元の Čech 降下を戻す。

## 方針
実際の前層の二つの自然変換を増強つき図式へ写し、局所化後の合成の逆で指定比較を正規化する。

## 規約
元の値域の線形性や共通の大域 rank は要求しない。

## 使われ方
論文 補題 3.2 の chart ごとに異なる rank を持つ有限平坦 transfer。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v w t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra
open SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {V : Type w} [Category.{t} V] {W X Y : C} (cover : W ⟶ Y) (f : X ⟶ Y)
  (U : V ⥤ SSet.{0}) [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：全対象で弱同値な transfer の合成と分裂した底変換から元の実降下を得る（補題 3.2）。
方針：実際の図式関手で自然変換を写し、指定比較の局所化後の retract を使う。
規約：成分ごとに別の rank でよい。使われ方：局所 chart の rank 公式からの有限平坦降下。 -/
theorem BaseChangeTransfer.cechDescent_of_weakComposite_of_splitBaseChange
    {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (hcomp : ∀ Z : Over Y, weakEquivalences SSet.{0}
      (U.map ((baseChangePresheafPullback f F ≫ tr.transfer).app (op Z))))
    (s : SplitEpi (pullback.snd cover f))
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace cover (F ⋙ U)) := by
  let T := presheafCosimplicialSpaces (cechOverDiagram cover) U
  let i := T.map (baseChangePresheafPullback f F)
  let r := T.map tr.transfer
  have hb := (cechSpaceDescent_iso_iff SimplexCategory I J
    (cechBaseChangedPresheafSpaceIso U cover f F)).mpr
      (cechAugmentedPresheafSpace_descent_of_split (pullback.snd cover f) (F ⋙ U) I J s hcof)
  have hl : weakEquivalences SSet.{0} (i ≫ r).left := by
    change weakEquivalences SSet.{0}
      (U.map ((baseChangePresheafPullback f F).app (op (Over.mk (𝟙 Y)))) ≫
        U.map (tr.transfer.app (op (Over.mk (𝟙 Y)))))
    rw [← U.map_comp]
    exact hcomp _
  have hr : ∀ n : SimplexCategory, weakEquivalences SSet.{0} ((i ≫ r).right.app n) := by
    intro n
    change weakEquivalences SSet.{0}
      (U.map ((baseChangePresheafPullback f F).app (op ((cechOverDiagram cover).obj (op n)))) ≫
        U.map (tr.transfer.app (op ((cechOverDiagram cover).obj (op n)))))
    rw [← U.map_comp]
    exact hcomp _
  have ho := cechSpaceDescent_of_weakComposite SimplexCategory I J i r hl hr hb
  exact (cechSpaceDescent_iso_iff SimplexCategory I J
    (cechOverPresheafSpaceIso U cover F)).mp ho

/-- 概要：全対象で弱同値な自然な transfer の合成から元の射の実降下（補題 3.2）。
方針：自身による底変換の対角切断を使う。
規約：共通 rank を要求しない。使われ方：有限 Zariski 被覆の局所 rank の式への接続。 -/
theorem BaseChangeTransfer.cechDescent_of_weakComposite
    {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (hcomp : ∀ Z : Over Y, weakEquivalences SSet.{0}
      (U.map ((baseChangePresheafPullback f F ≫ tr.transfer).app (op Z))))
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace f (F ⋙ U)) :=
  BaseChangeTransfer.cechDescent_of_weakComposite_of_splitBaseChange f f U I J tr hcomp
    (baseChangeSplitEpi f f (𝟙 X) (Category.id_comp f)) hcof

end SerrePositivity.KST.Descent
