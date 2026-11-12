module

public import SerrePositivity.KST.Descent.CechBaseChangeSpaces

/-!
# 正の局所 rank を持つ transfer による実際の Čech 降下

## 概要
自然な transfer と正の rank 公式から、元の前層の実際の指定 Čech 比較の弱同値を証明する。

## 方針
元の前層の retract を増強つき空間図式で写し、実際の底変換被覆の分裂降下から戻す。

## 規約
transfer と自然な rank 公式は明示した入力。分裂降下や底変換比較の同値自体は仮定しない。

## 使われ方
論文 補題 3.2 の有限平坦射の定 rank の場合と、有限平坦な細分からの実降下の移行。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v w t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {V : Type w} [Category.{t} V] [Preadditive V] [Linear ℚ V]
  {W X Y : C} (cover : W ⟶ Y) (f : X ⟶ Y)
  (U : V ⥤ SSet.{0}) [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：自然な transfer と分裂した底変換被覆から元の実際の Čech 降下を得る（補題 3.2）。
方針：元の前層の retract、底変換の指定空間同型、証明済みの分裂降下を合成する。
規約：rank は正の自然数で公式は前層の自然変換の等式。使われ方：有限平坦な細分への適用。 -/
theorem BaseChangeTransfer.cechDescent_of_splitBaseChange
    {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (rank_identity : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F))
    (s : SplitEpi (pullback.snd cover f))
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace cover (F ⋙ U)) := by
  have hb := (cechSpaceDescent_iso_iff SimplexCategory I J
    (cechBaseChangedPresheafSpaceIso U cover f F)).mpr
      (cechAugmentedPresheafSpace_descent_of_split (pullback.snd cover f) (F ⋙ U) I J s hcof)
  have ho := cechSpaceDescent_of_retract SimplexCategory I J
    ((BaseChangeTransfer.retract f tr rank positive rank_identity).map
      (presheafCosimplicialSpaces (cechOverDiagram cover) U)) hb
  exact (cechSpaceDescent_iso_iff SimplexCategory I J
    (cechOverPresheafSpaceIso U cover F)).mp ho

/-- 概要：被覆への持ち上げがある transfer から元の実際の Čech 降下を得る（補題 3.2）。
方針：実際の引き戻しの切断を持ち上げと恒等射から内部で構成する。
規約：点上の切断ではなく幾何の射と可換式を要求。使われ方：有限平坦な Čech 細分。 -/
theorem BaseChangeTransfer.cechDescent_of_lift
    {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (rank_identity : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F))
    (lift : X ⟶ W) (comm : lift ≫ cover = f)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace cover (F ⋙ U)) :=
  BaseChangeTransfer.cechDescent_of_splitBaseChange cover f U I J tr rank positive rank_identity
    (baseChangeSplitEpi cover f lift comm) hcof

/-- 概要：自然な正 rank の transfer を持つ射は元の実際の Čech 比較で降下（補題 3.2）。
方針：自身による底変換の対角切断と、構成済みの実際の transfer 移行を使う。
規約：有限平坦射の場合は transfer 公理と局所 rank 公式をこの入力へ接続する。
使われ方：定 rank の有限平坦降下の実際のホモトピー比較。 -/
theorem BaseChangeTransfer.cechDescent_of_rank
    {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (rank_identity : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F))
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace f (F ⋙ U)) :=
  BaseChangeTransfer.cechDescent_of_lift f f U I J tr rank positive rank_identity
    (𝟙 X) (Category.id_comp f) hcof

end SerrePositivity.KST.Descent
