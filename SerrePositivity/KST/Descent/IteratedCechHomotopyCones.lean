module

public import SerrePositivity.KST.Descent.CechFibrantDiagrams

/-!
# 行と外側を独立に置換した反復ホモトピー極限

## 概要
共通 fibrant 置換後の反復錐空間から、各行・外側の実際のホモトピー極限への比較を構成する。

## 方針
各行の fibrancy と錐関手の右 Quillen 性を使い、二つの指定置換の比較を弱同値と示す。

## 規約
HomotopyCones の既存の実際の置換と比較を全て使う。普通の極限は用いない。

## 使われ方
論文 補題 3.2・3.3 の二重 Čech の導来 Fubini の独立な反復計算。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K L : Type u) [SmallCategory K] [SmallCategory L] [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

local instance : IsLocallyPresentable.{u} SSet.{u} :=
  WeightedCones.simplicialSet_isLocallyPresentable

/-- 概要：各行の実際の内側重みつき錐空間（論文 補題 3.2）。
方針：curry 後に内側の指定重みの右随伴を各行へ適用する。
規約：内側の fibrant 置換はまだ適用しない。使われ方：指定比較の始域。 -/
abbrev innerCechConeFunctor : (K × L ⥤ SSet.{u}) ⥤ (K ⥤ SSet.{u}) :=
  Functor.curry ⋙ (Functor.whiskeringRight K (L ⥤ SSet.{u}) SSet.{u}).obj
    (WeightedCones.coneSpace L (HomotopyCones.weight L I J))

/-- 概要：各行で実際のホモトピー極限を取る関手（論文 補題 3.2）。
方針：curry 後に既存の内側の実際の置換込みの関手を適用する。
規約：全ての外側の射に自然。使われ方：反復した実際のホモトピー極限。 -/
abbrev innerCechHomotopyLimit : (K × L ⥤ SSet.{u}) ⥤ (K ⥤ SSet.{u}) :=
  Functor.curry ⋙ (Functor.whiskeringRight K (L ⥤ SSet.{u}) SSet.{u}).obj
    (HomotopyCones.functor L I J)

/-- 概要：内側・外側を独立に置換した実際の反復ホモトピー極限（補題 3.2）。
方針：各行の実際の関手に外側の実際の関手を合成する。
規約：二方向の置換を別々に実行する。使われ方：導来 Fubini の反復側。 -/
abbrev iteratedCechHomotopyLimit : (K × L ⥤ SSet.{u}) ⥤ SSet.{u} :=
  innerCechHomotopyLimit K L I J ⋙ HomotopyCones.functor K I J

/-- 概要：各行の錐空間からその実際のホモトピー極限への自然な比較（補題 3.2）。
方針：既存の指定 fibrant 置換の比較を各行へ適用する。
規約：全ての外側の射への自然性を保持する。使われ方：反復計算の比較。 -/
abbrev innerCechConeComparison : innerCechConeFunctor K L I J ⟶
    innerCechHomotopyLimit K L I J :=
  Functor.whiskerLeft Functor.curry
    ((Functor.whiskeringRight K (L ⥤ SSet.{u}) SSet.{u}).map (HomotopyCones.comparison L I J))

/-- 概要：反復した生の錐空間から独立置換した反復ホモトピー極限への比較（補題 3.2）。
方針：外側の置換比較の後、各行の置換比較を外側の実際の関手で写す。
規約：順序と指定比較を固定する。使われ方：共通置換後の弱同値。 -/
abbrev iteratedCechConeComparison :
    iteratedCechConeSpace K L (HomotopyCones.weight K I J) (HomotopyCones.weight L I J) ⟶
      iteratedCechHomotopyLimit K L I J :=
  Functor.whiskerLeft (innerCechConeFunctor K L I J) (HomotopyCones.comparison K I J) ≫
    Functor.whiskerRight (innerCechConeComparison K L I J) (HomotopyCones.functor K I J)

/-- 概要：fibrant な二重図式の各行も実際の射影的模型で fibrant（補題 3.2）。
方針：積添字の成分判定を内側の成分判定へ渡す。
規約：各行の fibrancy を独立に仮定しない。使われ方：行の指定置換比較の弱同値。 -/
theorem cechFibrant_row (F : K × L ⥤ SSet.{u})
    (hF : let := Projective.modelCategory (K × L) I J; IsFibrant F) (k : K) :
    let := Projective.modelCategory L I J
    IsFibrant ((Functor.curry.obj F).obj k) := by
  have h := (cechDiagram_isFibrant_iff (K × L) I J F).mp hF
  exact (cechDiagram_isFibrant_iff L I J _).mpr (fun l ↦ h (k, l))

variable [IsQuillenBifunctor (curriedTensor SSet.{u})]

/-- 概要：fibrant な二重図式の内側錐空間の列も fibrant（論文 補題 3.2）。
方針：各行の fibrancy と指定 cofibrant 重みの右 Quillen 性を使う。
規約：外側で必要な fibrancy を結論として供給する。使われ方：外側の指定比較の弱同値。 -/
theorem innerCechConeFunctor_isFibrant (F : K × L ⥤ SSet.{u})
    (hF : let := Projective.modelCategory (K × L) I J; IsFibrant F) :
    let := Projective.modelCategory K I J
    IsFibrant ((innerCechConeFunctor K L I J).obj F) := by
  apply (cechDiagram_isFibrant_iff K I J _).mpr
  intro k
  have hrow := cechFibrant_row K L I J F hF k
  let := Projective.modelCategory L I J
  have := hrow
  have := HomotopyCones.coneSpace_isRightQuillen L I J
  have : (WeightedCones.coneSpace L (HomotopyCones.weight L I J)).IsRightAdjoint :=
    (WeightedCones.adjunction L (HomotopyCones.weight L I J)).isRightAdjoint
  exact Quillen.isFibrant_obj (WeightedCones.coneSpace L (HomotopyCones.weight L I J)) _

/-- 概要：fibrant な二重図式上の各行の比較は弱同値（論文 補題 3.2）。
方針：各行の fibrancy を既存の比較の定理へ適用する。
規約：指定された比較射を検査する。使われ方：外側の実際の関手による弱同値の保存。 -/
theorem innerCechConeComparison_weakEquivalence (F : K × L ⥤ SSet.{u})
    (hF : let := Projective.modelCategory (K × L) I J; IsFibrant F) (k : K) :
    weakEquivalences SSet.{u} (((innerCechConeComparison K L I J).app F).app k) :=
  HomotopyCones.comparison_weakEquivalence_of_fibrant L I J _ (cechFibrant_row K L I J F hF k)

/-- 概要：fibrant な二重図式上で反復錐の指定比較は弱同値（補題 3.2）。
方針：外側の比較と、各行の比較を写した弱同値を合成する。
規約：独立な反復置換の比較を仮定しない。使われ方：導来 Fubini の仕上げ。 -/
theorem iteratedCechConeComparison_weakEquivalence (F : K × L ⥤ SSet.{u})
    (hF : let := Projective.modelCategory (K × L) I J; IsFibrant F) :
    weakEquivalences SSet.{u} ((iteratedCechConeComparison K L I J).app F) := by
  have h₁ := HomotopyCones.comparison_weakEquivalence_of_fibrant K I J _
    (innerCechConeFunctor_isFibrant K L I J F hF)
  have h₂ := HomotopyCones.map_weakEquivalence K I J
    ((innerCechConeComparison K L I J).app F) (innerCechConeComparison_weakEquivalence K L I J F hF)
  exact (weakEquivalences SSet.{u}).comp_mem _ _ h₁ h₂

/-- 概要：実際の反復ホモトピー極限は各二重添字での弱同値を保存（補題 3.2）。
方針：内側の実際の関手の保存を各行で使い、外側の実際の関手の保存を適用する。
規約：図式の fibrancy は不要。使われ方：共通置換を最後に外す比較。 -/
theorem iteratedCechHomotopyLimit_map_weakEquivalence {F G : K × L ⥤ SSet.{u}} (f : F ⟶ G)
    (hf : ∀ k, weakEquivalences SSet.{u} (f.app k)) :
    weakEquivalences SSet.{u} ((iteratedCechHomotopyLimit K L I J).map f) := by
  apply HomotopyCones.map_weakEquivalence K I J
  intro k
  exact HomotopyCones.map_weakEquivalence L I J _ (fun l ↦ hf (k, l))

end SerrePositivity.KST.Descent
