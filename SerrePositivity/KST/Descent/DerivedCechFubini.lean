module

public import SerrePositivity.KST.Descent.IteratedCechHomotopyCones
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyLimit

/-!
# 単体集合の実際のホモトピー極限の導来 Fubini

## 概要
積添字の実際のホモトピー極限と、行・外側を独立に計算する実際の反復ホモトピー極限を自然同定する。

## 方針
共通置換後の重みつき Fubini、反復置換の指定比較の弱同値、共通置換を外す弱同値を合成する。

## 規約
単体集合の弱同値で局所化した後の自然同型を構成する。Sp 内の Tot の実現は L9 と接続する別工程。

## 使われ方
論文 補題 3.2・3.3 の τ 位相の層論を二重 Čech の Fubini 計算へ置換する機構。
-/

@[expose] public section

noncomputable section

universe u vH uH vD uD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K L : Type u) [SmallCategory K] [SmallCategory L] [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{u})]

local instance : IsLocallyPresentable.{u} SSet.{u} :=
  WeightedCones.simplicialSet_isLocallyPresentable

variable {H : Type uH} [Category.{vH} H]
  (Λ : SSet.{u} ⥤ H) [Λ.IsLocalization (weakEquivalences SSet.{u})]

/-- 概要：共通 fibrant 置換後の反復錐の比較は局所化後に自然同型（補題 3.2）。
方針：各図式に対する指定比較の弱同値を局所化する。
規約：各成分だけでなく関手全体の自然同型を構成する。
使われ方：共通置換と独立な行・外側の置換の接続。 -/
def fibrantIteratedCechComparisonIso :
    HomotopyCones.replacement (K × L) I J ⋙
        iteratedCechConeSpace K L (HomotopyCones.weight K I J) (HomotopyCones.weight L I J) ⋙ Λ ≅
      HomotopyCones.replacement (K × L) I J ⋙ iteratedCechHomotopyLimit K L I J ⋙ Λ := by
  let a := Functor.whiskerRight
    (Functor.whiskerLeft (HomotopyCones.replacement (K × L) I J)
      (iteratedCechConeComparison K L I J)) Λ
  have : ∀ F, IsIso (a.app F) := by
    intro F
    exact Localization.inverts Λ (weakEquivalences SSet.{u}) _
      (iteratedCechConeComparison_weakEquivalence K L I J _
        (HomotopyCones.replacement_isFibrant (K × L) I J F))
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

/-- 概要：反復した実際のホモトピー極限では共通置換を外せる（論文 補題 3.2）。
方針：指定置換比較の各二重添字での弱同値を反復関手で写し、局所化する。
規約：二つの反復計算に同じ指定比較を用いる。
使われ方：積添字と反復した実際のホモトピー極限の最終比較。 -/
def iteratedCechReplacementComparisonIso :
    iteratedCechHomotopyLimit K L I J ⋙ Λ ≅
      HomotopyCones.replacement (K × L) I J ⋙ iteratedCechHomotopyLimit K L I J ⋙ Λ := by
  let b := Functor.whiskerRight
    (Functor.whiskerRight (HomotopyCones.replacementComparison (K × L) I J)
      (iteratedCechHomotopyLimit K L I J)) Λ
  have : ∀ F, IsIso (b.app F) := by
    intro F
    exact Localization.inverts Λ (weakEquivalences SSet.{u}) _
      (iteratedCechHomotopyLimit_map_weakEquivalence K L I J _
        (HomotopyCones.replacementComparison_weakEquivalence (K × L) I J F))
  have : IsIso b := NatIso.isIso_of_isIso_app b
  exact asIso b

variable (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
  {D : Type uD} [Category.{vD} D] (Q : (K × L ⥤ SSet.{u}) ⥤ D)
  [Q.IsLocalization (Projective.objectwise (K × L) (weakEquivalences SSet.{u}))]
  (constant : H ⥤ D)
  (e : (Functor.const (K × L) : SSet.{u} ⥤ _) ⋙ Q ≅ Λ ⋙ constant)

/-- 概要：積添字の実際のホモトピー極限は実際の反復ホモトピー極限と自然同型（補題 3.2・3.3）。
方針：可縮外重みの計算、反復錐の指定比較、共通置換を外す比較を順に合成する。
規約：全ての図式の射に自然。通常の極限・次数ごとの群の極限・Tot との交換を仮定しない。
使われ方：二重 Čech の単体集合の模型における導来 Fubini。Sp への実現は別に接続する。 -/
def cechHomotopyLimitFubiniIso : HomotopyCones.functor (K × L) I J ⋙ Λ ≅
    iteratedCechHomotopyLimit K L I J ⋙ Λ :=
  homotopyCechWeightedFubiniIso K L I J hcof Λ Q constant e ≪≫
    fibrantIteratedCechComparisonIso K L I J Λ ≪≫
    (iteratedCechReplacementComparisonIso K L I J Λ).symm

/-- 概要：導来定数関手の比較を内部で構成した実際のホモトピー極限の Fubini（補題 3.2・3.3）。
方針：既存の局所化の普遍性から定数関手を降ろし、その指定比較を前の自然同型へ渡す。
規約：導来定数関手やその比較を追加の入力にしない。
使われ方：二重 Čech の実際の単体集合の計算への共通の入口。 -/
def cechHomotopyLimitFubiniCanonicalIso : HomotopyCones.functor (K × L) I J ⋙ Λ ≅
    iteratedCechHomotopyLimit K L I J ⋙ Λ :=
  cechHomotopyLimitFubiniIso K L I J Λ hcof Q
    (HomotopyLimit.localizedConstant (K × L) Λ Q)
    (HomotopyLimit.constantComparison (K × L) Λ Q)

end SerrePositivity.KST.Descent
