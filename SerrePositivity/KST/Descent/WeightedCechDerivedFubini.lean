module

public import SerrePositivity.KST.Descent.WeightedCechDerivedComparison

/-!
# 実際のホモトピー極限と反復した重みつき錐空間の比較

## 概要
積添字の実際のホモトピー極限を、共通の fibrant 置換後に反復した錐空間で計算する。

## 方針
指定外重みの cofibrancy と可縮増強から重み変更を行い、右随伴の Fubini を合成する。

## 規約
単体集合と図式の弱同値での局所化後の自然同型。
共通の fibrant 置換を固定し、各行・外側の実際の置換との比較と Sp 内の Tot への接続は別に残す。

## 使われ方
論文 補題 3.2・3.3 の二重 Čech と、τ 位相の層論を置換する導来 Fubini の計算。
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
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)

local instance : IsLocallyPresentable.{u} SSet.{u} :=
  WeightedCones.simplicialSet_isLocallyPresentable

variable {H : Type uH} [Category.{vH} H] {D : Type uD} [Category.{vD} D]
  (Λ : SSet.{u} ⥤ H) [Λ.IsLocalization (weakEquivalences SSet.{u})]
  (Q : (K × L ⥤ SSet.{u}) ⥤ D)
  [Q.IsLocalization (Projective.objectwise (K × L) (weakEquivalences SSet.{u}))]
  (constant : H ⥤ D)
  (e : (Functor.const (K × L) : SSet.{u} ⥤ _) ⋙ Q ≅ Λ ⋙ constant)

/-- 概要：指定外重みは積添字の実際のホモトピー極限を計算する（補題 3.2）。
方針：構成した cofibrant な可縮外重みを、導来右随伴の重み変更へ渡す。
規約：外重みの導来性を追加仮定にしない。
使われ方：錐空間の Fubini を実際のホモトピー極限へ接続する。 -/
def homotopyCechProductWeightComparisonIso :
    CofibrantCechWeight.weightedFunctor (K × L) I J
        (homotopyCechProductWeight K L I J) ⋙ Λ ≅
      HomotopyCones.functor (K × L) I J ⋙ Λ :=
  CofibrantCechWeight.comparisonIso (K × L) I J (homotopyCechProductWeight K L I J)
    (homotopyCechProductWeight_isCofibrant K L I J)
    (externalCechWeightAugmentation K L (HomotopyCones.weightComparison K I J)
      (HomotopyCones.weightComparison L I J))
    (homotopyCechProductWeightAugmentation_weakEquivalence K L hcof I J)
    hcof Λ Q constant e

/-- 概要：実際の積添字ホモトピー極限と共通置換後の反復錐空間は自然同型（補題 3.2・3.3）。
方針：実際の重み変更と実際の右随伴の Fubini を合成する。
規約：各行と外側を別々に fibrant 置換する形との比較はまだ別に必要。
使われ方：二重 Čech の Fubini の導来側の比較。 -/
def homotopyCechWeightedFubiniIso :
    HomotopyCones.functor (K × L) I J ⋙ Λ ≅
      HomotopyCones.replacement (K × L) I J ⋙
        iteratedCechConeSpace K L (HomotopyCones.weight K I J)
          (HomotopyCones.weight L I J) ⋙ Λ :=
  (homotopyCechProductWeightComparisonIso K L I J hcof Λ Q constant e).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (HomotopyCones.replacement (K × L) I J)
        (weightedCechFubiniIso K L (HomotopyCones.weight K I J)
          (HomotopyCones.weight L I J))) Λ

end SerrePositivity.KST.Descent
