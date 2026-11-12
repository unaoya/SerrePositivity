module

public import SerrePositivity.EInfinity.ComplexLimits.SemifreeResolutionValue
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeBaseChange

/-!
# K 平坦な台の semifree 解像度と係数拡大

## 概要
HA §3.2.2 の台の底変更を、既存の D(A) の semifree 置換から比較する。

## 方針
置換の augmentation を取り、両端が K 平坦であることから拡大後の擬同型性を得る。

## 規約
底の環準同型に平坦性を仮定しない。台の K 平坦性はこの段階では引数。

## 使われ方
`baseChange_forget` の厳密な局所化源上での自然同型の各成分。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory DifferentialGraded
open SerrePositivity.InfinityCategories

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- K 平坦な複体では、D(S) の実際の置換の augmentation は係数拡大後も擬同型。 -/
lemma complexSemifreeResolutionValueAugmentation_baseChange_quasiIso
    (X : Complex S) (hX : complexKFlat S X) :
    QuasiIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).map (complexSemifreeResolutionValueAugmentation S X)) := by
  let P := complexSemifreeResolutionValue S X
  have hP : complexKFlat S P.val :=
    moduleSemifree_objectwiseKFlat S PUnit.{1} (fun _ _ => complexKFlat_unit S)
      P.property PUnit.unit
  have := complexSemifreeResolutionValueAugmentation_quasiIso S X
  exact ScalarExtension.extension_quasiIso_of_kFlat_ends f hP hX
    (complexSemifreeResolutionValueAugmentation S X)

end SerrePositivity.EInfinity.ComplexLimits
