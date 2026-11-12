module
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeSimplex
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeSimplexAugmentation

/-!
概要：元の実 cone と同じ augmentation に、終端 X を追加した実二重 cone 単体を作る。
方針：全 HA を証明した右 cone 構成へ、元の全 cochain augmentation をそのまま代入する。
規約：全三角形と大域自然性は別に検証する。使われ方：元の大域 cone 射の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorDoubleConeSimplex {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n + 2) :=
  complexRightConeSimplex A (normalizedTensorConeSimplexAugmentation A X Y c)

lemma normalizedTensorDoubleConeSimplex_front {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (normalizedTensorDoubleConeSimplex A X Y c).pullback Fin.castSuccOrderEmb.toOrderHom =
      normalizedTensorConeSimplex A X Y c :=
  complexRightConeSimplex_front A (normalizedTensorConeSimplexAugmentation A X Y c)

lemma normalizedTensorDoubleConeSimplex_last {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (normalizedTensorDoubleConeSimplex A X Y c).obj (Fin.last (n + 2)) = X :=
  complexRightConeObj_last A (normalizedTensorConeSimplex A X Y c) X

end SerrePositivity.EInfinity.ComplexLimits
