module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ComplexRightConeSimplex
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeSimplexAugmentation

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorDoubleConeSimplex {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n + 2) :=
  _root_.SerrePositivity.ComplexLimits.complexRightConeSimplex A (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplexAugmentation A X Y c)

lemma normalizedTensorDoubleConeSimplex_front {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c).pullback Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c :=
  _root_.SerrePositivity.ComplexLimits.complexRightConeSimplex_front A (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplexAugmentation A X Y c)

lemma normalizedTensorDoubleConeSimplex_last {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c).obj (Fin.last (n + 2)) = X :=
  _root_.SerrePositivity.ComplexLimits.complexRightConeObj_last A (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c) X

end SerrePositivity.ComplexLimits
