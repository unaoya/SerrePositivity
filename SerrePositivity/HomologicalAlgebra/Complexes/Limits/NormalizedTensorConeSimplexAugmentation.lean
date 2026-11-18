module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ComplexSimplexAugmentation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeAugmentationCompatibility
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeSimplexMap

/-!
概要：元の全次数の実 cone 単体に、同じ先端 X への検証済み全斉次 augmentation を与える。
方針：同じ元の対象ごとの射と、全有限集合・全次数での元の合成式を代入する。
規約：終端 cone や全三角形を未証明の入力にしない。使われ方：元の二重 cone の構成。
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

def normalizedTensorConeSimplexAugmentation {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.ComplexLimits.ComplexSimplexAugmentation A (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c) X where
  app := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c
  hom_naturality := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt_compose A X Y c

lemma normalizedTensorConeSimplexAugmentation_app_quasiIso {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (i : Fin (n + 2)) :
    QuasiIso ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplexAugmentation A X Y c).app i) :=
  _root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt_quasiIso A X Y c i

end SerrePositivity.ComplexLimits
