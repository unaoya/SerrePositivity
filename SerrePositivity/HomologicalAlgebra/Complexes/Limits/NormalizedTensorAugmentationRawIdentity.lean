module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorAugmentationCurryZero
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ExtendedTruncationZeroMono

/-!
# 元の正規化テンソル augmentation の Γ 零次数像の直接値

概要：元の augmentation の実 Γ 零次数像を単射な切断包含で戻すと元の恒等 cochain になる。
方針：実 Hom の零次数直接評価と同じ augmentation の curry を合成する。
規約：元の Γ 同型・包含・augmentation・Hom 同値を保つ。
使われ方：普遍 Hom 族の augmentation 像と恒等辺の同定の元の Hom 複体側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedTensorAugmentation_gamma_zero_raw (X : Complex A) :
    _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
      _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero rfl (homComplex A X X)
      ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso ((homComplex A X X).truncLE'
        (ComplexShape.embeddingUpIntLE 0))).hom
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A X X ⦋0⦌
          ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app ⦋0⦌))) =
    CochainComplex.HomComplex.Cochain.ofHom (𝟙 X) := by
  exact (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_zero_raw A (homComplex A X X)
    (tensorHomEquiv X _ X ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app ⦋0⦌))).trans
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorAugmentation_curry_zero A X)

end SerrePositivity.ComplexLimits
