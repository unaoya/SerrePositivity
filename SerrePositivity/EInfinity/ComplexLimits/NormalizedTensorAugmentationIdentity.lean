module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorAugmentationGammaIdentity
public import SerrePositivity.EInfinity.ComplexLimits.StandardDoldKanPinchedComparison
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorAugmentationSimplex

/-!
# 元の普遍正規化 Hom 族の augmentation 像は元の恒等辺

概要：元の augmentation の零次数像を標準閉恒等辺に同定する。
方針：同じ Γ 零次数像の一致と元の標準/pinched 比較の合成式を使う。
規約：元の比較射・恒等辺・augmentation を保つ。
使われ方：元の普遍族の実屋根評価方程式の恒等射条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma complexIdentityDoldKanVertex_pinched (X : Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomPinchedIso (R := A) (D := Complex A) X X).hom.app (Opposite.op ⦋0⦌)
      (ULift.up (complexIdentityDoldKanVertex A X)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (Complex A) ((complexToClosed A).map (𝟙 X)) := by
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A X X 0 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant
    (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map (𝟙 X))) 0
  have h := congrArg (fun f : SSet.uliftFunctor.{u + 1, u}.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) (D := Complex A) X X) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X X => f.app (Opposite.op ⦋0⦌) (ULift.up s))
    (standardDoldKanPinchedComparison (R := A) (D := Complex A) X X)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomPinchedIso (R := A) (D := Complex A) X X).hom.app (Opposite.op ⦋0⦌)
      (ULift.up (complexIdentityDoldKanVertex A X)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex A (Complex A) ((complexToClosed A).map (𝟙 X)) 0 at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex_zero A (Complex A) _)

lemma normalizedTensorAugmentationVertex_identity (X : Complex A) :
    normalizedTensorAugmentationVertex A X =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (Complex A) ((complexToClosed A).map (𝟙 X)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomPinchedIso (R := A) (D := Complex A) X X).hom.app (Opposite.op ⦋0⦌)
    (ULift.up (normalizedSimplexTensorHomEquiv A X X ⦋0⦌
      ((normalizedSimplexTensorAugmentation A X).app ⦋0⦌))) = _
  rw [normalizedTensorAugmentation_gamma_zero_eq]
  exact complexIdentityDoldKanVertex_pinched A X

lemma normalizedTensorUniversalSimplex_augmentation_identity (X : Complex A)
    (n : SimplexCategory) :
    normalizedTensorUniversalSimplex A X n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap
      (homPostcompose X ((normalizedSimplexTensorAugmentation A X).app n)) =
    SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (Complex A) ((complexToClosed A).map (𝟙 X))) := by
  rw [normalizedTensorUniversalSimplex_augmentation, normalizedTensorAugmentationVertex_identity]

end SerrePositivity.EInfinity.ComplexLimits
