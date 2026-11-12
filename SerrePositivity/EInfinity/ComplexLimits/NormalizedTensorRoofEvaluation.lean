module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorAugmentationFamily

/-!
# 元の正規化 frame の実屋根評価方程式

概要：元の augmentation の閉辺と普遍 Hom 族が互いに逆であることを証明する。
方針：全族の後合成式、元の恒等頂点との一致、実収縮による可逆性を使う。
規約：任意の複体・全次数・任意のパラメータを保つ。
使われ方：同じ U の導来単位の写像空間比較の幾何的三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

lemma normalizedTensorRoofEvaluation_family (X Y : Complex A) (n : SimplexCategory)
    (g : (normalizedSimplexTensor A X).obj n ⟶ Y) (K : SSet.{u + 1})
    (t : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj (SSet.stdSimplex.obj n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A)
          ((complexToClosed A).map ((normalizedSimplexTensorAugmentation A X).app n)))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A) (t ≫ normalizedTensorHomPinchedSimplex A X Y n g) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((complexToClosed A).map g))) := by
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
    (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A)
      ((complexToClosed A).map ((normalizedSimplexTensorAugmentation A X).app n))))
  let b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A) (t ≫ normalizedTensorUniversalSimplex A X n)
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
    (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((complexToClosed A).map g)))
  have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A)
      (t ≫ normalizedTensorHomPinchedSimplex A X Y n g) = b ≫ c := by
    rw [← normalizedTensorUniversalSimplex_evaluation, ← Category.assoc]
    exact complexPinchedPostcomposition_family A X g K _
  have hi : a ≫ b = 𝟙 _ := normalizedTensorUniversalSimplex_augmentation_inverse A X n K t
  exact (congrArg (fun f => a ≫ f) he).trans
    ((Category.assoc a b c).symm.trans ((congrArg (fun f => f ≫ c) hi).trans
      (Category.id_comp c)))

end SerrePositivity.EInfinity.ComplexLimits
