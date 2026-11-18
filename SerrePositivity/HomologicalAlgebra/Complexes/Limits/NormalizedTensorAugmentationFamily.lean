module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorAugmentationIdentity
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ComplexPinchedPostcomposition
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ComplexClosedEdgeHomotopyEquivalence

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

lemma normalizedTensorUniversalSimplex_augmentation_family (X : Complex A)
    (n : SimplexCategory) (K : SSet.{u + 1})
    (t : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj (SSet.stdSimplex.obj n)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A) (t ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex A X n) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A)
          ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app n)))) =
    𝟙 _ := by
  rw [← _root_.SerrePositivity.ComplexLimits.complexPinchedPostcomposition_family, Category.assoc,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex_augmentation_identity, SSet.comp_const]
  have h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A) (SSet.const (X := K)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (Complex A) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X)))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X)))) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilyHom_const_vertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) _
  rw [h, _root_.SerrePositivity.ComplexLimits.complexToClosed_edge_id]
  have hi := Truncated.HomotopyCategory.homMk_id
    (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)
  exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K) hi).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_id (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) K (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))

lemma normalizedTensorUniversalSimplex_augmentation_inverse (X : Complex A)
    (n : SimplexCategory) (K : SSet.{u + 1})
    (t : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj (SSet.stdSimplex.obj n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A)
          ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app n)))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A) (t ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex A X n) =
    𝟙 _ := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A)
      ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app n))) :=
    _root_.SerrePositivity.ComplexLimits.normalizedTensorAugmentation_edge_invertible A X n
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A)
        ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app n))))) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap]
    infer_instance
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
    (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A)
      ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app n))))
  let b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A) (t ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex A X n)
  have h : b ≫ a = 𝟙 _ := _root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex_augmentation_family A X n K t
  change a ≫ b = 𝟙 _
  apply (cancel_mono a).1
  calc
    (a ≫ b) ≫ a = a ≫ (b ≫ a) := Category.assoc _ _ _
    _ = a ≫ 𝟙 _ := congrArg (fun f => a ≫ f) h
    _ = 𝟙 _ ≫ a := by simp

end SerrePositivity.ComplexLimits
