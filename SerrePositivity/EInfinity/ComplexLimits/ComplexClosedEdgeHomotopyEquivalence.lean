module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorAugmentation
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.StandardCofiberPullback

/-!
# 元の複体射の閉辺の回収と同じホモトピー同値の反転

概要：同じ複体射の閉辺を読み戻し、元の鎖ホモトピー同値の可逆性を移す。
方針：既存の辺の回収・反転定理と同じ実収縮を使う。
規約：元の複体射と augmentation を保つ。
使われ方：普遍正規化 Hom 族の実屋根評価方程式の相殺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomologicalComplex SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma complexToClosed_edgeChainMap {P Q : Complex A} (f : P ⟶ Q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((complexToClosed A).map f)) = f := by
  change complexClosedHomEquiv A P Q
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((complexToClosed A).map f))) = f
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed]
  exact complexToClosed_map A f

lemma complexToClosed_edge_invertible {P Q : Complex A} (f : P ⟶ Q)
    (hf : homotopyEquivalences (ModuleCat A) (.up ℤ) f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((complexToClosed A).map f)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complex_edge_invertible_of_homotopyEquivalence
  rw [complexToClosed_edgeChainMap]
  exact hf

lemma complexToClosed_edge_id (X : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((complexToClosed A).map (𝟙 X)) =
      Truncated.Edge.id (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) := by
  rw [CategoryTheory.Functor.map_id]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_edgeClosed A (Complex A)
    (Truncated.Edge.id (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeClosed_id (A := A) (D := Complex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)
  have hi' : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (Truncated.Edge.id
      (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) =
      𝟙 ((complexToClosed A).obj X) := hi
  exact (congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A)) hi').symm.trans h

lemma normalizedTensorAugmentation_edge_invertible (X : Complex A) (n : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A)
      ((complexToClosed A).map ((normalizedSimplexTensorAugmentation A X).app n))) :=
  complexToClosed_edge_invertible A _
    (normalizedSimplexTensorContraction A X n).homotopyEquivalences_hom

end SerrePositivity.EInfinity.ComplexLimits
