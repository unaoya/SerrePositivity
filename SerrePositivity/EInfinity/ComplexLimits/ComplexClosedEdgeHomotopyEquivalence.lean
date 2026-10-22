module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorAugmentation
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource
public import SerrePositivity.InfinityCategories.Derived.StandardCofiberPullback

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
open DGNerve DGNerve.HomotopyComparison
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma complexToClosed_edgeChainMap {P Q : Complex A} (f : P ⟶ Q) :
    edgeChainMap (dgClosedEdge A (Complex A) ((complexToClosed A).map f)) = f := by
  change complexClosedHomEquiv A P Q
    (edgeClosed (dgClosedEdge A (Complex A) ((complexToClosed A).map f))) = f
  rw [dgClosedEdge_closed]
  exact complexToClosed_map A f

lemma complexToClosed_edge_invertible {P Q : Complex A} (f : P ⟶ Q)
    (hf : homotopyEquivalences (ModuleCat A) (.up ℤ) f) :
    IsInvertibleEdge (X := dgNerve A (Complex A))
      (dgClosedEdge A (Complex A) ((complexToClosed A).map f)) := by
  apply complex_edge_invertible_of_homotopyEquivalence
  rw [complexToClosed_edgeChainMap]
  exact hf

lemma complexToClosed_edge_id (X : Complex A) :
    dgClosedEdge A (Complex A) ((complexToClosed A).map (𝟙 X)) =
      Truncated.Edge.id (X := (truncation 2).obj (dgNerve A (Complex A))) (Simplex.vertex X) := by
  rw [CategoryTheory.Functor.map_id]
  have h := dgClosedEdge_edgeClosed A (Complex A)
    (Truncated.Edge.id (X := (truncation 2).obj (dgNerve A (Complex A)))
      (Simplex.vertex X))
  have hi := edgeClosed_id (A := A) (D := Complex A) (Simplex.vertex X)
  have hi' : edgeClosed (Truncated.Edge.id
      (X := (truncation 2).obj (dgNerve A (Complex A))) (Simplex.vertex X)) =
      𝟙 ((complexToClosed A).obj X) := hi
  exact (congrArg (dgClosedEdge A (Complex A)) hi').symm.trans h

lemma normalizedTensorAugmentation_edge_invertible (X : Complex A) (n : SimplexCategory) :
    IsInvertibleEdge (X := dgNerve A (Complex A)) (dgClosedEdge A (Complex A)
      ((complexToClosed A).map ((normalizedSimplexTensorAugmentation A X).app n))) :=
  complexToClosed_edge_invertible A _
    (normalizedSimplexTensorContraction A X n).homotopyEquivalences_hom

end SerrePositivity.EInfinity.ComplexLimits
