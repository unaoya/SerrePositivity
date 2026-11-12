module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ComparisonTriangle

/-!
概要：選んだ cocartesian lift の保存から、全ての cocartesian 辺の保存を導く。
方針：同じ底と始点の比較三角形の可逆辺を写し、cocartesian 辺の合成閉性を使う。
規約：比較は元の単体集合の射そのものであり、ホモトピー圏の射への置き換えをしない。
使われ方：weighted nerve の標準水平 lift による関手性と、scaffold の写像空間比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 各辺と同じ始点・底を持つ cocartesian lift を保つなら、全 cocartesian 辺を保つ。 -/
lemma preservesCocartesianEdges_of_matching_lifts {E D B : SSet.{u}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p] [InnerFibration q]
    (f : E ⟶ D)
    (hl : ∀ e : E _⦋1⦌, ∃ h : E _⦋1⦌,
      E.δ 1 h = E.δ 1 e ∧ p.app (Opposite.op ⦋1⦌) h = p.app _ e ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p h ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (f.app (Opposite.op ⦋1⦌) h)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges p q f := by
  intro e he
  obtain ⟨h, hs, hp, hh, hfh⟩ := hl e
  obtain ⟨t, ht₂, ht₁, hi⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_cocartesianComparisonTriangle p e h he hh hs hp
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q
      (SSet.yonedaEquiv (stdSimplex.δ 2 ≫ (t ≫ f))) := by
    rw [← Category.assoc, ht₂, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hfh
  have hsecond : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q
      (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ (t ≫ f))) := by
    rw [← Category.assoc, SSet.yonedaEquiv_comp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_isInvertibleEdge q
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ t))).map ((truncation 2).map f))
      (hi.map f)
  have hlong := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_triangle_longEdge (t ≫ f) q hfirst hsecond
  rw [← Category.assoc, ht₁, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hlong
  exact hlong

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
