module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientFiniteRelativePrimitives

/-! # 指定された有限個の商の原始元の実分母辺による相対持ち上げ

概要：共通分母を元の dg nerve の実辺として返し、両微分式と比較境界を保つ。
方針：選んだ閉分母の実辺化と、その閉射への厳密な逆変換を使う。
規約：全ての指定原始元を保持する。使われ方：pinched 境界の有限成分の相対充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 有限個の指定原始元を、共通実分母辺と両微分式を保って相対持ち上げする。 -/
theorem dgQuotientFinite_exists_actualRelativePrimitives (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {m : ℕ} (x : D) (y : Fin m → D) (k : Fin m → ℤ)
    (a : ∀ i, _root_.SerrePositivity.DifferentialGraded.GradedHom A x (y i) (k i + 1)) (ha : ∀ i, _root_.SerrePositivity.DifferentialGraded.differential A (a i) = 0)
    (c : ∀ i, _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i)) (k i))
    (hc : ∀ i, _root_.SerrePositivity.DifferentialGraded.differential A (c i) = ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).map x (y i)).f (k i + 1) (a i)) :
    ∃ (q : D) (s : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)), s.edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∀ i, ∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom A q (y i) (k i),
        differential A h = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k i + 1) (a i) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed s) ∧
        ∃ b : _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj q) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i)) (k i - 1),
          (_root_.SerrePositivity.DifferentialGraded.homObject A (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj q)
            ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i))).d (k i - 1) (k i) b =
              _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D (QuotientObject D P) (inclusion A D P)
                (k i) (c i) h (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed s) := by
  obtain ⟨q, s, hs, hw⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFinite_exists_relativePrimitives A D P hP x y k a ha c hc
  refine ⟨q, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s, hs, fun i => ?_⟩
  obtain ⟨h, hh, b, hb⟩ := hw i
  refine ⟨h, ?_, b, ?_⟩
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed]
    exact hh
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed]
    exact hb

end SerrePositivity.InfinityCategories.Project.DerivedCategories
