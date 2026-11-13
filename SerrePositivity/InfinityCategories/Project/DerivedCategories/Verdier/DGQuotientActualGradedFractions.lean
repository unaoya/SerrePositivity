module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientGradedFractions

/-! # 商の全次数の分数表示の実分母辺

概要：商の斉次閉元の分数表示を、元の dg nerve の実辺を分母として公開する。
方針：閉次数零分母を厳密な実辺へ送り、その閉射が元の分母であることを使う。
規約：商の入力元と比較境界を保持する。使われ方：β3 の実写像空間の相対比較。
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

/-- 商の任意次数の斉次閉元に、元の実分母辺・斉次閉分子・実比較境界が存在する。 -/
theorem dgQuotientGraded_exists_actualFraction (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) (n : ℤ)
    (c : _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) n)
    (hc : _root_.SerrePositivity.DifferentialGraded.differential A c = 0) :
    ∃ (q : D) (s : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)), s.edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∃ a : _root_.SerrePositivity.DifferentialGraded.GradedHom A q y n, _root_.SerrePositivity.DifferentialGraded.differential A a = 0 ∧
        ∃ b : _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj q) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) (n - 1),
          (_root_.SerrePositivity.DifferentialGraded.homObject A (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj q)
            ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)).d (n - 1) n b =
              ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).map q y).f n a -
                _root_.SerrePositivity.DifferentialGraded.compose A c (((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).map q x).f 0
                  (closedHomEquiv A D _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed s)).val) (zero_add n) := by
  obtain ⟨q, s, hs, a, ha, b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientGraded_exists_fraction A D P hP x y n c hc
  refine ⟨q, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s, hs, a, ha, b, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed]
  exact hb

end SerrePositivity.InfinityCategories.Project.DerivedCategories
