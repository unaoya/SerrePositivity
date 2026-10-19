module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientGradedFractions

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 商の任意次数の斉次閉元に、元の実分母辺・斉次閉分子・実比較境界が存在する。 -/
theorem dgQuotientGraded_exists_actualFraction (P : Set D) (hP : localKFlat A D P)
    (x y : D) (n : ℤ)
    (c : GradedHom A ((inclusion A D P).obj x) ((inclusion A D P).obj y) n)
    (hc : differential A c = 0) :
    ∃ (q : D) (s : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex q) (Simplex.vertex x)), s.edge ∈ dgVerdierEdges A D P ∧
      ∃ a : GradedHom A q y n, differential A a = 0 ∧
        ∃ b : GradedHom A ((inclusion A D P).obj q) ((inclusion A D P).obj y) (n - 1),
          (homObject A (QuotientObject D P) ((inclusion A D P).obj q)
            ((inclusion A D P).obj y)).d (n - 1) n b =
              ((inclusion A D P).map q y).f n a -
                compose A c (((inclusion A D P).map q x).f 0
                  (closedHomEquiv A D _ _ (edgeClosed s)).val) (zero_add n) := by
  obtain ⟨q, s, hs, a, ha, b, hb⟩ := dgQuotientGraded_exists_fraction A D P hP x y n c hc
  refine ⟨q, dgClosedEdge A D s, hs, a, ha, b, ?_⟩
  rw [dgClosedEdge_closed]
  exact hb

end SerrePositivity.InfinityCategories
