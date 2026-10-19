module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientFiniteRelativePrimitives

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 有限個の指定原始元を、共通実分母辺と両微分式を保って相対持ち上げする。 -/
theorem dgQuotientFinite_exists_actualRelativePrimitives (P : Set D) (hP : localKFlat A D P)
    {m : ℕ} (x : D) (y : Fin m → D) (k : Fin m → ℤ)
    (a : ∀ i, GradedHom A x (y i) (k i + 1)) (ha : ∀ i, differential A (a i) = 0)
    (c : ∀ i, GradedHom A ((inclusion A D P).obj x) ((inclusion A D P).obj (y i)) (k i))
    (hc : ∀ i, differential A (c i) = ((inclusion A D P).map x (y i)).f (k i + 1) (a i)) :
    ∃ (q : D) (s : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex q) (Simplex.vertex x)), s.edge ∈ dgVerdierEdges A D P ∧
      ∀ i, ∃ h : GradedHom A q (y i) (k i),
        differential A h = dgGradedPrecompose A D (k i + 1) (a i) (edgeClosed s) ∧
        ∃ b : GradedHom A ((inclusion A D P).obj q) ((inclusion A D P).obj (y i)) (k i - 1),
          (homObject A (QuotientObject D P) ((inclusion A D P).obj q)
            ((inclusion A D P).obj (y i))).d (k i - 1) (k i) b =
              dgPrimitiveResidual A D (QuotientObject D P) (inclusion A D P)
                (k i) (c i) h (edgeClosed s) := by
  obtain ⟨q, s, hs, hw⟩ := dgQuotientFinite_exists_relativePrimitives A D P hP x y k a ha c hc
  refine ⟨q, dgClosedEdge A D s, hs, fun i => ?_⟩
  obtain ⟨h, hh, b, hb⟩ := hw i
  refine ⟨h, ?_, b, ?_⟩
  · rw [dgClosedEdge_closed]
    exact hh
  · rw [dgClosedEdge_closed]
    exact hb

end SerrePositivity.InfinityCategories
