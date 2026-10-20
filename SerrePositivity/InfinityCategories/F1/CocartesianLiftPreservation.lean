module

public import SerrePositivity.InfinityCategories.F1.CocartesianComparisonTriangle

/-!
概要：選んだ cocartesian lift の保存から、全ての cocartesian 辺の保存を導く。
方針：同じ底と始点の比較三角形の可逆辺を写し、cocartesian 辺の合成閉性を使う。
規約：比較は元の単体集合の射そのものであり、ホモトピー圏の射への置き換えをしない。
使われ方：weighted nerve の標準水平 lift による関手性と、scaffold の写像空間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 各辺と同じ始点・底を持つ cocartesian lift を保つなら、全 cocartesian 辺を保つ。 -/
lemma preservesCocartesianEdges_of_matching_lifts {E D B : SSet.{u}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p] [InnerFibration q]
    (f : E ⟶ D)
    (hl : ∀ e : E _⦋1⦌, ∃ h : E _⦋1⦌,
      E.δ 1 h = E.δ 1 e ∧ p.app (Opposite.op ⦋1⦌) h = p.app _ e ∧
      IsCocartesianEdge p h ∧ IsCocartesianEdge q (f.app (Opposite.op ⦋1⦌) h)) :
    PreservesCocartesianEdges p q f := by
  intro e he
  obtain ⟨h, hs, hp, hh, hfh⟩ := hl e
  obtain ⟨t, ht₂, ht₁, hi⟩ := exists_cocartesianComparisonTriangle p e h he hh hs hp
  have hfirst : IsCocartesianEdge q
      (SSet.yonedaEquiv (stdSimplex.δ 2 ≫ (t ≫ f))) := by
    rw [← Category.assoc, ht₂, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hfh
  have hsecond : IsCocartesianEdge q
      (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ (t ≫ f))) := by
    rw [← Category.assoc, SSet.yonedaEquiv_comp]
    exact isCocartesianEdge_of_isInvertibleEdge q
      ((edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ t))).map ((truncation 2).map f))
      (hi.map f)
  have hlong := isCocartesianEdge_triangle_longEdge (t ≫ f) q hfirst hsecond
  rw [← Category.assoc, ht₁, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hlong
  exact hlong

end SerrePositivity.InfinityCategories
