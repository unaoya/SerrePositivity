module

public import SerrePositivity.KST.Spectra.CompositionTriangleSquare

/-!
概要：実三角形から構成した正方形全体の射影を、元の三角形単体の射影へ照合する。
方針：正方形の pushout の二つの三角形で、元の単体と退化単体の自然性を検査する。
規約：同じ二単体と正方形を保持。使われ方：指定境界を保つ区間の構造ホモトピー。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 元の三角形を写してから正方形へ展開しても、元の正方形全体の射影と同じ。 -/
lemma compositionTriangleSquare_map {E B : SSet.{u}} (p : E ⟶ B)
    {x y z : E _⦋0⦌} {a : E.Edge x y} {b : E.Edge y z} {c : E.Edge x z}
    (t : SSet.Edge.CompStruct a b c) :
    compositionTriangleSquare t ≫ p = compositionTriangleSquare (t.map p) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.hom_ext
  · rw [← Category.assoc, compositionTriangleSquare_upper, compositionTriangleSquare_upper]
    exact SSet.yonedaEquiv_symm_comp t.simplex p
  · rw [← Category.assoc, compositionTriangleSquare_lower, compositionTriangleSquare_lower]
    rw [SSet.yonedaEquiv_symm_comp]
    apply congrArg SSet.yonedaEquiv.symm
    simp only [SSet.Edge.CompStruct.compId_simplex, SSet.Edge.map_edge]
    exact SSet.σ_naturality_apply p (1 : Fin 2) c.edge

/-- 射影先の三角形の単体を指定すれば、正方形全体の厳密射影が指定される。 -/
lemma compositionTriangleSquare_post_eq {E B : SSet.{u}} (p : E ⟶ B)
    {x y z : E _⦋0⦌} {a : E.Edge x y} {b : E.Edge y z} {c : E.Edge x z}
    (t : SSet.Edge.CompStruct a b c) {u v w : B _⦋0⦌}
    {a' : B.Edge u v} {b' : B.Edge v w} {c' : B.Edge u w}
    (s : SSet.Edge.CompStruct a' b' c')
    (ht : SSet.yonedaEquiv.symm t.simplex ≫ p = SSet.yonedaEquiv.symm s.simplex) :
    compositionTriangleSquare t ≫ p = compositionTriangleSquare s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.hom_ext
  · rw [← Category.assoc, compositionTriangleSquare_upper, compositionTriangleSquare_upper]
    exact ht
  · rw [← Category.assoc, compositionTriangleSquare_lower, compositionTriangleSquare_lower]
    have hc := congrArg (stdSimplex.δ (1 : Fin 3) ≫ ·) ht
    rw [← Category.assoc, SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm,
      SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm] at hc
    have he : p.app _ c.edge = c'.edge := by
      apply SSet.yonedaEquiv.symm.injective
      rw [← SSet.yonedaEquiv_symm_comp]
      exact hc
    rw [SSet.yonedaEquiv_symm_comp]
    apply congrArg SSet.yonedaEquiv.symm
    rw [SSet.Edge.CompStruct.compId_simplex, SSet.Edge.CompStruct.compId_simplex,
      SSet.σ_naturality_apply, he]

/-- 三角形全体の射影が定数なら、展開した正方形全体も同じ定数へ厳密に射影される。 -/
lemma compositionTriangleSquare_post_const {E B : SSet.{u}} (p : E ⟶ B)
    {x y z : E _⦋0⦌} {a : E.Edge x y} {b : E.Edge y z} {c : E.Edge x z}
    (t : SSet.Edge.CompStruct a b c) (v : B _⦋0⦌)
    (ht : SSet.yonedaEquiv.symm t.simplex ≫ p = SSet.const v) :
    compositionTriangleSquare t ≫ p = SSet.const v := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.hom_ext
  · rw [← Category.assoc, compositionTriangleSquare_upper, SSet.comp_const]
    exact ht
  · rw [← Category.assoc, compositionTriangleSquare_lower, SSet.comp_const]
    have hc := congrArg (stdSimplex.δ (1 : Fin 3) ≫ ·) ht
    rw [← Category.assoc, SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm,
      SSet.comp_const] at hc
    rw [SSet.Edge.CompStruct.compId_simplex, ← stdSimplex.σ_comp_yonedaEquiv_symm,
      Category.assoc, hc, SSet.comp_const]

end SerrePositivity.KST.Spectra
