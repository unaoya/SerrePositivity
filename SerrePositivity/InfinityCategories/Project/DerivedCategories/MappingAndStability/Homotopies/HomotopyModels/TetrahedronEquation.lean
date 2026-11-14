module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.TriangleExt

/-! # dg nerve の三単体の最上位方程式

概要：四頂点の方程式を四つの三角形成分と二つの辺の式へ展開する。
方針：内部点 1・2 の切断寄与を有限集合で計算する。
規約：HA Construction 1.3.1.6 の符号を保持する。使われ方：D7 の後合成比較の欠けた面。
-/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded

set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 三単体の右辺は二つの内部点の削除項と切断合成からなる。 -/
lemma dgSimplexData_rhs_tetrahedron (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D 3) :
    s.rhs Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide) =
      (s.tripleHom 0 2 3 (by decide) (by decide) -
        compose R (s.tripleHom 1 2 3 (by decide) (by decide)) (s.edgeHom 0 1 (by decide))
          (zero_add (-1))) -
      (s.tripleHom 0 1 3 (by decide) (by decide) -
        compose R (s.edgeHom 2 3 (by decide)) (s.tripleHom 0 1 2 (by decide) (by decide))
          (add_zero (-1))) := by
  have he1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} := by decide
  have he2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} := by decide
  have hl1 : (Finset.univ : Finset (Fin 4)).filter (· ≤ 1) = {0, 1} := by decide
  have hr1 : (Finset.univ : Finset (Fin 4)).filter (1 ≤ ·) = {1, 2, 3} := by decide
  have hl2 : (Finset.univ : Finset (Fin 4)).filter (· ≤ 2) = {0, 1, 2} := by decide
  have hr2 : (Finset.univ : Finset (Fin 4)).filter (2 ≤ ·) = {2, 3} := by decide
  have hs1 : ((Finset.univ : Finset (Fin 4)).filter (1 < ·)).card = 2 := by decide
  have hs2 : ((Finset.univ : Finset (Fin 4)).filter (2 < ·)).card = 1 := by decide
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ]
  norm_num [Fin.sum_univ_succ]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom,
    he1, he2, hl1, hr1, hl2, hr2, hs1, hs2]
  norm_num [Int.negOnePow_even 2 ⟨1, rfl⟩]
  change (s.tripleHom 0 2 3 (by decide) (by decide) -
      compose R (s.tripleHom 1 2 3 (by decide) (by decide)) (s.edgeHom 0 1 (by decide))
        (zero_add (-1))) +
    (compose R (s.edgeHom 2 3 (by decide)) (s.tripleHom 0 1 2 (by decide) (by decide))
        (add_zero (-1)) - s.tripleHom 0 1 3 (by decide) (by decide)) =
    (s.tripleHom 0 2 3 (by decide) (by decide) -
      compose R (s.tripleHom 1 2 3 (by decide) (by decide)) (s.edgeHom 0 1 (by decide))
        (zero_add (-1))) -
    (s.tripleHom 0 1 3 (by decide) (by decide) -
      compose R (s.edgeHom 2 3 (by decide)) (s.tripleHom 0 1 2 (by decide) (by decide))
        (add_zero (-1)))
  abel

end SerrePositivity.InfinityCategories.Project.DerivedCategories
