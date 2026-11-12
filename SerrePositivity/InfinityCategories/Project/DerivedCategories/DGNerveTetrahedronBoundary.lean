module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TripleHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra
/-!
概要：実四頂点単体の最高成分と、削除二項・切断合成二項からなる同じ HA 境界を照合する。
方針：内部点1・2の有限和を計算し、元の実単体の方程式を適用する。
規約：通常順合成と降順の向きの符号を保持する。使われ方：tensor 候補の三次元較正。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 実四頂点データの最高次数 −2 の同じ Hom 成分。 -/
def dgNerveTetrahedronHom (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D 3) : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj 0) (s.obj 3) (-2) :=
  s.hom Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide)
/-- 四頂点の実 HA 右辺は同じ二つの削除成分と二つの切断合成からなる。 -/
lemma dgNerveTetrahedron_rhs (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D 3) :
    s.rhs Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide) =
      s.tripleHom 0 2 3 (by decide) (by decide) - s.tripleHom 0 1 3 (by decide) (by decide) -
      _root_.SerrePositivity.DifferentialGraded.compose R (n := -1) (s.tripleHom 1 2 3 (by decide) (by decide))
        (s.edgeHom 0 1 (by decide)) (by decide) +
      _root_.SerrePositivity.DifferentialGraded.compose R (n := -1) (s.edgeHom 2 3 (by decide))
        (s.tripleHom 0 1 2 (by decide) (by decide)) (by decide) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ]
  have he1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} := by decide
  have he2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} := by decide
  have hl1 : (Finset.univ : Finset (Fin 4)).filter (· ≤ 1) = {0, 1} := by decide
  have hr1 : (Finset.univ : Finset (Fin 4)).filter (1 ≤ ·) = {1, 2, 3} := by decide
  have hl2 : (Finset.univ : Finset (Fin 4)).filter (· ≤ 2) = {0, 1, 2} := by decide
  have hr2 : (Finset.univ : Finset (Fin 4)).filter (2 ≤ ·) = {2, 3} := by decide
  have hs1 : ((Finset.univ : Finset (Fin 4)).filter (1 < ·)).card = 2 := by decide
  have hs2 : ((Finset.univ : Finset (Fin 4)).filter (2 < ·)).card = 1 := by decide
  norm_num [Fin.sum_univ_succ]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom,
    he1, he2, hl1, hr1, hl2, hr2, hs1, hs2]
  norm_num
  rw [Int.negOnePow_even 2 ⟨1, rfl⟩, one_smul]
  change (s.tripleHom 0 2 3 (by decide) (by decide) -
      compose R (n := -1) (s.tripleHom 1 2 3 (by decide) (by decide))
        (s.edgeHom 0 1 (by decide)) (by decide)) +
      (compose R (n := -1) (s.edgeHom 2 3 (by decide))
        (s.tripleHom 0 1 2 (by decide) (by decide)) (by decide) -
        s.tripleHom 0 1 3 (by decide) (by decide)) =
      s.tripleHom 0 2 3 (by decide) (by decide) - s.tripleHom 0 1 3 (by decide) (by decide) -
      compose R (n := -1) (s.tripleHom 1 2 3 (by decide) (by decide))
        (s.edgeHom 0 1 (by decide)) (by decide) +
      compose R (n := -1) (s.edgeHom 2 3 (by decide))
        (s.tripleHom 0 1 2 (by decide) (by decide)) (by decide)
  abel
/-- 実三単体の最高成分の微分を、同じ面と辺の四項で表す。 -/
lemma dgNerveTetrahedronHom_differential (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 3) :
    _root_.SerrePositivity.DifferentialGraded.differential R (dgNerveTetrahedronHom R D s.toSimplexData) =
      s.toSimplexData.tripleHom 0 2 3 (by decide) (by decide) -
      s.toSimplexData.tripleHom 0 1 3 (by decide) (by decide) -
      _root_.SerrePositivity.DifferentialGraded.compose R (n := -1) (s.toSimplexData.tripleHom 1 2 3 (by decide) (by decide))
        (s.edgeHom 0 1 (by decide)) (by decide) +
      _root_.SerrePositivity.DifferentialGraded.compose R (n := -1) (s.edgeHom 2 3 (by decide))
        (s.toSimplexData.tripleHom 0 1 2 (by decide) (by decide)) (by decide) := by
  rw [dgNerveTetrahedronHom, s.equation, dgNerveTetrahedron_rhs]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
