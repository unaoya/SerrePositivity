module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TripleHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedEquation

/-! # 最後外三次ホーンの二未知成分の微分式

概要：欠けた三角形と最上位四面体の右辺を、次数を明示した二つの式へ展開する。
方針：有限集合の削除と切断を計算し、dg nerve の規約の符号をそのまま保持する。
規約：dQ = f12 f01 − f02、dA = h023 − h123 f01 − h013 + f23 Q。
使われ方：実分母図式の始錐の一次整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 欠けた三角形の微分方程式の右辺。 -/
def dgTetrahedronMissingResidual (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 3) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 0) (s.obj 2) 0 :=
  _root_.SerrePositivity.DifferentialGraded.compose A (s.edgeHom 1 2 (by decide)) (s.edgeHom 0 1 (by decide)) (by decide) -
    s.edgeHom 0 2 (by decide)

/-- 最上位の式の、未知 Q を含まない既知部分。 -/
def dgTetrahedronTopResidual (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 3) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 0) (s.obj 3) (-1) :=
  s.tripleHom 0 2 3 (by decide) (by decide) -
    _root_.SerrePositivity.DifferentialGraded.compose A (s.tripleHom 1 2 3 (by decide) (by decide))
      (s.edgeHom 0 1 (by decide)) (by decide) -
    s.tripleHom 0 1 3 (by decide) (by decide)

/-- 欠けた面の右辺は二辺の合成と第三辺の差。 -/
lemma dgTetrahedron_rhs_missing (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 3) :
    s.rhs {0, 1, 2} 0 2 (-1) (by decide) (by decide) (by decide) (by decide) =
      dgTetrahedronMissingResidual s := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [Finset.sum_eq_single (⟨1, by decide⟩ : ({0, 1, 2} : Finset (Fin 4)))]
  · have he : ({0, 1, 2} : Finset (Fin 4)).erase 1 = {0, 2} := by decide
    have hl : ({0, 1, 2} : Finset (Fin 4)).filter (· ≤ 1) = {0, 1} := by decide
    have hr : ({0, 1, 2} : Finset (Fin 4)).filter (1 ≤ ·) = {1, 2} := by decide
    have hs : (({0, 1, 2} : Finset (Fin 4)).filter (1 < ·)).card = 1 := by decide
    simp only [dite_eq_left (show (0 : Fin 4) < 1 ∧ (1 : Fin 4) < 2 from by decide),
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, he, hl, hr, hs]
    change (-1 : ℤ) • (s.edgeHom 0 2 (by decide) -
      compose A (s.edgeHom 1 2 (by decide)) (s.edgeHom 0 1 (by decide)) (by decide)) = _
    simp only [neg_smul, one_smul, neg_sub]
    rfl
  · intro j _ hj
    have hn : ¬ ((0 : Fin 4) < j.val ∧ j.val < 2) := by
      intro hh
      apply hj
      apply Subtype.ext
      apply Fin.ext
      have h₀ : 0 < j.val.val := hh.1
      have h₂ : j.val.val < 2 := hh.2
      change j.val.val = 1
      omega
    exact dite_eq_right hn
  · intro hj
    exact False.elim (hj (Finset.mem_univ _))

/-- 四面体の右辺は、既知三面の寄与と最後の閉辺による Q の後合成。 -/
lemma dgTetrahedron_rhs_top (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 3) :
    s.rhs Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide) =
      dgTetrahedronTopResidual s +
        _root_.SerrePositivity.DifferentialGraded.compose A (s.edgeHom 2 3 (by decide)) (s.tripleHom 0 1 2 (by decide) (by decide))
          (by decide) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ]
  have he₁ : (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} := by decide
  have he₂ : (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} := by decide
  have hl₁ : (Finset.univ : Finset (Fin 4)).filter (· ≤ 1) = {0, 1} := by decide
  have hr₁ : (Finset.univ : Finset (Fin 4)).filter (1 ≤ ·) = {1, 2, 3} := by decide
  have hl₂ : (Finset.univ : Finset (Fin 4)).filter (· ≤ 2) = {0, 1, 2} := by decide
  have hr₂ : (Finset.univ : Finset (Fin 4)).filter (2 ≤ ·) = {2, 3} := by decide
  have hs₁ : ((Finset.univ : Finset (Fin 4)).filter (1 < ·)).card = 2 := by decide
  have hs₂ : ((Finset.univ : Finset (Fin 4)).filter (2 < ·)).card = 1 := by decide
  norm_num [Fin.sum_univ_succ]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, he₁, he₂, hl₁, hr₁, hl₂, hr₂, hs₁, hs₂]
  change (1 : ℤ) • (s.tripleHom 0 2 3 (by decide) (by decide) -
    compose A (s.tripleHom 1 2 3 (by decide) (by decide))
      (s.edgeHom 0 1 (by decide)) (by decide)) +
    (-1 : ℤ) • (s.tripleHom 0 1 3 (by decide) (by decide) -
      compose A (s.edgeHom 2 3 (by decide))
        (s.tripleHom 0 1 2 (by decide) (by decide)) (by decide)) = _
  unfold dgTetrahedronTopResidual
  simp only [neg_smul, one_smul]
  abel

end SerrePositivity.InfinityCategories.Project.DerivedCategories
