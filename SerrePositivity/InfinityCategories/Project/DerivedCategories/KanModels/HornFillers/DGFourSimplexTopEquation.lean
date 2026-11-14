module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TripleHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedEquation

/-! # 四次単体の最上位 rhs の二未知分解

概要：四次単体の右辺を、欠面成分を含まない既知部分と最後辺による後合成に分ける。
方針：三つの内部頂点の削除・左右切断・符号を直接計算する。
規約：dg nerve の rhs の符号を保持する。使われ方：最後外四次ホーンの残差 cone。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 四次単体の最上位 rhs の、欠面成分 Q を含まない既知部分。 -/
def dgFourSimplexTopResidual (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 4) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 0) (s.obj 4) (-2) :=
  -s.hom {0, 2, 3, 4} 0 4 (-2) (by decide) (by decide) (by decide) (by decide) +
    _root_.SerrePositivity.DifferentialGraded.compose A (s.hom {1, 2, 3, 4} 1 4 (-2)
      (by decide) (by decide) (by decide) (by decide)) (s.edgeHom 0 1 (by decide)) (by decide) +
    s.hom {0, 1, 3, 4} 0 4 (-2) (by decide) (by decide) (by decide) (by decide) -
    _root_.SerrePositivity.DifferentialGraded.compose A (s.tripleHom 2 3 4 (by decide) (by decide))
      (s.tripleHom 0 1 2 (by decide) (by decide)) (by decide) -
    s.hom {0, 1, 2, 4} 0 4 (-2) (by decide) (by decide) (by decide) (by decide)

/-- 四次単体の最上位右辺は、既知残差と最後辺による Q の後合成の和。 -/
lemma dgFourSimplex_rhs_top (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 4) :
    s.rhs Finset.univ 0 4 (-3) (by decide) (by decide) (by decide) (by decide) =
      dgFourSimplexTopResidual s + _root_.SerrePositivity.DifferentialGraded.compose A (s.edgeHom 3 4 (by decide))
        (s.hom {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide))
        (by decide) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ]
  have he₁ : (Finset.univ : Finset (Fin 5)).erase 1 = {0, 2, 3, 4} := by decide
  have he₂ : (Finset.univ : Finset (Fin 5)).erase 2 = {0, 1, 3, 4} := by decide
  have he₃ : (Finset.univ : Finset (Fin 5)).erase 3 = {0, 1, 2, 4} := by decide
  have hl₁ : (Finset.univ : Finset (Fin 5)).filter (· ≤ 1) = {0, 1} := by decide
  have hr₁ : (Finset.univ : Finset (Fin 5)).filter (1 ≤ ·) = {1, 2, 3, 4} := by decide
  have hl₂ : (Finset.univ : Finset (Fin 5)).filter (· ≤ 2) = {0, 1, 2} := by decide
  have hr₂ : (Finset.univ : Finset (Fin 5)).filter (2 ≤ ·) = {2, 3, 4} := by decide
  have hl₃ : (Finset.univ : Finset (Fin 5)).filter (· ≤ 3) = {0, 1, 2, 3} := by decide
  have hr₃ : (Finset.univ : Finset (Fin 5)).filter (3 ≤ ·) = {3, 4} := by decide
  have hs₁ : ((Finset.univ : Finset (Fin 5)).filter (1 < ·)).card = 3 := by decide
  have hs₂ : ((Finset.univ : Finset (Fin 5)).filter (2 < ·)).card = 2 := by decide
  have hs₃ : ((Finset.univ : Finset (Fin 5)).filter (3 < ·)).card = 1 := by decide
  norm_num [Fin.sum_univ_succ]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, he₁, he₂, he₃, hl₁, hr₁, hl₂, hr₂, hl₃, hr₃, hs₁, hs₂, hs₃]
  change (-1 : ℤ) • (s.hom {0, 2, 3, 4} 0 4 (-2)
    (by decide) (by decide) (by decide) (by decide) -
    compose A (s.hom {1, 2, 3, 4} 1 4 (-2)
      (by decide) (by decide) (by decide) (by decide)) (s.edgeHom 0 1 (by decide)) (by decide)) +
    ((1 : ℤ) • (s.hom {0, 1, 3, 4} 0 4 (-2)
      (by decide) (by decide) (by decide) (by decide) -
      compose A (s.tripleHom 2 3 4 (by decide) (by decide))
        (s.tripleHom 0 1 2 (by decide) (by decide)) (by decide)) +
    (-1 : ℤ) • (s.hom {0, 1, 2, 4} 0 4 (-2)
      (by decide) (by decide) (by decide) (by decide) -
      compose A (s.edgeHom 3 4 (by decide)) (s.hom {0, 1, 2, 3} 0 3 (-2)
        (by decide) (by decide) (by decide) (by decide)) (by decide))) = _
  unfold dgFourSimplexTopResidual
  simp only [neg_smul, one_smul]
  abel

end SerrePositivity.InfinityCategories.Project.DerivedCategories
