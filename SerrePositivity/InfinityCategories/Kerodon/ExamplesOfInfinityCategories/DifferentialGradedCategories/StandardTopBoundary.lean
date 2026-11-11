module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeBoundary

/-!
# 標準単体の最上位評価と交代境界

概要：標準単体の最上位評価の微分は面の最上位評価の交代和である。
方針：標準方程式の全体集合の成分を取り、余面の像を一点削除した集合に同定する。
規約：Hom の cochain 微分は次数を +1 上げ、単体の次元は一つ下がる。
使われ方：HA 1.3.1.16 の基本鎖の評価を微分する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：標準単体の面の最上位成分は、その頂点を削除した元の成分である。
方針：余面は単射で、全頂点の像は指定頂点を除いた集合となる。
規約：次数は小さい単体の次元の負。
使われ方：Kerodon 2.5.9（Tag 00SC） の面による評価と削除境界の対応。 -/
lemma standardTopEval_face {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y (n + 1)) (j : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback (SimplexCategory.δ j).toOrderHom f) =
      f.val.component (Finset.univ.erase j) (-(n : ℤ))
        (by apply Finset.card_pos.mp; simp) (by simp) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback (SimplexCategory.δ j).toOrderHom f).val.component
    Finset.univ (-(n : ℤ)) Finset.univ_nonempty (by simp) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _
    j.succAboveOrderEmb.injective.injOn]
  have he : (Finset.univ : Finset (Fin (n + 1))).image (SimplexCategory.δ j).toOrderHom =
      Finset.univ.erase j := by
    change Finset.image j.succAbove Finset.univ = _
    simpa only [Finset.compl_eq_univ_sdiff, Finset.sdiff_singleton_eq_erase] using
      Fin.image_succAbove_univ j
  exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.component_heq_of_eq f.val _ _ he _ _ _ _ _ _)

/-- 概要：標準単体の全体集合の微分は全余面の削除成分の交代和である。
方針：標準方程式を全域削除和にし、Fin の前の点数がその値に等しいことを使う。
規約：始次数 p と終次数 q を指定して等式の型を保つ。
使われ方：HA 1.3.1.16 の標準単体の鎖の評価の微分。 -/
lemma standardTop_d_components {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y (n + 1))
    (p q : ℤ) (hp : p = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ))
    (hpq : q = p + 1) :
    (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d p q (f.val.component Finset.univ p Finset.univ_nonempty hp) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        f.val.component (Finset.univ.erase j) q
          (by apply Finset.card_pos.mp; simp) (by simp at hp ⊢; omega) := by
  subst hpq
  have h := f.property Finset.univ p Finset.univ_nonempty hp
  refine h.trans ?_
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs_eq_deleteSum]
  rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ]
  apply Finset.sum_congr rfl
  intro j _
  have he : (Finset.univ : Finset (Fin (n + 2))).filter (· < j) = Finset.Iio j := by
    ext a
    simp
  rw [he, Fin.card_Iio, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_eq _ _ _
    (by apply Finset.card_pos.mp; simp) (by simp at hp ⊢; omega)]

/-- 概要：標準単体の最上位評価は微分を面の最上位評価の交代和に送る。
方針：全体集合の微分の式に、各面の最上位評価の計算を代入する。
規約：次数 −(n+1) から −n への Hom の微分として述べる。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の基本鎖の評価の微分公式。 -/
lemma standardTopEval_d {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y (n + 1)) :
    (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y (n + 1) f) =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y n
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback (SimplexCategory.δ j).toOrderHom f) := by
  refine (standardTop_d_components f _ _ (by simp; omega) (by omega)).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  rw [standardTopEval_face]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
