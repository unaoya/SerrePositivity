module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSumLinear
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedTermLinear

/-! # 右 pinched 方程式の右辺の和

概要：元の単体方程式の右辺を先頭集合に添字付けた項の和に直す。
方針：最終点の項を消し、対象の移送を保持して各項の線形表示を足し合わせる。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：回収した族の線形方程式。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：対象を等式で移送した有限族の和は異種等号で一致する。
方針：対象の等式を消し、各項の比較を有限和の外延性に適用する。
規約：HA Construction 1.3.1.6。使われ方：線形化した各項の和の比較。 -/
lemma sum_heq_of_obj_eq {ι : Type*} [Fintype ι] {a b c d : D} (ha : a = c) (hb : b = d)
    {k : ℤ} (f : ι → GradedHom A a b k) (g : ι → GradedHom A c d k)
    (h : ∀ i, HEq (f i) (g i)) : HEq (∑ i, f i) (∑ i, g i) := by
  subst c
  subst d
  apply heq_of_eq
  apply Finset.sum_congr rfl
  intro i _
  exact eq_of_heq (h i)

/-- 概要：対象を等式で移送した射の微分は異種等号で一致する。
方針：対象の等式と元の成分の異種等号を消去する。
規約：HA Construction 1.3.1.6。使われ方：回収した族の微分方程式の左辺。 -/
lemma differential_heq_of_obj_eq {a b c d : D} (ha : a = c) (hb : b = d) {k : ℤ}
    (f : GradedHom A a b k) (g : GradedHom A c d k) (h : HEq f g) :
    HEq (differential A f) (differential A g) := by
  subst c
  subst d
  have he := eq_of_heq h
  rw [he]

namespace PinchedHom

/-- 概要：最終点を含む集合の右辺は、先頭集合の最小点以外の項の和。
方針：追加した最終点の項が零となることを使い、先頭埋め込みで和を移す。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：右辺全体の線形化の添字。 -/
lemma rhs_withLast {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1))
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    s.rhs (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega) =
      ∑ j : J, if h : J.min' hJ < j.val then
        s.term (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega) j.val.castSucc
          (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, j.property, rfl⟩))
          (Fin.castSucc_lt_castSucc_iff.mpr h) (Fin.castSucc_lt_last _) else 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sum_withLast]
  simp only [lt_self_iff_false, and_false, dite_false, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : J.min' hJ < j.val
  · simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, and_true, dite_eq_left hj]
  · simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, and_true, dite_eq_right hj]

open scoped _root_.Simplicial

variable {x y : D}

/-- 概要：元の右辺は全ての先頭内部点の線形表示の和と異種等号で一致する。
方針：先頭集合への和の引き戻しと各項の線形表示を対象の移送に沿って足す。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：最小点の削除項を復元する直前の式。 -/
lemma rhs_heq_linear_terms {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    HEq (s.val.toSimplexData.rhs (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)).castSucc
      (Fin.last (n + 1)) k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega))
      (∑ j : J, if J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) < j.val then
        (((J.filter (j.val < ·)).card : ℤ) + 1).negOnePow •
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component (J.erase j.val) (k + 1)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ j.val j.property)
            (by have := Finset.card_erase_add_one j.property; omega) -
          if j.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ then
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component (J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))) (k + 1)
              (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ _ (J.min'_mem _))
              (by have := Finset.card_erase_add_one (J.min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)); omega)
          else 0)
        else 0) := by
  rw [rhs_withLast s.val.toSimplexData J (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) k hk]
  apply sum_heq_of_obj_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj s _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s)
  intro j
  by_cases hj : J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) < j.val
  · simp only [dite_eq_left hj, ite_eq_left hj]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.term_heq_linear s J hJ k hk j.val j.property hj
  · simp only [dite_eq_right hj, ite_eq_right hj]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj s _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s]

/-- 概要：元の右辺は回収した族の全線形削除和と異種等号で一致する。
方針：各内部点の線形表示を足し、二番目の補正を最小点の削除項に戻す。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形方程式の右辺。 -/
lemma rhs_heq_linear {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    HEq (s.val.toSimplexData.rhs (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)).castSucc
      (Fin.last (n + 1)) k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).rhs J k hk) := by
  refine (rhs_heq_linear_terms s J hJ k hk).trans (heq_of_eq ?_)
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs
  rw [dite_eq_left hJ]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sum_linear_terms J hJ (fun j => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component (J.erase j.val) (k + 1)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ j.val j.property)
    (by have := Finset.card_erase_add_one j.property; omega))

/-- 概要：実際の右 pinched 単体から回収した全成分は線形削除方程式を満たす。
方針：対象移送に沿う微分の比較、元の単体方程式、線形右辺の同定を合成する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。一点集合は元の辺の閉性を使う。
使われ方：全次数の線形表示への順写像。 -/
lemma toLinearData_equation {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    differential A ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).rhs J k hk := by
  have hdeg : k = 2 - ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).card : ℤ) := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega
  have hdiff := differential_heq_of_obj_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj s (J.min' hJ)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s).symm
    _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_component_heq s J k hJ hk)
  have he := s.val.equation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _) hdeg
  have hleft := hdiff.trans (heq_of_eq he)
  apply eq_of_heq
  refine hleft.trans ?_
  by_cases hJ2 : 2 ≤ J.card
  · exact rhs_heq_linear s J hJ2 k hk
  · have hc : J.card = 1 := by have := Finset.card_pos.mpr hJ; omega
    have hcone : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).card = 2 := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast, hc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_of_card_two _ _ _ _ _ _ _ _ _ hcone]
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs
    rw [dite_eq_right hJ2]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj s _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s]

/-- 概要：右 pinched 単体の全成分の回収は線形単体を与える。
方針：回収する成分族に全ての線形方程式の証明を添える。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：全次数の線形模型への順写像。 -/
def toLinearSimplex {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s, toLinearData_equation s⟩

end PinchedHom

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
