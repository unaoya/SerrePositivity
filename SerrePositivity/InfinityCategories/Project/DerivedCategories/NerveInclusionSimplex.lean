module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ClosedComposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DGNerveBasic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! # 閉零圏の通常の単体を dg 単体として読む

概要：合成可能な閉零射の列を、高次成分が零である dg nerve の単体へ送る。
方針：三点の方程式は関手の合成保存、それより高い方程式は零成分から従う。
規約：対象と辺を保つ。使われ方：通常の nerve から dg nerve への包含。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded

open scoped BigOperators
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：閉零射を次数零に置き、他の次数では零にする。
方針：次数で場合分けする。
規約：閉零圏の対象包装は外す。使われ方：通常の nerve の斉次成分。 -/
def closedNerveHom {x y : ClosedCategory A D} (f : x ⟶ y) (k : ℤ) :
    GradedHom A (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y) k := by
  by_cases hk : k = 0
  · subst k
    exact (closedHomEquiv A D x y f).val
  · exact 0

/-- 概要：次数零で閉零射の元を復元する。
方針：次数の分岐を評価する。
規約：等式は元の Hom 複体の次数零。使われ方：辺の整合性。 -/
theorem closedNerveHom_zero {x y : ClosedCategory A D} (f : x ⟶ y) :
    closedNerveHom f 0 = (closedHomEquiv A D x y f).val := by
  simp only [closedNerveHom, dite_true]

/-- 概要：零でない次数の閉零射成分は零。
方針：次数の分岐を評価する。
規約：任意の非零整数次数。使われ方：高次成分の消去。 -/
theorem closedNerveHom_of_ne {x y : ClosedCategory A D} (f : x ⟶ y)
    (k : ℤ) (hk : k ≠ 0) : closedNerveHom f k = 0 := by
  simp only [closedNerveHom, dite_eq_right hk]

/-- 概要：次数零の閉零射の合成は dg Hom の合成に一致する。
方針：次数等式を消去し、閉零圏の合成評価を使う。
規約：次数の等式は引数として保持する。使われ方：三点の単体方程式。 -/
theorem closedNerveHom_comp {x y z : ClosedCategory A D} (f : x ⟶ y) (g : y ⟶ z)
    (p q r : ℤ) (hp : p = 0) (hq : q = 0) (hr : r = 0) (h : p + q = r) :
    compose A (closedNerveHom g q) (closedNerveHom f p) h = closedNerveHom (f ≫ g) r := by
  subst hp hq hr
  simp only [closedNerveHom_zero]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp f g).symm

private theorem compose_zero_right {x y z : D} {p q k : ℤ}
    (g : GradedHom A y z q) (hk : p + q = k) : compose A g (0 : GradedHom A x y p) hk = 0 := by
  simp [compose, forward]

private theorem compose_zero_left {x y z : D} {p q k : ℤ}
    (f : GradedHom A x y p) (hk : p + q = k) : compose A (0 : GradedHom A y z q) f hk = 0 := by
  simp [compose, forward]

/-- 概要：閉零圏の合成可能射の列から dg 単体のデータを作る。
方針：両端の間の関手の射を次数零に配置する。
規約：濃度三以上の成分は零。使われ方：単体方程式の検証。 -/
abbrev closedNerveData {n : ℕ} (F : ComposableArrows (ClosedCategory A D) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n where
  obj i := ForgetEnrichment.to (Complex A) (F.obj i)
  hom I a b k hI ha hb hk :=
    closedNerveHom (F.map (homOfLE (by
      rw [ha, hb]
      exact I.min'_le _ (I.max'_mem _)))) k

/-- 概要：通常の nerve から作ったデータの各内部点の寄与は零。
方針：三点では合成保存、高次では削除成分と少なくとも一方の切断成分が零。
規約：dg nerve の標準符号を使う。使われ方：単体方程式の右辺。 -/
theorem closedNerveData_term {n : ℕ} (F : ComposableArrows (ClosedCategory A D) n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) :
    (closedNerveData F).term I a b k hI ha hb hk j hj haj hjb = 0 := by
  have haI : a ∈ I := by rw [ha]; exact I.min'_mem _
  have hbI : b ∈ I := by rw [hb]; exact I.max'_mem _
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two haI hj haj
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbI hjb
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
  have he := Finset.card_erase_add_one hj
  by_cases hc : I.card = 3
  · have hleft : (I.filter (· ≤ j)).card = 2 := by omega
    have hright : (I.filter (j ≤ ·)).card = 2 := by omega
    have hk' : k = -1 := by omega
    subst hk'
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, closedNerveData]
    rw [closedNerveHom_comp _ _ _ _ _ (by omega) (by omega) (by decide)]
    rw [← F.map_comp, homOfLE_comp, sub_self, smul_zero]
  · have he0 : k + 1 ≠ 0 := by omega
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, closedNerveData]
    rw [closedNerveHom_of_ne _ _ he0]
    by_cases hleft : (I.filter (· ≤ j)).card = 2
    · have hr0 : 2 - ((I.filter (j ≤ ·)).card : ℤ) ≠ 0 := by omega
      rw [closedNerveHom_of_ne _ _ hr0, compose_zero_left, sub_self, smul_zero]
    · have hl0 : 2 - ((I.filter (· ≤ j)).card : ℤ) ≠ 0 := by omega
      rw [closedNerveHom_of_ne _ _ hl0, compose_zero_right, sub_self, smul_zero]

/-- 概要：通常の nerve の単体は高次成分零の dg nerve の単体を定める。
方針：左辺は閉性または零、右辺は各内部点の寄与が零であることを使う。
規約：合成可能な閉零射の列に対し構成する。使われ方：nerve 包含の各次数の写像。 -/
def closedNerveSimplex {n : ℕ} (F : ComposableArrows (ClosedCategory A D) n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n where
  toSimplexData := closedNerveData F
  equation I a b k hI ha hb hk := by
    have hrhs : (closedNerveData F).rhs I a b k hI ha hb hk = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hint : a < j.val ∧ j.val < b
      · simp only [dite_eq_left hint, closedNerveData_term]
      · simp only [dite_eq_right hint]
    rw [hrhs]
    change differential A (closedNerveHom _ k) = 0
    by_cases hk0 : k = 0
    · subst hk0
      rw [closedNerveHom_zero]
      exact (closedHomEquiv A D _ _ _).property
    · rw [closedNerveHom_of_ne _ k hk0]
      exact map_zero _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
