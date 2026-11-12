module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWDoubleSum

/-!
# AW の三重合成の切断項の結合則

概要：二つの切断点を固定した三重斉次合成は括弧付けによらない。
方針：反復切断の集合を同定し、dg 合成の結合則を成分に適用する。
規約：二つの切断点は等しくてもよい。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の AW 結合律の各項。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 概要：通常順の斉次合成は各次数の異種等号を保つ。
方針：次数の等式と異種等号を消去して通常の等号に帰着する。
規約：終次数は両辺で同じとする。
使われ方：Kerodon 2.5.8（Tag 00S0） の反復切断の成分の同定。 -/
lemma compose_eq_of_heq {x y z : D} {p p' q q' k : ℤ}
    (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z q) (g' : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z q')
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y p) (f' : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y p')
    (hg : HEq g g') (hf : HEq f f') (hp : p = p') (hq : q = q')
    (hk : p + q = k) (hk' : p' + q' = k) : _root_.SerrePositivity.DifferentialGraded.compose R g f hk = compose R g' f' hk' := by
  subst p' q'
  cases hg
  cases hf
  rfl

/-- 概要：中間の和次数を別名にした通常順の合成も結合則を満たす。
方針：中間次数の等式を消去して dg 圏の結合則を使う。
規約：合成の順序は前の射から f、g、h とする。
使われ方：HA 1.3.1.13 の三つの切断成分の結合則。 -/
lemma compose_assoc_of_sum {w x y z : D} {p q r a b k : ℤ}
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R w x p) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y q) (h : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z r)
    (ha : p + q = a) (hb : q + r = b) (hk : a + r = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R h (_root_.SerrePositivity.DifferentialGraded.compose R g f ha) hk = _root_.SerrePositivity.DifferentialGraded.compose R (_root_.SerrePositivity.DifferentialGraded.compose R h g hb) f (by omega) := by
  subst a b
  exact _root_.SerrePositivity.DifferentialGraded.compose_assoc R f g h hk

/-- 概要：異なる集合表示の三つの成分にも通常順の結合則が成立する。
方針：各成分の次数と異種等号を消去し、中間次数を指定した結合則を使う。
規約：終次数は両辺で同じとする。
使われ方：Kerodon 2.5.8（Tag 00S0） の二つの反復切断の合成項の比較。 -/
lemma compose_assoc_of_heq {w x y z : D} {p p' q q' r r' a b k : ℤ}
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R w x p) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y q) (h : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z r)
    (f' : _root_.SerrePositivity.DifferentialGraded.GradedHom R w x p') (g' : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y q') (h' : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z r')
    (hf : HEq f f') (hg : HEq g g') (hh : HEq h h')
    (hp : p = p') (hq : q = q') (hr : r = r')
    (ha : p + q = a) (hb : q' + r' = b) (hk : a + r = k) (hk' : p' + b = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R h (_root_.SerrePositivity.DifferentialGraded.compose R g f ha) hk = _root_.SerrePositivity.DifferentialGraded.compose R (_root_.SerrePositivity.DifferentialGraded.compose R h' g' hb) f' hk' := by
  subst p' q' r'
  cases hf
  cases hg
  cases hh
  exact compose_assoc_of_sum f g h ha hb hk

/-- 概要：右側から括った AW 三重合成の二切断に対応する項。
方針：先の切断点の接尾部分を後の切断点でさらに切って内側を合成する。
規約：i ≤ j で、後の射 h の接頭部分は i まで。
使われ方：HA 1.3.1.13 の h ⋆ (g ⋆ f) の二重和の各項。 -/
def awNestedRight {w x y z : D} {n : ℕ} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n)
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R w x n)
    (J : Finset (Fin (n + 1))) (i j : J) (hij : i.val ≤ j.val)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) : GradedHom R w z k :=
  compose R (h.component (J.filter (· ≤ i.val)) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.left_nonempty i.property) rfl)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm g f (J.filter (i.val ≤ ·))
      ⟨j.val, Finset.mem_filter.mpr ⟨j.property, hij⟩⟩ _ rfl)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.degree_add i.property]; exact hk.symm)

/-- 概要：左側から括った AW 三重合成の二切断に対応する項。
方針：後の切断点の接頭部分を先の切断点でさらに切って内側を合成する。
規約：i ≤ j で、前の射 f の接尾部分は j から。
使われ方：HA 1.3.1.13 の (h ⋆ g) ⋆ f の二重和の各項。 -/
def awNestedLeft {w x y z : D} {n : ℕ} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n)
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R w x n)
    (J : Finset (Fin (n + 1))) (i j : J) (hij : i.val ≤ j.val)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) : GradedHom R w z k :=
  compose R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm h g (J.filter (· ≤ j.val))
      ⟨i.val, Finset.mem_filter.mpr ⟨i.property, hij⟩⟩ _ rfl)
    (f.component (J.filter (j.val ≤ ·)) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.right_nonempty j.property) rfl)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.degree_add j.property]; exact hk.symm)

/-- 概要：同じ二切断に対応する AW 三重合成の二つの括弧付けは一致する。
方針：接頭・中間・接尾の反復切断の集合を同定し、通常順の結合則を適用する。
規約：成分族に標準方程式は仮定しない。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の AW 結合律の各項。 -/
lemma awNestedRight_eq_left {w x y z : D} {n : ℕ} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n)
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R w x n)
    (J : Finset (Fin (n + 1))) (i j : J) (hij : i.val ≤ j.val)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    awNestedRight h g f J i j hij k hk = awNestedLeft h g f J i j hij k hk := by
  unfold awNestedRight awNestedLeft _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm
  apply compose_assoc_of_heq
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.component_heq_of_eq f _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.right_right hij) _ _ _ _ _ _
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.component_heq_of_eq g _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.middle.symm _ _ _ _ _ _
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.component_heq_of_eq h _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.left_left hij).symm _ _ _ _ _ _
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.right_right hij]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.middle]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.left_left hij]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms
