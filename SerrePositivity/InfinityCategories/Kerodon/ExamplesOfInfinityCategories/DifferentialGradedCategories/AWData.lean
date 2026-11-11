module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanIso
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra

/-!
# 標準 Hom の Alexander–Whitney 合成の成分族

概要：全ての切断点に沿う斉次合成の和で、標準座標の AW 成分族を定義する。
方針：後の射の接頭部分と前の射の接尾部分を通常順 compose で合成する。
規約：この定義は成分族の演算であり、標準方程式の保存は別途証明する。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の単体的豊穣合成。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y z : D}

/-- 概要：AW 合成の一つの切断点に対応する成分を定義する。
方針：接頭部分を後の射、接尾部分を前の射に評価して通常順に合成する。
規約：成分の次数の和は切断の濃度の式で保証する。
使われ方：HA 1.3.1.13 の AW の成分表示。 -/
def awTerm {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (j : J) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom R x z k :=
  compose R (g.component (J.filter (· ≤ j.val)) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.left_nonempty j.property) rfl)
    (f.component (J.filter (j.val ≤ ·)) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.right_nonempty j.property) rfl)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.degree_add j.property]; exact hk.symm)

/-- 概要：標準成分族の Alexander–Whitney 合成を定義する。
方針：指定した非空集合の全ての切断点について成分を足す。
規約：通常順に後の射 g、前の射 f を引数に取る。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の豊穣合成の台の成分族。 -/
def awData {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x z n := fun i ↦ ∑ j : i.val.1, awTerm g f i.val.1 j i.val.2 i.property.2

/-- 概要：AW 成分族の指定成分は全ての切断点での合成の和である。
方針：成分と成分族の定義を評価する。
規約：次数の証明を明示したまま述べる。
使われ方：Kerodon 2.5.8（Tag 00S0） の合成の方程式の展開。 -/
lemma awData_component {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (awData g f).component J k hJ hk = ∑ j : J, awTerm g f J j k hk := rfl

/-- 概要：AW 合成は後の射の成分族の加法を保つ。
方針：各切断点で合成の加法性を使い有限和を分配する。
規約：方程式を満たすことを仮定しない成分族についての等式。
使われ方：Kerodon 2.5.8（Tag 00S0） の単体的加群上の双線形性。 -/
lemma awData_add_left {n : ℕ} (g g' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) :
    awData (g + g') f = awData g f + awData g' f := by
  funext i
  simp only [awData, awTerm, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, Pi.add_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left,
    Finset.sum_add_distrib]

/-- 概要：AW 合成は前の射の成分族の加法を保つ。
方針：各切断点で合成の加法性を使い有限和を分配する。
規約：方程式を満たすことを仮定しない成分族についての等式。
使われ方：Kerodon 2.5.8（Tag 00S0） の単体的加群上の双線形性。 -/
lemma awData_add_right {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f f' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) :
    awData g (f + f') = awData g f + awData g f' := by
  funext i
  simp only [awData, awTerm, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, Pi.add_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_right,
    Finset.sum_add_distrib]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
