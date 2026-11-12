module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanComparisonAWBoundaryIndex

/-!
# AW 合成の成分の微分

概要：標準単体の AW 成分族を微分すると、左右の標準境界を合成する和が得られる。
方針：各切断点で Leibniz 則と標準単体の方程式を使う。
規約：Leibniz の次数は後の射の接頭部分の cochain 次数。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の標準方程式の保存の証明。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y z : D}

/-- 概要：AW の一つの切断項の微分は左右の標準境界との合成である。
方針：dg の通常順 Leibniz 則と標準単体の方程式を使う。
規約：方程式は実際の標準単体から取り、追加仮定にはしない。
使われ方：HA 1.3.1.13 の AW の微分の各項。 -/
lemma differential_awTerm {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R y z n)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) (J : Finset (Fin (n + 1))) (i : J) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    differential R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm g.val f.val J i k hk) =
      compose R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs g.val (J.filter (· ≤ i.val)) _ rfl)
        (f.val.component (J.filter (i.val ≤ ·)) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.right_nonempty i.property) rfl)
        (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.degree_add i.property; omega) +
      (1 - ((J.filter (· ≤ i.val)).card : ℤ)).negOnePow •
        _root_.SerrePositivity.DifferentialGraded.compose R
          (g.val.component (J.filter (· ≤ i.val)) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.left_nonempty i.property) rfl)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs f.val (J.filter (i.val ≤ ·)) _ rfl)
          (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.degree_add i.property; omega) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm
  rw [_root_.SerrePositivity.DifferentialGraded.differential_compose, g.property, f.property]

/-- 概要：標準単体の AW 成分族の微分は切断項の微分の和である。
方針：Hom の微分の線形性で有限和を外へ出す。
規約：成分の終次数を k+1 として保つ。
使われ方：Kerodon 2.5.8（Tag 00S0） の標準方程式の保存における境界和の展開。 -/
lemma differential_awData_component {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R y z n)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    differential R ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g.val f.val).component J k hJ hk) =
      ∑ i : J, differential R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm g.val f.val J i k hk) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component]
  exact map_sum ((_root_.SerrePositivity.DifferentialGraded.homObject R D x z).d k (k + 1)).hom _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
