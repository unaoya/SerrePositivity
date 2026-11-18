module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RegularFactorSums
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.BoundaryPositions

/-!
模型。文献の定義との比較は後で
# 実際の辺成分の微分と全因子境界和

概要：Berger–Fresse §2.2.7 の実際の辺成分の微分を共通次数の全活動位置境界へ展開する。
方針：指定次数への移送と微分を交換し、非零切断ごとのテンソル境界和を足す。
規約：活動位置を区切りと切断点に分け、両因子境界和を同じ成分で比較する。
使われ方：辺での微分保存を正次数・次数零の両方で閉じる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable (A : Type u) [CommRing A]

/-- 概要：指定次数のテンソル生成元の微分は元次数の微分を移したもの（BF §2.2.7）。
方針：次数等式を消去して同じ微分へ戻す。
規約：微分の標的整数次数も等式で指定する。
使われ方：実際の切断テンソルの微分を共通境界次数へ展開する。 -/
lemma tensorVectorOfDegree_d_at (n q : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (r : ℤ)
    (hq : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f = q) (hr : -(q : ℤ) + 1 = r) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-(q : ℤ)) r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n q f hq) =
      eqToHom (congrArg (fun s : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X s)
          (by omega : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1 = r))
        ((power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n f)) := by
  subst q
  subst r
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree, eqToHom_refl, ModuleCat.id_apply]

/-- 概要：一非零切断の指定次数テンソルの微分は全活動位置因子境界の和（BF §2.2.7）。
方針：指定次数の微分公式と既存のテンソル境界和を使う。
規約：符号付きの実際のテンソルを語次数の負の成分へ送る。
使われ方：全辺成分の微分を各因子へ分割する。 -/
lemma edgeOutput_component_boundary {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val p • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n (d + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree u p h)) =
      ∑ a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.factorBoundaryValue A u p h (u.val a) := by
  rw [map_zsmul, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree_d_at A n (d + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) (-(d : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree u p h) (by omega), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tensorVector_d A u p h]
  simp only [map_sum, Finset.smul_sum, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.factorBoundaryValue, map_zsmul]

/-- 概要：実際の全辺成分の微分は全非零切断・全活動位置の因子境界和（BF §2.2.7）。
方針：辺成分を非零切断部分型へ展開し、微分を和の各項へ適用する。
規約：語の全次数に成立する。
使われ方：全削除和との比較の左辺。 -/
lemma edgeComponentOnWord_boundary_activities {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A u) =
      ∑ p : {p : Fin (n + d) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p},
        ∑ a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p.val, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.factorBoundaryValue A u p.val p.property (u.val a) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord_sum_subtype, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_component_boundary A u p.val p.property

/-- 概要：切断点色全境界和は非零切断部分型上の共通因子境界値の和（BF §2.2.7）。
方針：退化切断の零項を除く。
規約：次数移送の証明は一意。
使われ方：全活動位置境界の切断点部分との比較。 -/
lemma pivotBoundaryValue_sum_factors {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    (∑ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue A u p) =
      ∑ p : {p : Fin (n + d) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p},
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.factorBoundaryValue A u p.val p.property (u.val p.val) := by
  change (∑ p, if h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p then
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.factorBoundaryValue A u p h (u.val p) else 0) = _
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_dite_eq_subtype _ _

/-- 概要：実際の全辺成分の微分は全反復色境界と全切断点色境界の和（BF §2.2.7）。
方針：活動集合を切断点と全区切りに分け、共通次数の各因子境界を足す。
規約：切断点自身は区切りではない。
使われ方：実際の削除微分の同じ二つの和との照合。 -/
lemma edgeComponentOnWord_boundary_factors {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A u) =
      (∑ p : {p : Fin (n + d) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p},
        ∑ a : {a : Fin (n + d) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val a},
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.factorBoundaryValue A u p.val p.property (u.val a.val)) +
        ∑ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue A u p := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord_boundary_activities, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue_sum_factors,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hp : p.val ∉ Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val) := by
    intro hp
    exact (lt_irrefl _) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_before_pivot p.property (Finset.mem_filter.mp hp).2)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions, Finset.sum_insert hp, add_comm]
  congr 1
  exact Finset.sum_subtype _ (fun _ => by simp) _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
