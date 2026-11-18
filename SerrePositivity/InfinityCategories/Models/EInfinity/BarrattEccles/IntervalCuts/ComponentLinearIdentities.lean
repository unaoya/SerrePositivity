module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeChainIdentity
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.VertexChainIdentity

/-!
模型。文献の定義との比較は後で
# 区間切断成分の微分条件の線形写像としての等式

概要：Berger–Fresse §2.2.7 の頂点・辺の全基底での微分比較を全射語加群の線形等式へ移す。
方針：全射語の自由基底の外延性で既存の実際の微分恒等式を適用する。
規約：各等式は任意の可換環・全 arity に成立する。
使われ方：χ の実際の複体と区間のテンソルからの射の微分条件。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：正次数の辺成分と微分は全射語加群全体で可換（BF §2.2.7）。
方針：自由基底上の実際の辺微分恒等式を使う。
規約：語次数 d+1 から d の比較。
使われ方：余演算の辺入力に対する線形な微分条件。 -/
lemma edgeComponent_d_positive (n d : ℕ) :
    ((power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-((d + 2 : ℕ) : ℤ)) (-((d + 1 : ℕ) : ℤ))).hom.comp
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent A n (d + 1)) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent A n d).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d) := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n (d + 1)).ext
  intro u
  obtain ⟨u⟩ := u
  simp only [LinearMap.comp_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent_basis, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential_basis]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord_d_positive A u

/-- 概要：零次数の辺成分の微分は二頂点成分の差という線形等式（BF §2.2.7）。
方針：全ての置換語基底に次数零の辺恒等式を適用する。
規約：arity 零も含む。
使われ方：余演算の入力辺自身の微分との比較。 -/
lemma edgeComponent_d_zero (n : ℕ) :
    ((power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-1) 0).hom.comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent A n 0) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n 0 1 - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n 0 0 := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n 0).ext
  intro u
  obtain ⟨u⟩ := u
  change (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-1) 0
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent A n 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n 0 (ULift.up u))) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n 0 1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n 0 (ULift.up u)) -
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n 0 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n 0 (ULift.up u))
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent_basis A u, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_basis A u 1, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_basis A u 0]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord_d_zero A u

/-- 概要：頂点成分の出力は全射語加群全体で閉じている（BF §2.2.7）。
方針：自由基底の全頂点値の微分零を使う。
規約：語の全次数を扱う。
使われ方：頂点入力の標的微分。 -/
lemma vertexComponent_d_eq_zero (n d : ℕ) (b : Fin 2) :
    ((power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-(d : ℤ)) (-(d : ℤ) + 1)).hom.comp
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n d b) = 0 := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d).ext
  intro u
  obtain ⟨u⟩ := u
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_basis]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord_d_eq_zero A u b

/-- 概要：頂点成分に続く削除微分は全射語加群全体で零（BF §2.2.7）。
方針：次数一の二項相殺と高次数零性を自由基底の外延性で移す。
規約：語次数 d+1 から d の全てを扱う。
使われ方：頂点入力の第一因子微分の消滅。 -/
lemma vertexComponent_differential (n d : ℕ) (b : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n d b).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d) = 0 := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n (d + 1)).ext
  intro u
  obtain ⟨u⟩ := u
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential_basis]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_differentialOnWord A u b

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
