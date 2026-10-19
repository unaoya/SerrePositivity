module

public import SerrePositivity.EInfinity.IntervalCuts.EdgeComponentBoundary

/-!
# 区間切断の実際の辺成分の微分保存

概要：Berger–Fresse §2.2.7 の Δ¹ の辺上の微分保存を全 arity・全語次数で比較する。
方針：正次数は全削除和と全因子境界和を同定し、次数零は入力辺の両端差を使う。
規約：任意の可換環上の実際の非有界整数複体で等式を述べる。
使われ方：χ の区間余演算を複体射へ束ねる際の辺生成元の条件。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped BigOperators

variable (A : Type u) [CommRing A]

/-- 概要：正次数の語の実際の辺成分は削除微分と可換（BF §2.2.7）。
方針：出力全因子境界和と、三種類を統合した実際の全削除微分の辺成分を照合する。
規約：入力辺の二頂点に対する正次数の作用は零。
使われ方：区間余演算の正次数の辺生成元に対する複体射条件。 -/
lemma edgeComponentOnWord_d_positive {n d : ℕ} (u : BasisWord n (d + 1)) :
    (power (interval A) n).d (-((d + 2 : ℕ) : ℤ)) (-((d + 1 : ℕ) : ℤ))
        (edgeComponentOnWord A u) = edgeComponent A n d (differentialOnWord A u) :=
  (edgeComponentOnWord_boundary_factors A u).trans
    (edgeComponent_differentialOnWord_factor_sums A u).symm

/-- 概要：次数零の語の実際の辺成分の微分は二頂点成分の差（BF §2.2.7）。
方針：次数零の語の色は単射なので区切り因子境界を除き、全切断点境界の二端点公式を使う。
規約：arity 零でも二つの空テンソルの差として成立する。
使われ方：区間余演算の次数零の辺生成元に対する複体射条件。 -/
lemma edgeComponentOnWord_d_zero {n : ℕ} (u : BasisWord n 0) :
    (power (interval A) n).d (-1) 0 (edgeComponentOnWord A u) =
      vertexComponentOnWord A u 1 - vertexComponentOnWord A u 0 := by
  have hinj : Function.Injective u.val := (vertexNondegenerate_iff u).mpr rfl
  have hz : (∑ p : {p : Fin (n + 0) // EdgeNondegenerate u.val p},
      ∑ a : {a : Fin (n + 0) // Caesura u.val a},
        factorBoundaryValue A u p.val p.property (u.val a.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    apply Finset.sum_eq_zero
    intro a _
    obtain ⟨b, hab, hu⟩ := a.property
    exact False.elim ((ne_of_lt hab) (hinj hu.symm))
  have h := edgeComponentOnWord_boundary_factors A u
  simpa only [hz, zero_add, pivotBoundaryValue_sum_zeroDegree, Nat.cast_one, Nat.cast_zero,
    neg_zero, vertexComponentOnWord, dite_eq_left rfl] using! h

end SerrePositivity.EInfinity.IntervalCuts
