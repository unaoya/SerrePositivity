module

public import SerrePositivity.EInfinity.IntervalCuts.EdgeChainIdentity
public import SerrePositivity.EInfinity.IntervalCuts.VertexChainIdentity

/-!
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

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：正次数の辺成分と微分は全射語加群全体で可換（BF §2.2.7）。
方針：自由基底上の実際の辺微分恒等式を使う。
規約：語次数 d+1 から d の比較。
使われ方：余演算の辺入力に対する線形な微分条件。 -/
lemma edgeComponent_d_positive (n d : ℕ) :
    ((power (interval A) n).d (-((d + 2 : ℕ) : ℤ)) (-((d + 1 : ℕ) : ℤ))).hom.comp
        (edgeComponent A n (d + 1)) =
      (edgeComponent A n d).comp (differential A n d) := by
  apply (basis A n (d + 1)).ext
  intro u
  obtain ⟨u⟩ := u
  simp only [LinearMap.comp_apply, edgeComponent_basis, differential_basis]
  exact edgeComponentOnWord_d_positive A u

/-- 概要：零次数の辺成分の微分は二頂点成分の差という線形等式（BF §2.2.7）。
方針：全ての置換語基底に次数零の辺恒等式を適用する。
規約：arity 零も含む。
使われ方：余演算の入力辺自身の微分との比較。 -/
lemma edgeComponent_d_zero (n : ℕ) :
    ((power (interval A) n).d (-1) 0).hom.comp (edgeComponent A n 0) =
      vertexComponent A n 0 1 - vertexComponent A n 0 0 := by
  apply (basis A n 0).ext
  intro u
  obtain ⟨u⟩ := u
  change (power (interval A) n).d (-1) 0
      (edgeComponent A n 0 (basis A n 0 (ULift.up u))) =
    vertexComponent A n 0 1 (basis A n 0 (ULift.up u)) -
      vertexComponent A n 0 0 (basis A n 0 (ULift.up u))
  rw [edgeComponent_basis A u, vertexComponent_basis A u 1, vertexComponent_basis A u 0]
  exact edgeComponentOnWord_d_zero A u

/-- 概要：頂点成分の出力は全射語加群全体で閉じている（BF §2.2.7）。
方針：自由基底の全頂点値の微分零を使う。
規約：語の全次数を扱う。
使われ方：頂点入力の標的微分。 -/
lemma vertexComponent_d_eq_zero (n d : ℕ) (b : Fin 2) :
    ((power (interval A) n).d (-(d : ℤ)) (-(d : ℤ) + 1)).hom.comp
        (vertexComponent A n d b) = 0 := by
  apply (basis A n d).ext
  intro u
  obtain ⟨u⟩ := u
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, vertexComponent_basis]
  exact vertexComponentOnWord_d_eq_zero A u b

/-- 概要：頂点成分に続く削除微分は全射語加群全体で零（BF §2.2.7）。
方針：次数一の二項相殺と高次数零性を自由基底の外延性で移す。
規約：語次数 d+1 から d の全てを扱う。
使われ方：頂点入力の第一因子微分の消滅。 -/
lemma vertexComponent_differential (n d : ℕ) (b : Fin 2) :
    (vertexComponent A n d b).comp (differential A n d) = 0 := by
  apply (basis A n (d + 1)).ext
  intro u
  obtain ⟨u⟩ := u
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, differential_basis]
  exact vertexComponent_differentialOnWord A u b

end SerrePositivity.EInfinity.IntervalCuts
