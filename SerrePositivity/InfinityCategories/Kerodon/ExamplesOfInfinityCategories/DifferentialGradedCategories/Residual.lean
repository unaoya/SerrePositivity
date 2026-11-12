module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Signs

/-! # 単体の方程式の残差

概要：微分と方程式の右辺の差を残差として定義し、その基本恒等式を示す。
方針：Hom 複体の微分の線形性と微分の二乗が零であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：欠けた面自身の方程式の検証。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：Hom 複体の微分の二乗は零。
方針：複体の `d_comp_d` を斉次元で評価する。
規約：HA Proposition 1.3.1.10、微分は +1。使われ方：残差の微分の計算。 -/
lemma differential_squared {x y : D} {k : ℤ} (f : GradedHom A x y k) :
    differential A (differential A f) = 0 :=
  congrArg (fun d => d f) ((homObject A D x y).d_comp_d k (k + 1) (k + 1 + 1))

/-- 概要：Hom 複体の微分は加法を保つ。
方針：微分の線形性。規約：HA Proposition 1.3.1.10。
使われ方：残差恒等式の有限和の展開。 -/
lemma differential_add {x y : D} {k : ℤ} (f g : GradedHom A x y k) :
    differential A (f + g) = differential A f + differential A g := by simp [differential]

/-- 概要：Hom 複体の微分は差を保つ。
方針：微分の線形性。規約：HA Proposition 1.3.1.10。
使われ方：残差の微分の展開。 -/
lemma differential_sub {x y : D} {k : ℤ} (f g : GradedHom A x y k) :
    differential A (f - g) = differential A f - differential A g := by simp [differential]

/-- 概要：Hom 複体の微分は符号スカラーを保つ。
方針：整数スカラーに対する線形性。規約：HA Proposition 1.3.1.10。
使われ方：負一冪を持つ有限和の微分の計算。 -/
lemma differential_units_smul {x y : D} {k : ℤ} (c : ℤˣ) (f : GradedHom A x y k) :
    differential A (c • f) = c • differential A f := by
  simp [differential, Units.smul_def]

/-- 概要：Hom 複体の微分は有限和と可換。
方針：線形写像の有限和の保存を使う。
規約：HA Proposition 1.3.1.10。使われ方：方程式の右辺の微分の展開。 -/
lemma differential_sum {ι : Type*} {x y : D} {k : ℤ} (S : Finset ι)
    (f : ι → GradedHom A x y k) :
    differential A (∑ t ∈ S, f t) = ∑ t ∈ S, differential A (f t) := by
  simp [differential]

namespace SimplexData

/-- 概要：成分族の残差は微分と HA の方程式の右辺の差。
方針：同じ次数 `k+1` の二つの射の差として定義する。
規約：HA Proposition 1.3.1.10。使われ方：欠けた面の方程式を零残差として検証する。 -/
def residual {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) : GradedHom A (s.obj a) (s.obj b) (k + 1) :=
  differential A (s.hom I a b k hI ha hb hk) - s.rhs I a b k hI ha hb hk

/-- 概要：残差が零であることは、その成分の単体の方程式と同値。
方針：加法群の差が零であることの判定。
規約：HA Proposition 1.3.1.10。使われ方：ホーン充填の各方程式の受入条件。 -/
lemma residual_eq_zero_iff {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    s.residual I a b k hI ha hb hk = 0 ↔
      differential A (s.hom I a b k hI ha hb hk) = s.rhs I a b k hI ha hb hk :=
  sub_eq_zero

/-- 概要：残差の微分は方程式の右辺の微分の負。
方針：微分の差の法則と二乗が零であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：欠けた面に残る残差を導く計算の出発点。 -/
lemma differential_residual {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    differential A (s.residual I a b k hI ha hb hk) =
      -differential A (s.rhs I a b k hI ha hb hk) := by
  rw [residual, differential_sub, differential_squared, zero_sub]

end SimplexData

namespace Simplex

/-- 概要：実際の単体の各成分の残差は零。
方針：単体の方程式と残差の零の判定を使う。
規約：HA Proposition 1.3.1.10。使われ方：ホーンの既知の面の残差を消去する。 -/
lemma residual_eq_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) : s.toSimplexData.residual I a b k hI ha hb hk = 0 :=
  (s.toSimplexData.residual_eq_zero_iff I a b k hI ha hb hk).mpr (s.equation I a b k hI ha hb hk)

end Simplex

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
