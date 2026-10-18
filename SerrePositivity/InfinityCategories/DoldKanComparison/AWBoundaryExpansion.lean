module

public import SerrePositivity.InfinityCategories.DoldKanComparison.AWDiagonal

/-!
# AW 微分の左右の削除和への展開

概要：標準単体の AW 合成の微分を、同じ全体境界符号を持つ二つの削除和へ展開する。
方針：全域評価による標準境界の式、斉次合成の整数線形性、切断符号の比較を使う。
規約：切断点自身の削除も和に含める。
使われ方：HA 1.3.1.13、Kerodon 2.5.8 の AW の chain map 性の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DoldKanComparison

open CategoryTheory DifferentialGraded DGNerve.PinchedHom

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y z : D}

/-- 概要：通常順の斉次合成は後の射の整数倍を保つ。
方針：tensor と Hom 複体の線形写像の整数線形性を使う。
規約：整数スカラーと dg の符号単元の作用を可換にする。
使われ方：Kerodon 2.5.8 の標準境界の係数を合成の外へ出す。 -/
lemma compose_zsmul_left {p q k : ℤ} (a : ℤ) (g : GradedHom R y z q)
    (f : GradedHom R x y p) (hk : p + q = k) :
    compose R (a • g) f hk = a • compose R g f hk := by
  simp only [compose, forward, TensorProduct.tmul_smul, map_zsmul]
  exact smul_comm _ _ _

/-- 概要：通常順の斉次合成は前の射の整数倍を保つ。
方針：tensor と Hom 複体の線形写像の整数線形性を使う。
規約：整数スカラーと dg の符号単元の作用を可換にする。
使われ方：Kerodon 2.5.8 の標準境界の係数を合成の外へ出す。 -/
lemma compose_zsmul_right {p q k : ℤ} (a : ℤ) (g : GradedHom R y z q)
    (f : GradedHom R x y p) (hk : p + q = k) :
    compose R g (a • f) hk = a • compose R g f hk := by
  simp only [compose, forward, ← TensorProduct.smul_tmul', map_zsmul]
  exact smul_comm _ _ _

/-- 概要：接頭部分の一点削除から来る AW 微分の項。
方針：後の射の削除成分を元の接尾成分と合成し、全体の削除符号を掛ける。
規約：空の削除集合の値は零である。
使われ方：HA 1.3.1.13 の AW 微分の第一の二重和。 -/
def awBoundaryLeftTerm {n : ℕ} (g : LinearData R y z n) (f : LinearData R x y n)
    (J : Finset (Fin (n + 1))) (i : J) (j : Fin (n + 1)) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) : GradedHom R x z (k + 1) :=
  (-1 : ℤ) ^ (J.filter (· < j)).card •
    compose R
      (g.componentOrZero ((J.filter (· ≤ i.val)).erase j)
        (1 - ((J.filter (· ≤ i.val)).card : ℤ) + 1))
      (f.component (J.filter (i.val ≤ ·)) _ (AWIndex.right_nonempty i.property) rfl)
      (by have := AWIndex.degree_add i.property; omega)

/-- 概要：接尾部分の一点削除から来る AW 微分の項。
方針：元の接頭成分を前の射の削除成分と合成し、全体の削除符号を掛ける。
規約：Leibniz の符号は全体の削除符号に既に吸収した。
使われ方：HA 1.3.1.13 の AW 微分の第二の二重和。 -/
def awBoundaryRightTerm {n : ℕ} (g : LinearData R y z n) (f : LinearData R x y n)
    (J : Finset (Fin (n + 1))) (i : J) (j : Fin (n + 1)) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) : GradedHom R x z (k + 1) :=
  (-1 : ℤ) ^ (J.filter (· < j)).card •
    compose R
      (g.component (J.filter (· ≤ i.val)) _ (AWIndex.left_nonempty i.property) rfl)
      (f.componentOrZero ((J.filter (i.val ≤ ·)).erase j)
        (1 - ((J.filter (i.val ≤ ·)).card : ℤ) + 1))
      (by have := AWIndex.degree_add i.property; omega)

/-- 概要：AW の切断項の微分は左右の削除和で表せる。
方針：標準単体の方程式を全域的削除和にし、合成を分配して符号を統一する。
規約：切断点自身の削除を含む。
使われ方：HA 1.3.1.13 の標準方程式の保存における二重和の入口。 -/
lemma differential_awTerm_eq_sums {n : ℕ} (g : StandardSimplex R y z n)
    (f : StandardSimplex R x y n) (J : Finset (Fin (n + 1))) (i : J) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    differential R (awTerm g.val f.val J i k hk) =
      (∑ j : J.filter (· ≤ i.val), awBoundaryLeftTerm g.val f.val J i j.val k hk) +
        ∑ j : J.filter (i.val ≤ ·), awBoundaryRightTerm g.val f.val J i j.val k hk := by
  rw [differential_awTerm, standardRhs_eq_deleteSum, standardRhs_eq_deleteSum,
    DGNerve.compose_sum_left, DGNerve.compose_sum_right]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [compose_zsmul_left]
    unfold awBoundaryLeftTerm
    rw [AWIndex.before_left (Finset.mem_filter.mp j.property).2]
  · simp only [Units.smul_def, Finset.smul_sum, compose_zsmul_right, smul_smul]
    apply Finset.sum_congr rfl
    intro j _
    unfold awBoundaryRightTerm
    rw [AWIndex.sign_right i.property (Finset.mem_filter.mp j.property).2]

/-- 概要：標準単体の AW 成分の微分は左右の全ての削除項の二重和である。
方針：微分を切断点の和へ分配して各切断項の削除和を適用する。
規約：非対角項の対応と対角項の相殺はこの二重和に対して行う。
使われ方：Kerodon 2.5.8 の AW の標準方程式の保存の計算。 -/
lemma differential_awData_component_eq_sums {n : ℕ} (g : StandardSimplex R y z n)
    (f : StandardSimplex R x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    differential R ((awData g.val f.val).component J k hJ hk) =
      (∑ i : J, ∑ j : J.filter (· ≤ i.val), awBoundaryLeftTerm g.val f.val J i j.val k hk) +
        ∑ i : J, ∑ j : J.filter (i.val ≤ ·), awBoundaryRightTerm g.val f.val J i j.val k hk := by
  rw [differential_awData_component]
  simp_rw [differential_awTerm_eq_sums]
  rw [Finset.sum_add_distrib]

end SerrePositivity.InfinityCategories.DoldKanComparison
