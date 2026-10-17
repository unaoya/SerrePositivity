module
public import SerrePositivity.InfinityCategories.DGNerve.LinearBoundary

/-! # 方程式の右辺の線形部分と合成部分

概要：HA の方程式の右辺を削除成分の和と左右切断の合成の和の差に分解する。
方針：両者を同じ内部点集合で添字付けし、各項で元の成分の評価に戻す。
規約：HA Construction 1.3.1.6、Proposition 1.3.1.10。
使われ方：残差恒等式で削除・混合・三重合成の各部分を分離する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：切断点で左右の成分を合成し、次数の和が合わないときは零とする補助評価。
方針：元の成分の零による全域化と、合成の次数の等式の条件分岐を使う。
規約：HA Construction 1.3.1.6。使われ方：内部点集合にわたる合成部分の有限和。 -/
def cutCompose {n : ℕ} (s : SimplexData A D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1)) :
    GradedHom A (s.obj a) (s.obj b) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 then
    compose A (s.homOrZero (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ)))
      (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ))) h
  else 0

/-- 概要：単体の方程式の合成部分は、内部点での左右切断の合成の符号付き和。
方針：全域化した合成評価を内部点の有限集合で足し合わせる。
規約：HA Construction 1.3.1.6。使われ方：方程式の非線形部分の計算。 -/
def quadraticBoundary {n : ℕ} (s : SimplexData A D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) : GradedHom A (s.obj a) (s.obj b) (k + 1) :=
  ∑ j ∈ Index.interior I a b, Index.sign I j • s.cutCompose I a b k j

/-- 概要：元の内部点の寄与は、全域化した削除成分と切断合成の差に符号を掛けたもの。
方針：削除と左右切断の端点・次数・濃度を確認し、全域化した評価を元の評価へ戻す。
規約：HA Construction 1.3.1.6。使われ方：元の右辺と削除・合成の分解との一致。 -/
lemma term_eq_linear_sub_cut {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    s.term I a b k hI ha hb hk j hj haj hjb =
      Index.sign I j • (s.homOrZero (I.erase j) a b (k + 1) - s.cutCompose I a b k j) := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by rw [hb]; exact I.isGreatest_max' _
  have hE := Index.erase_two hamin.1 hbmax.1 haj hjb
  have hL := Index.left_two hamin.1 hj haj
  have hR := Index.right_two hj hbmax.1 hjb
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := Index.split_card hj
    omega
  rw [homOrZero_eq s _ _ _ _ hE (Index.erase_min hamin haj _)
    (Index.erase_max hbmax hjb _) (by have := Finset.card_erase_add_one hj; omega)]
  unfold cutCompose
  rw [dite_eq_left hsum]
  rw [homOrZero_eq s _ _ _ _ hR (Index.right_min hj _) (Index.right_max hbmax hjb.le _) rfl,
    homOrZero_eq s _ _ _ _ hL (Index.left_min hamin haj.le _) (Index.left_max hj _) rfl]
  rfl

/-- 概要：元の方程式の右辺は、線形な削除部分から左右切断の合成部分を引いたもの。
方針：全ての項を同じ内部点の有限集合へ移し、有限和と差の分配を使う。
規約：HA Proposition 1.3.1.10。使われ方：主残差恒等式の三種類の相殺への分解。 -/
lemma rhs_eq_linear_sub_quadratic {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    s.rhs I a b k hI ha hb hk = s.linearBoundary I a b k - s.quadraticBoundary I a b k := by
  rw [linearBoundary, quadraticBoundary, ← Finset.sum_sub_distrib]
  simp only [Index.interior, Finset.sum_filter]
  rw [← Finset.sum_coe_sort I]
  unfold rhs
  apply Finset.sum_congr rfl
  intro j _
  by_cases hint : a < j.val ∧ j.val < b
  · simp only [dite_eq_left hint, ite_eq_left hint, ← smul_sub]
    exact term_eq_linear_sub_cut s I a b k hI ha hb hk j.val j.property hint.1 hint.2
  · simp only [dite_eq_right hint, ite_eq_right hint]

/-- 概要：次数の合う切断合成の微分は、通常順合成の Leibniz 則で展開できる。
方針：全域化の次数の条件分岐を評価し、既存の dg 圏の微分合成則を適用する。
規約：HA Proposition 1.3.1.10。使われ方：残差恒等式で微分する合成項の展開。 -/
lemma differential_cutCompose {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1))
    (hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1) :
    differential A (s.cutCompose I a b k j) =
      compose A
        (differential A (s.homOrZero (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ))))
        (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ))) (by omega) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)).negOnePow •
        compose A (s.homOrZero (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ)))
          (differential A (s.homOrZero (I.filter (· ≤ j)) a j
            (2 - ((I.filter (· ≤ j)).card : ℤ)))) (by omega) := by
  rw [cutCompose, dite_eq_left hsum, differential_compose]

/-- 概要：方程式の右辺の微分は、削除成分の微分の和と切断合成の微分の和の差。
方針：右辺の分解と微分の有限和・符号スカラー・差の保存を使う。
規約：HA Proposition 1.3.1.10。使われ方：主残差恒等式に単体の真部分集合の式を代入する。 -/
lemma differential_rhs {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    differential A (s.rhs I a b k hI ha hb hk) =
      (∑ j ∈ Index.interior I a b, Index.sign I j •
        differential A (s.homOrZero (I.erase j) a b (k + 1))) -
      ∑ j ∈ Index.interior I a b, Index.sign I j • differential A (s.cutCompose I a b k j) := by
  rw [rhs_eq_linear_sub_quadratic s I a b k hI ha hb hk, differential_sub]
  simp only [linearBoundary, quadraticBoundary, differential_sum, differential_units_smul]

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
