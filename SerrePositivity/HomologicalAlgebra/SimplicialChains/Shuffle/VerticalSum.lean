module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalCorner
public import Mathlib.Data.Fintype.BigOperators
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalSum
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.VerticalBoundary

/-!
# 一般の単体集合の内部の垂直面の有限和の添字替え

概要：Berger–Fresse §1.1.3 の内部の垂直面の和を第二の入力の内部の境界和と比較する。
方針：角の全単射を用い、各項の符号つき面の等式と入力の欠落頂点の番号を代入する。
規約：始端・終端は含めず、入力の内部面は Fin q の番号 j に対して j+1 とする。
使われ方：shuffle の Leibniz 則の第二の入力の内部微分を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：内部の垂直角に対応する符号つき正規化境界項（Berger–Fresse §1.1.3）。
方針：二辺の間の頂点を削除して shuffle 符号と境界符号を掛ける。
規約：角の辺番号 a に対する頂点の境界符号は (−1)^(a+1) である。
使われ方：内部の垂直角の全体にわたる和の被加数となる。 -/
def verticalCornerTerm (X Y : SSet.{0}) {p q : ℕ}
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌)
    (c : VerticalCorner p q) : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + q) :=
  (-1 : ℤ) ^ (c.val.2.val + 1) • (c.val.1.sign : ℤ) •
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
      ((X ⊗ Y).δ c.val.2.castSucc.succ
        (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q + 1) c.val.1 x y))

/-- 概要：垂直角の添字替えは第二の入力の内部面の番号と符号を保存する（Berger–Fresse §1.1.3）。
方針：垂直辺を挿入した角へ符号つき面の比較を適用し、昇順の辺番号を欠落頂点へ移す。
規約：入力の内部面の番号は j.succ.castSucc である。
使われ方：全単射による有限和の添字替えの各項の等式を与える。 -/
lemma verticalCornerTerm_indexed (X Y : SSet.{0}) {p q : ℕ}
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌)
    (s : ShufflePath p q) (j : Fin q) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.verticalCornerTerm A X Y x y
        (verticalCornerEquiv p q (verticalMarkedEdgeEquiv p q (s, j))) =
      (-1 : ℤ) ^ p • (-1 : ℤ) ^ (j.val + 1) • (s.sign : ℤ) •
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q) s x
            (Y.δ j.succ.castSucc y)) := by
  let v := verticalMarkedEdgeEquiv p q (s, j)
  let c := verticalCornerEquiv p q v
  have hcoord : c.val.1.vertical v.val.2.castSucc.succ = j.succ.castSucc := by
    apply Fin.ext
    have h := verticalCornerEquiv_vertical v
    change (c.val.1.vertical v.val.2.castSucc.succ).val =
      (s.vertical v.val.2.castSucc).val + 1 at h
    erw [verticalMarkedEdgeEquiv_vertical s j] at h
    exact h
  have hdel : (verticalInsertionEquiv p q v.val.2.castSucc).symm
      ⟨c.val.1, c.property.1⟩ = s :=
    (verticalInsertionEquiv p q v.val.2.castSucc).symm_apply_apply s
  change (-1 : ℤ) ^ (v.val.2.val + 1) • (c.val.1.sign : ℤ) •
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
      ((X ⊗ Y).δ v.val.2.castSucc.succ
        (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q + 1) c.val.1 x y)) = _
  erw [_root_.SerrePositivity.SimplicialChains.Shuffle.shuffle_vertical_face_signed A X Y c.val.1 v.val.2.castSucc v.val.2.succ
    rfl c.property.1 c.property.2 x y, hdel, hcoord]
  simp only [Fin.val_castSucc, Fin.val_succ]

/-- 概要：内部の垂直角の境界和は第二の入力の内部境界を用いた shuffle の和に等しい（Berger–Fresse §1.1.3）。
方針：角と小さい経路・垂直辺番号の全単射で有限和を添字替えし、各項の等式を使う。
規約：水平次数 p による Koszul 符号 (−1)^p を含む。
使われ方：Leibniz 則の第二の入力の内部微分の寄与を同定する。 -/
lemma sum_verticalCornerTerm (X Y : SSet.{0}) {p q : ℕ}
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌) :
    ∑ c : VerticalCorner p q, _root_.SerrePositivity.SimplicialChains.Shuffle.verticalCornerTerm A X Y x y c =
      ∑ s : ShufflePath p q, ∑ j : Fin q,
        (-1 : ℤ) ^ p • (-1 : ℤ) ^ (j.val + 1) • (s.sign : ℤ) •
          _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
            (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q) s x
              (Y.δ j.succ.castSucc y)) := by
  classical
  let e := (verticalMarkedEdgeEquiv p q).trans (verticalCornerEquiv p q)
  rw [← e.sum_comp (_root_.SerrePositivity.SimplicialChains.Shuffle.verticalCornerTerm A X Y x y), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro j _
  exact _root_.SerrePositivity.SimplicialChains.Shuffle.verticalCornerTerm_indexed A X Y x y s j

end SerrePositivity.SimplicialChains.Shuffle
