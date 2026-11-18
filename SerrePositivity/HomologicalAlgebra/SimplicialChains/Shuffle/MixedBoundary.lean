module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwapFaces
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleMixedBoundary
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.MixedFaces

/-!
# 一般の単体集合のshuffle の混合角の境界和の消滅

概要：Berger–Fresse §1.1.3 の shuffle の微分で、水平辺と垂直辺が隣り合う角の寄与を消去する。
方針：混合角を交換する固定点のない involution により、符号が反対の二項を対にする。
規約：境界の符号 (−1)^b と shuffle の signature の両方を含める。
使われ方：shuffle の Leibniz 則を同じ向きの辺の削除と端点の計算に帰着する。
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

/-- 概要：混合角に対応する shuffle の符号つき境界項（Berger–Fresse §1.1.3）。
方針：指定した頂点を除く面の正規化鎖に shuffle 符号と境界符号を掛ける。
規約：面の族 f は after の辺番号、すなわち削除する頂点で添字づける。
使われ方：混合角全体の寄与を有限和で表す。 -/
def mixedCornerTerm (X Y : SSet.{0}) {p q r : ℕ}
    (f : Fin (p + q) → (⦋r⦌ ⟶ ⦋p + q⦌))
    (x : X _⦋p⦌) (y : Y _⦋q⦌)
    (c : MixedCorner p q) : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X r :=
  (-1 : ℤ) ^ c.after.val • ((c.path.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) r
    ((X ⊗ Y).map (f c.after).op (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y c.path x y)))

/-- 概要：交換された混合角の二つの境界項は相殺する（Berger–Fresse §1.1.3）。
方針：面の一致と shuffle 符号の反転に、同じ境界符号を掛ける。
規約：f b の像は頂点 b を避けると仮定する。
使われ方：混合角全体の有限和の相殺の一対の計算となる。 -/
lemma mixedCornerTerm_swap_add (X Y : SSet.{0}) {p q r : ℕ}
    (f : Fin (p + q) → (⦋r⦌ ⟶ ⦋p + q⦌))
    (hf : ∀ b j, ((f b).toOrderHom j).val ≠ b.val)
    (x : X _⦋p⦌) (y : Y _⦋q⦌)
    (c : MixedCorner p q) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.mixedCornerTerm A X Y f x y c.swap + _root_.SerrePositivity.SimplicialChains.Shuffle.mixedCornerTerm A X Y f x y c = 0 := by
  have h := _root_.SerrePositivity.SimplicialChains.Shuffle.swap_face_cancel A X Y c.path c.before c.after c.property.1 c.property.2
    (f c.after) (hf c.after) x y
  simpa only [_root_.SerrePositivity.SimplicialChains.Shuffle.mixedCornerTerm, MixedCorner.swap, MixedCorner.path, MixedCorner.after,
    smul_add, smul_zero] using congrArg (fun z => (-1 : ℤ) ^ c.after.val • z) h

/-- 概要：shuffle の全ての混合角の境界の和は零である（Berger–Fresse §1.1.3）。
方針：混合角の交換を有限和の固定点のない involution として用いる。
規約：境界符号と shuffle 符号を含む正規化鎖の和について述べる。
使われ方：Leibniz 則の証明から内部の異方向の辺の寄与を取り除く。 -/
lemma sum_mixedCornerTerm_eq_zero (X Y : SSet.{0}) {p q r : ℕ}
    (f : Fin (p + q) → (⦋r⦌ ⟶ ⦋p + q⦌))
    (hf : ∀ b j, ((f b).toOrderHom j).val ≠ b.val)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    ∑ c : MixedCorner p q, _root_.SerrePositivity.SimplicialChains.Shuffle.mixedCornerTerm A X Y f x y c = 0 := by
  classical
  apply Finset.sum_ninvolution (g := MixedCorner.swap)
  · intro c
    exact (add_comm _ _).trans (_root_.SerrePositivity.SimplicialChains.Shuffle.mixedCornerTerm_swap_add A X Y f hf x y c)
  · intro c _
    exact c.swap_ne_self
  · intro c
    exact Finset.mem_univ _
  · exact MixedCorner.swap_swap

/-- 概要：標準の境界面に対する混合角の寄与の和は零である（Berger–Fresse §1.1.3）。
方針：各頂点を削除する実際の面写像を相殺定理へ適用する。
規約：正次数 p+q の境界の次数は p+q−1。
使われ方：shuffle の Leibniz 則の境界計算にそのまま用いる。 -/
lemma sum_mixedBoundary_eq_zero (X Y : SSet.{0}) (p q : ℕ)
    (hN : 0 < p + q) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    ∑ c : MixedCorner p q,
      _root_.SerrePositivity.SimplicialChains.Shuffle.mixedCornerTerm A X Y (middleFaceMap (p + q) hN) x y c = 0 :=
  _root_.SerrePositivity.SimplicialChains.Shuffle.sum_mixedCornerTerm_eq_zero A X Y (middleFaceMap (p + q) hN)
    (middleFaceMap_avoids (p + q) hN) x y

end SerrePositivity.SimplicialChains.Shuffle
