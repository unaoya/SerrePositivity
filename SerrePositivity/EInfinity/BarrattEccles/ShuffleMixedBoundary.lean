module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwapFaces
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# shuffle の混合角の境界和の消滅

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

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：経路とその中の隣り合う異方向の辺の組（Berger–Fresse §1.1.3）。
方針：有限な経路・辺の組に隣接性と向きが異なる条件を課す。
規約：二辺の順序は before、after とし、間の頂点番号は after である。
使われ方：shuffle の微分の混合角の寄与を添字づける。 -/
abbrev MixedCorner (p q : ℕ) :=
  {t : ShufflePath p q × (Fin (p + q) × Fin (p + q)) //
    t.2.2.val = t.2.1.val + 1 ∧ (t.2.1 ∈ t.1.val ↔ t.2.2 ∉ t.1.val)}

/-- 概要：混合角が属する shuffle 経路（Berger–Fresse §1.1.3）。
方針：有限な添字の組の第一成分を取る。
規約：水平辺集合として表された経路。
使われ方：境界項の合成単体と符号を取り出す。 -/
abbrev MixedCorner.path {p q : ℕ} (c : MixedCorner p q) : ShufflePath p q := c.val.1

/-- 概要：混合角の最初の辺の位置（Berger–Fresse §1.1.3）。
方針：辺の組の第一成分を取る。
規約：0 始まりの辺番号。
使われ方：二辺の交換を指定する。 -/
abbrev MixedCorner.before {p q : ℕ} (c : MixedCorner p q) : Fin (p + q) := c.val.2.1

/-- 概要：混合角の次の辺の位置（Berger–Fresse §1.1.3）。
方針：辺の組の第二成分を取る。
規約：この番号は削除する角の頂点番号にも一致する。
使われ方：面写像とその境界符号を指定する。 -/
abbrev MixedCorner.after {p q : ℕ} (c : MixedCorner p q) : Fin (p + q) := c.val.2.2

/-- 概要：混合角の二つの辺を交換する（Berger–Fresse §1.1.3）。
方針：経路に隣接交換を施し、辺番号と隣接性を保つ。
規約：交換後も二辺の向きは異なる。
使われ方：混合角の境界項を相殺する involution となる。 -/
def MixedCorner.swap {p q : ℕ} (c : MixedCorner p q) : MixedCorner p q :=
  ⟨(c.path.swapSteps c.before c.after, (c.before, c.after)),
    c.property.1, c.path.swapSteps_crossed c.before c.after c.property.2⟩

/-- 概要：混合角の交換は二回で元に戻る（Berger–Fresse §1.1.3）。
方針：経路の二回の互換と、変わらない辺番号を比較する。
規約：部分型の証明の値には依存しない。
使われ方：有限和の involution による相殺を適用する。 -/
@[simp] lemma MixedCorner.swap_swap {p q : ℕ} (c : MixedCorner p q) : c.swap.swap = c := by
  apply Subtype.ext
  apply Prod.ext
  · exact c.path.swapSteps_swapSteps c.before c.after
  · rfl

/-- 概要：混合角の交換には固定点がない（Berger–Fresse §1.1.3）。
方針：異なる向きの二辺の交換で経路が変わることを使う。
規約：符号や鎖の値に関係なく成立する。
使われ方：零でない境界項が自分自身と対にならないことを保証する。 -/
lemma MixedCorner.swap_ne_self {p q : ℕ} (c : MixedCorner p q) : c.swap ≠ c := by
  intro h
  exact c.path.swapSteps_ne_self c.before c.after c.property.2
    (congrArg MixedCorner.path h)

variable (A : Type u) [CommRing A]

/-- 概要：混合角に対応する shuffle の符号つき境界項（Berger–Fresse §1.1.3）。
方針：指定した頂点を除く面の正規化鎖に shuffle 符号と境界符号を掛ける。
規約：面の族 f は after の辺番号、すなわち削除する頂点で添字づける。
使われ方：混合角全体の寄与を有限和で表す。 -/
def mixedCornerTerm (m n : ℕ) (i : Fin (m + 1)) {p q r : ℕ}
    (f : Fin (p + q) → (⦋r⦌ ⟶ ⦋p + q⦌))
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (c : MixedCorner p q) : (normalizedChains A (m + n)).X r :=
  (-1 : ℤ) ^ c.after.val • ((c.path.sign : ℤ) • normalizedGenerator A (m + n) r
    ((simplicial (m + n)).map (f c.after).op (shuffleSimplex m n i c.path x y)))

/-- 概要：交換された混合角の二つの境界項は相殺する（Berger–Fresse §1.1.3）。
方針：面の一致と shuffle 符号の反転に、同じ境界符号を掛ける。
規約：f b の像は頂点 b を避けると仮定する。
使われ方：混合角全体の有限和の相殺の一対の計算となる。 -/
lemma mixedCornerTerm_swap_add (m n : ℕ) (i : Fin (m + 1)) {p q r : ℕ}
    (f : Fin (p + q) → (⦋r⦌ ⟶ ⦋p + q⦌))
    (hf : ∀ b j, ((f b).toOrderHom j).val ≠ b.val)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (c : MixedCorner p q) :
    mixedCornerTerm A m n i f x y c.swap + mixedCornerTerm A m n i f x y c = 0 := by
  have h := shuffle_swap_face_cancel A m n i c.path c.before c.after c.property.1 c.property.2
    (f c.after) (hf c.after) x y
  simpa only [mixedCornerTerm, MixedCorner.swap, MixedCorner.path, MixedCorner.after,
    smul_add, smul_zero] using congrArg (fun z => (-1 : ℤ) ^ c.after.val • z) h

/-- 概要：shuffle の全ての混合角の境界の和は零である（Berger–Fresse §1.1.3）。
方針：混合角の交換を有限和の固定点のない involution として用いる。
規約：境界符号と shuffle 符号を含む正規化鎖の和について述べる。
使われ方：Leibniz 則の証明から内部の異方向の辺の寄与を取り除く。 -/
lemma sum_mixedCornerTerm_eq_zero (m n : ℕ) (i : Fin (m + 1)) {p q r : ℕ}
    (f : Fin (p + q) → (⦋r⦌ ⟶ ⦋p + q⦌))
    (hf : ∀ b j, ((f b).toOrderHom j).val ≠ b.val)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    ∑ c : MixedCorner p q, mixedCornerTerm A m n i f x y c = 0 := by
  classical
  apply Finset.sum_ninvolution (g := MixedCorner.swap)
  · intro c
    exact (add_comm _ _).trans (mixedCornerTerm_swap_add A m n i f hf x y c)
  · intro c _
    exact c.swap_ne_self
  · intro c
    exact Finset.mem_univ _
  · exact MixedCorner.swap_swap

/-- 概要：正次数 N の経路から頂点 b を除く標準の面写像（Berger–Fresse §1.1.3）。
方針：Fin N と Fin(N−1+1) の次数同定の後に succAbove を適用する。
規約：b は最後の頂点より前にある頂点で、混合角では 0 でもない。
使われ方：抽象的な面の族による相殺を実際の境界面へ適用する。 -/
def middleFaceMap (N : ℕ) (hN : 0 < N) (b : Fin N) : ⦋N - 1⦌ ⟶ ⦋N⦌ :=
  SimplexCategory.mkHom {
    toFun j := b.castSucc.succAbove (Fin.cast (Nat.sub_add_cancel (by omega : 1 ≤ N)) j)
    monotone' := fun _ _ h => (Fin.strictMono_succAbove b.castSucc).monotone h }

/-- 概要：標準の面写像の像は削除した頂点を含まない（Berger–Fresse §1.1.3）。
方針：succAbove の値が指定した欠落点と異なることを使う。
規約：頂点番号の値の不一致として述べる。
使われ方：混合角の境界和の相殺条件を満たす。 -/
lemma middleFaceMap_avoids (N : ℕ) (hN : 0 < N) (b : Fin N)
    (j : Fin (N - 1 + 1)) : ((middleFaceMap N hN b).toOrderHom j).val ≠ b.val := by
  intro h
  exact Fin.succAbove_ne b.castSucc
    (Fin.cast (Nat.sub_add_cancel (by omega : 1 ≤ N)) j) (Fin.ext h)

/-- 概要：正次数を r+1 と書くと標準の面写像は δ に一致する（Berger–Fresse §1.1.3）。
方針：自然数の減算と次数同定を定義展開する。
規約：削除する頂点は b.castSucc である。
使われ方：交代面和としての微分と標準の面写像を接続する。 -/
lemma middleFaceMap_succ (r : ℕ) (b : Fin (r + 1)) :
    middleFaceMap (r + 1) (Nat.succ_pos r) b = SimplexCategory.δ b.castSucc := by
  rfl

/-- 概要：標準の境界面に対する混合角の寄与の和は零である（Berger–Fresse §1.1.3）。
方針：各頂点を削除する実際の面写像を相殺定理へ適用する。
規約：正次数 p+q の境界の次数は p+q−1。
使われ方：shuffle の Leibniz 則の境界計算にそのまま用いる。 -/
lemma sum_mixedBoundary_eq_zero (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (hN : 0 < p + q) (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    ∑ c : MixedCorner p q,
      mixedCornerTerm A m n i (middleFaceMap (p + q) hN) x y c = 0 :=
  sum_mixedCornerTerm_eq_zero A m n i (middleFaceMap (p + q) hN)
    (middleFaceMap_avoids (p + q) hN) x y

end SerrePositivity.EInfinity.BarrattEccles
