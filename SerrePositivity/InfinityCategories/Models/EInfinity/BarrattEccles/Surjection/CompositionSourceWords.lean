module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccessSums
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWords

/-!
模型。文献の定義との比較は後で
# 成功二表データと各列の成功基底語の和の添字

概要：Berger–Fresse §1.5.6 の元の二つの TR 和と分割和を同じ有限添字へ揃える。
方針：各列の成功 Schedule・基底語と重なり分割の依存直和を TableCompositionData と同値にする。
規約：元の両置換列と挿入位置を固定し、正の内側 arity を使う。
使われ方：成功二表の全符号付き和を両線形部分合成へ同定する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：元の二つの成功基底語の対と全重なり分割（BF §1.5.6）。
方針：各列の実際の成功型を二つ取り、その外側語の出現回数で分割型を指定する。
規約：分割型は外側成功基底語に依存する。
使われ方：各 onSequence の展開と compositionOnWords の分割和を直接表す。 -/
abbrev WordSource {m n d e : ℕ}
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :=
  Σ u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord outer, Σ _v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord inner,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val.2.val k) (n + e)

/-- 概要：固定列の成功二表データを各列の成功基底語と分割へ分ける（BF §1.5.6）。
方針：固定条件を消去し、元の両 Schedule・両語・成功等式と分割をそのまま返す。
規約：証明の選び方による違いは持たない。
使われ方：元データの有限和を二つの成功和と分割和へ展開する。 -/
def toWords {m n d e : ℕ}
    {outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1))}
    {inner : Fin (e + 1) → Equiv.Perm (Fin n)} {k : Fin (m + 1)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.WordSource outer inner k := by
  rcases c with ⟨⟨outer', su, u, hu, inner', sv, v, hv, slot, cuts, hpos⟩, ho, hi, hk⟩
  dsimp only at ho hi hk
  cases ho
  cases hi
  cases hk
  exact ⟨⟨(su, u), hu⟩, ⟨(sv, v), hv⟩, cuts⟩

/-- 概要：各列の成功基底語と分割を固定列の成功二表データへまとめる（BF §1.5.6）。
方針：元の成功等式を既存の入力構造の各欄へ入れる。
規約：内側語長の正値性は正の arity から導く。
使われ方：元データの依存直和表示の逆方向。 -/
def ofWords {m n d e : ℕ} (hn : 0 < n)
    {outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1))}
    {inner : Fin (e + 1) → Equiv.Perm (Fin n)} {k : Fin (m + 1)}
    (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.WordSource outer inner k) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k :=
  ⟨⟨outer, p.1.val.1, p.1.val.2, p.1.property, inner, p.2.1.val.1, p.2.1.val.2,
    p.2.1.property, k, p.2.2, by omega⟩, rfl, rfl, rfl⟩

/-- 概要：固定列の成功二表と各列の成功基底語＋分割の同値（BF §1.5.6）。
方針：固定条件と成功等式の証明の違いを無視して二つの構造の欄を往復する。
規約：依存する分割型も元の語とともに保持する。
使われ方：有限和を二つの TR 和と部分合成の分割和へ変形する。 -/
def wordsEquiv {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.WordSource outer inner k where
  toFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.toWords
  invFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.ofWords hn
  left_inv := by
    intro c
    rcases c with ⟨⟨outer', su, u, hu, inner', sv, v, hv, slot, cuts, hpos⟩, ho, hi, hk⟩
    dsimp only at ho hi hk
    cases ho
    cases hi
    cases hk
    rfl
  right_inv := by
    intro p
    rcases p with ⟨⟨⟨su, u⟩, hu⟩, ⟨⟨sv, v⟩, hv⟩, cuts⟩
    rfl

/-- 概要：成功二表を分けても各符号付き合成項は変わらない（BF §1.5.6）。
方針：固定列・位置の等式を消去し、元の語・分割が同じであることを使う。
規約：任意の可換環上。
使われ方：依存直和による有限和の添字変更で符号と合成語を保存する。 -/
lemma sourceTerm_toWords (A : Type*) [CommRing A] {m n d e : ℕ}
    {outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1))}
    {inner : Fin (e + 1) → Equiv.Perm (Fin n)} {k : Fin (m + 1)} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceTerm A c = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.toWords c).1.val.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.toWords c).2.1.val.2 k
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.toWords c).2.2 • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.toWords c).1.val.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.toWords c).2.1.val.2 k
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.toWords c).2.2 := by
  rcases c with ⟨⟨outer', su, u, hu, inner', sv, v, hv, slot, cuts, hpos⟩, ho, hi, hk⟩
  dsimp only at ho hi hk
  cases ho
  cases hi
  cases hk
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess
