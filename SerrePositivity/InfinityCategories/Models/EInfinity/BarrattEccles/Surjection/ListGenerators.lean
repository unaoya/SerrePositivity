module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Modules
public import Mathlib.Data.List.GetD

/-!
模型。文献の定義との比較は後で
# リストから全射語の自由加群への正規化

概要：Berger–Fresse §1.3.1 の抽出された文字列を次数成分の元へ移す。
方針：長さを検査して有限語へ直し、退化・非全射なら零へ送る。
規約：指定した長さと異なるリストも零とする。
使われ方：table reduction の各項を定義する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：有限リストを対応する全射語の元か零へ送る（BF §1.3.1）。
方針：長さが n+d のとき各位置で読み、既存の正規化を使う。
規約：長さの不一致・退化・非全射は零。
使われ方：table の行の連結を自由加群へ送る。 -/
def listGenerator {n d : ℕ} (xs : List (Fin n)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  if h : xs.length = n + d then
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (fun i => xs[i.val]'(by omega)) else 0

/-- 概要：有限語のリスト化と正規化は元の正規化を与える（BF §1.3.1）。
方針：ofFn の長さと各成分の評価を使う。
規約：退化語・非全射語を含めて成立する。
使われ方：TR の次数零の公式を既存の語の生成元と比較する。 -/
@[simp]
lemma listGenerator_ofFn {n d : ℕ} (v : Fin (n + d) → Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (List.ofFn v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator
  simp only [List.length_ofFn, ↓reduceDIte]
  apply congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (n := n) (d := d))
  funext i
  simp only [List.getElem_ofFn, Fin.eta]

/-- 概要：文字列の正規化は値の置換と可換（BF §1.3.6）。
方針：長さを比較し、語の正規化の置換同変性を使う。
規約：無効な文字列も含む。
使われ方：TR の各項の同変性を証明する。 -/
lemma renameLinear_listGenerator {n d : ℕ} (σ : Equiv.Perm (Fin n))
    (xs : List (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A σ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (d := d) xs) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (xs.map σ) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator
  simp only [List.length_map]
  split
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear_generator]
    congr 1
    funext i
    simp only [Function.comp_apply, List.getElem_map]
  · exact map_zero _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
