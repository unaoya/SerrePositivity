module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.RawDifferential
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ListGenerators

/-!
模型。文献の定義との比較は後で
# リストの正規化と削除微分

概要：Berger–Fresse §1.4.4 の table 出力の微分をリストから直接計算する。
方針：正しい長さのリストを有限語へ変換し、任意の語の削除和を適用する。
規約：長さが n+d+1 と異なる入力は零。
使われ方：TR の各 table 項の境界を正規化の前の削除和へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：table 出力リストの符号付き削除和（BF §1.4.4）。
方針：正しい長さなら有限語として読み、rawDifferential を使う。
規約：退化・非全射な入力も処理する。
使われ方：TR の和における各項の微分を指定する。 -/
def rawListDifferential {n d : ℕ} (xs : List (Fin n)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  if h : xs.length = n + (d + 1) then
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential A (fun i => xs[i.val]'(by omega)) else 0

/-- 概要：有限語をリスト化しても削除和は変わらない（BF §1.4.4）。
方針：ofFn の長さと各文字の評価を使う。
規約：語の全射性や非退化性を要求しない。
使われ方：リストの計算と有限語の符号の補題を接続する。 -/
@[simp] lemma rawListDifferential_ofFn {n d : ℕ} (v : Fin (n + (d + 1)) → Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawListDifferential A (List.ofFn v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential A v := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawListDifferential
  simp only [List.length_ofFn, ↓reduceDIte]
  apply congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential A (n := n) (d := d))
  funext i
  simp only [List.getElem_ofFn, Fin.eta]

/-- 概要：リストの生成元の微分はリストの削除和（BF §1.4.4）。
方針：長さの検査の各分岐で任意の語の正規化との両立を使う。
規約：無効な長さでは両辺とも零。
使われ方：TR の全ての table 項の微分を一つの式で展開する。 -/
lemma differential_listGenerator {n d : ℕ} (xs : List (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (d := d + 1) xs) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawListDifferential A xs := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawListDifferential
  split
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential_generator A _
  · exact map_zero _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
