module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseOccurrences

/-!
模型。文献の定義との比較は後で
# 逆構成の解放値は元の削除位置の直前値

概要：Berger–Fresse §1.4.4 の逆探索の値を元の成功出力から一意に読む。
方針：逆構成の左語の末尾と先行出力の長さを評価する。
規約：元の出力の非退化性は仮定しない。
使われ方：順方向の削除値と逆方向の解放値を同定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：逆構成の解放値は元の行末の直前にある値（BF §1.4.4）。
方針：短縮行を末尾一文字で分け、連結語の指定位置を評価する。
規約：p は元の成功出力の有限添字。
使われ方：同じ行末から始めた二つの逆探索の値を揃える。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData.released_value {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {out : List (Fin n)} {q : Fin out.length} (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q)
    (p : Fin out.length) (hp : p.val + 1 = q.val) : out[p.val] = b.a := by
  obtain ⟨head, hh⟩ := b.left_end
  have hlength : b.left.length = head.length + 1 := by
    simpa only [List.length_append, List.length_singleton] using congrArg List.length hh
  have he : out = (b.context.picked.flatten ++ head) ++
      b.a :: (b.b :: (b.middle ++ b.right)) := by
    calc
      out = _ := b.source_shape
      _ = _ := by rw [hh]; simp only [List.append_assoc, List.singleton_append]
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.value_at_insert out (b.context.picked.flatten ++ head) _ b.a he p
  simp only [List.length_append]
  have := b.source_position
  omega

/-- 概要：逆構成の挿入点の値は探索した解放値（BF §1.4.4）。
方針：全出力の連結表示と挿入位置の座標を評価する。
規約：挿入点の前の語には同じ値が含まれてよい。
使われ方：順から逆の復元で最終出現位置の一意性を適用する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData.point_value_eq {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {out : List (Fin n)} {q : Fin out.length} (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q) :
    b.new[b.point.val] = b.a := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.value_at_insert b.new ((b.context.picked.flatten ++ b.left) ++ b.middle)
    b.right b.a (by simpa only [List.append_assoc] using b.target_shape) b.point
  simp only [List.length_append]
  have := b.source_position
  have := b.point_value
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
