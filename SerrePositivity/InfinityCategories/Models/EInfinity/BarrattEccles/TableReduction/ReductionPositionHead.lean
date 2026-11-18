module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowCursorRemainder

/-!
模型。文献の定義との比較は後で
# 元の指定位置まで進めた行の先頭と未除外性

概要：Berger–Fresse §1.5.7 の元の語の任意位置で現在行がその文字から再開することを示す。
方針：行内前半の除外による drop と元の行内値の一致を使う。
規約：任意の arity。位置が存在しない空語の場合も追加仮定を置かない。
使われ方：水平転送の固定内側の先頭条件と外側終点の未除外性を供給する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：元の位置まで進めた利用可能行の先頭はその位置の文字（BF §1.5.7）。
方針：元の列番号より前を drop し、その列の値を元の語へ移す。
規約：その位置が行末でも成立する。
使われ方：元の内側の成功から固定水平転送の先頭文字を得る。 -/
lemma reductionRemoved_available_head {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (v : Fin (n + d) → Fin n) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) :
    ∃ ys, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w r v h p)
      (List.ofFn (w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p)).symm) = v p :: ys := by
  let c := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionCursor w r v h p
  let j := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionColumn w r v h p
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p))).drop (j.val + 1), ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (c.removed ++
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p))).take j.val)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p)) = _
  have hb : j.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p))).length := by
    have := c.bound; have := j.isLt; omega
  rw [c.available_remainder j, List.drop_eq_getElem_cons hb,
    ← c.value p j (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionColumn_position w r v h p)]

/-- 概要：元の指定位置の文字はその位置の進行状態でまだ除外されていない（BF §1.5.7）。
方針：利用可能行の先頭の filter 条件を使う。
規約：行内部前半の除外後の状態について述べる。
使われ方：水平成分の終点の指定値が未除外という条件を元の成功から得る。 -/
lemma reductionRemoved_not_mem {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (v : Fin (n + d) → Fin n) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) : v p ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w r v h p := by
  obtain ⟨ys, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved_available_head w r v h p
  have hm : v p ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w r v h p)
      (List.ofFn (w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p)).symm) := by rw [he]; simp
  exact of_decide_eq_true (List.mem_filter.mp hm).2

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
