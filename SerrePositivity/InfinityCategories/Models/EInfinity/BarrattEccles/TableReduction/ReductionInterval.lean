module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CursorInterval
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionCursor

/-!
模型。文献の定義との比較は後で
# 成功表の任意の閉区間の具体的な抽出

概要：Berger–Fresse §1.5.7 の任意の二つの語位置の間の実際の抽出証明書を構成する。
方針：語から決まる元の行・列・状態へ任意の cursor 間の区間証跡を適用する。
規約：区間の両端を含み、終点の文字を次の状態に残す。
使われ方：内側の重なる分割の各成分を元の連続する置換行から抽出する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：語の指定位置より前の文字を除いた元の進行状態（BF §1.5.7）。
方針：その位置の cursor の元の除外へ現在行の列より前の文字を加える。
規約：指定位置の文字自身は残す。
使われ方：隣接する成分の共有端点で同じ再開状態を使う。 -/
noncomputable def reductionRemoved {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (v : Fin (n + d) → Fin n) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) : List (Fin n) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionCursor w r v h p).removed ++
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionCursor w r v h p).removed
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p))).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionColumn w r v h p).val

/-- 概要：元の成功表の閉区間の語・状態・元の行列の証明書（BF §1.5.7）。
方針：具体的な行と選択語、元の端点の状態を結ぶ先行証跡を保持する。
規約：行数は閉区間が交わる元の行の数。
使われ方：成分次数に対応する元の抽出を合成表の構成へ渡す。 -/
structure ReductionInterval {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : Fin (n + d) → Fin n)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v)) (p q : Fin (n + d)) where
  part : List (List (Fin n) × ℕ)
  selected : List (List (Fin n))
  trace : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix part (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w r v h p) selected (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w r v h q)
  word : selected.flatten = ((List.ofFn v).drop p.val).take (q.val - p.val + 1)
  length : part.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v q.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val + 1
  source : part.map Prod.fst = (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val)).take
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v q.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val + 1)).map Prod.fst

/-- 概要：元の成功表の任意の閉区間の抽出証明書を構成（BF §1.5.7）。
方針：両端の有限行・列と単調性を既存の cursor 間の区間へ渡す。
規約：追加の区間抽出成功仮定は不要。
使われ方：正の長さの分割成分を元の成功だけから取り出す。 -/
lemma reductionInterval_nonempty {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (v : Fin (n + d) → Fin n) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v))
    (p q : Fin (n + d)) (hpq : p ≤ q) : Nonempty (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval w r v h p q) := by
  obtain ⟨part, selected, ht, hw, hl, hs⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cursorInterval_nonempty w r v h
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h q) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow_mono w r v h hpq)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionCursor w r v h p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionCursor w r v h q) p q
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionColumn w r v h p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionColumn w r v h q)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionColumn_position w r v h p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionColumn_position w r v h q) hpq
  exact ⟨⟨part, selected, ht, hw, hl, hs⟩⟩

/-- 概要：閉区間の証明書は元の reduceRows で実際にその部分語を返す（BF §1.5.7）。
方針：区間の先行証跡に空の後続成功を連結し、選択語を元の区間へ照合する。
規約：終状態の指定も元の先行証跡に保持する。
使われ方：分割成分を実際の抽出成功として合成の証明へ渡す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval.success {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {v : Fin (n + d) → Fin n}
    {h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v)} {p q : Fin (n + d)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval w r v h p q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows c.part (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w r v h p) =
      some (((List.ofFn v).drop p.val).take (q.val - p.val + 1)) := by
  have ht := c.trace.append [] [] rfl
  simpa only [List.append_nil, c.word] using ht

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
