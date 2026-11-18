module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceRowRanges

/-!
模型。文献の定義との比較は後で
# 出現境界で切る外側成分の実際の抽出

概要：Berger–Fresse §1.5.7 の各水平成分を元の成功表の閉区間として取り出す。
方針：既存の出現境界の有限位置と単調性を任意の区間抽出に適用する。
規約：最初と最後の成分も同じ式で扱い、両端を含める。
使われ方：内側成分の間の外側の進行を元の連続行から構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：指定値の出現で切る一つの外側部分語（BF §1.5.7）。
方針：前後の出現境界の閉区間を元の語から切り出す。
規約：出現境界の文字は両側の成分に含める。
使われ方：元の水平成分の選択語。 -/
def outerComponentWord {n l : ℕ} (v : Fin l → Fin n) (k : Fin n) (i : ℕ) : List (Fin n) :=
  ((List.ofFn v).drop (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary v k i)).take
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary v k (i + 1) - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary v k i + 1)

/-- 概要：元の外側成功表の一つの出現成分の抽出証明書（BF §1.5.7）。
方針：出現境界の二つの有限位置の間の区間を構成する。
規約：語長は正。次数零の成分も一行で抽出する。
使われ方：候補経路の水平成分の実際の元の行と除外状態。 -/
noncomputable def outerComponentExtraction {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val)) (k : Fin n)
    (hl : 0 < n + d) (i : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval w s v.val h (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition v.val k hl i)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition v.val k hl (i + 1)) :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionInterval_nonempty w s v.val h _ _
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition_mono v.val k hl (by omega)))

/-- 概要：外側成分の選択語は実際の出現境界間の部分語（BF §1.5.7）。
方針：有限境界の値を元の自然数境界へ戻す。
規約：共有境界文字を含める。
使われ方：水平成分の語を元の外側合成語へ照合する。 -/
lemma outerComponentExtraction_word {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val)) (k : Fin n)
    (hl : 0 < n + d) (i : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction w s v h k hl i).selected.flatten = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentWord v.val k i :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction w s v h k hl i).word

/-- 概要：外側成分の行数は水平成分次数＋1（BF §1.5.7）。
方針：元の閉区間の行数を成分次数の境界差へ照合する。
規約：最初・最後の零次数成分も含む。
使われ方：実際の行の進行を候補経路の水平辺数へ対応させる。 -/
lemma outerComponentExtraction_length {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val)) (k : Fin n)
    (hl : 0 < n + d) (i : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction w s v h k hl i).part.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree v.val k i + 1 :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction w s v h k hl i).length

/-- 概要：元の外側成分は追加の成功仮定なしに実際に抽出される（BF §1.5.7）。
方針：元の区間証跡の後続を空にして、選択語を照合する。
規約：始状態は元の出現境界の進行状態。
使われ方：水平成分を合成抽出へ転送する入力。 -/
lemma outerComponentExtraction_success {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val)) (k : Fin n)
    (hl : 0 < n + d) (i : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction w s v h k hl i).part
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w s v.val h (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition v.val k hl i)) =
        some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentWord v.val k i) := by
  have hs := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction w s v h k hl i).trace.append [] [] rfl
  simpa only [List.append_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction_word] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
