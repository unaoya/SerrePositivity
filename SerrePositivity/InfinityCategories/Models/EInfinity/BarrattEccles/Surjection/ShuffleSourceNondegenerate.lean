module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ShuffleOuterRows
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEdges
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SequenceDegeneracy

/-!
模型。文献の定義との比較は後で
# 非退化な成功 shuffle 表から元の内外列を復元

概要：Berger–Fresse §1.5.8 の逆構成で元の置換列の非退化性を成功から導く。
方針：元の隣接重複を実際の水平辺・垂直辺へ持ち上げ、合成出力の退化と矛盾させる。
規約：入力列の非退化性を追加仮定にせず、元の成功と出力の非退化性だけを用いる。
使われ方：元の外側行列・行数を持つ実際の成功表を逆構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
open scoped _root_.Simplicial

/-- 概要：非退化な成功 shuffle 表の元の外側列は隣接非一致（BF §1.5.8）。
方針：重複する元の外側頂点を結ぶ水平辺で合成の二頂点も一致させる。
規約：初期除外は元の TR と同じ空リスト。
使われ方：外側行列の縮約を除き、元の外側次数の行数を得る。 -/
lemma shuffle_outer_isChain_of_success {m n d e : ℕ} (k : Fin (m + 1)) (s : ShufflePath d e)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun i => permutationComposition m n k (outer (s.horizontal i))
      (inner (s.vertical i))) r) [] = some out) (hc : out.IsChain (· ≠ ·)) :
    (List.ofFn outer).IsChain (· ≠ ·) := by
  apply List.isChain_ofFn.mpr
  intro i hi he
  let j : Fin d := ⟨i, by omega⟩
  change outer j.castSucc = outer j.succ at he
  obtain ⟨a, hzero, hsucc, hfixed⟩ := s.horizontal_edge j
  let w := fun b => permutationComposition m n k (outer (s.horizontal b)) (inner (s.vertical b))
  have hw : w a.castSucc = w a.succ := by
    dsimp only [w]
    rw [hzero, hsucc, hfixed, he]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_not_isChain_of_adjacent_eq w a.castSucc a.succ rfl hw r out h hc

/-- 概要：非退化な成功 shuffle 表の元の内側列は隣接非一致（BF §1.5.8）。
方針：重複する元の内側頂点を結ぶ垂直辺で合成の二頂点も一致させる。
規約：零内側 arity も含む。辺があれば合成頂点の退化を検出する。
使われ方：元の内側行数と非退化入力列を逆構成する。 -/
lemma shuffle_inner_isChain_of_success {m n d e : ℕ} (k : Fin (m + 1)) (s : ShufflePath d e)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun i => permutationComposition m n k (outer (s.horizontal i))
      (inner (s.vertical i))) r) [] = some out) (hc : out.IsChain (· ≠ ·)) :
    (List.ofFn inner).IsChain (· ≠ ·) := by
  apply List.isChain_ofFn.mpr
  intro i hi he
  let j : Fin e := ⟨i, by omega⟩
  change inner j.castSucc = inner j.succ at he
  obtain ⟨a, hzero, hsucc, hfixed⟩ := s.vertical_edge j
  let w := fun b => permutationComposition m n k (outer (s.horizontal b)) (inner (s.vertical b))
  have hw : w a.castSucc = w a.succ := by
    dsimp only [w]
    rw [hzero, hsucc, hfixed, he]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_not_isChain_of_adjacent_eq w a.castSucc a.succ rfl hw r out h hc

/-- 概要：実際の成功から元の外側行列・行数と非退化外側語を持つ成功表を復元する（BF §1.5.8）。
方針：経路の隣接条件と元の列の非退化性を成功から導き、全外側復元へ渡す。
規約：正の内側 arity で初期外側除外は空。元の行列・行数以外の Schedule 条件は後続。
使われ方：TR 部分合成保存の逆方向の元の外側表と次数を供給する。 -/
lemma shuffle_outer_recovery_with_rows {m n d e : ℕ} (hn : 0 < n)
    (k : Fin (m + 1)) (s : ShufflePath d e)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun i => permutationComposition m n k (outer (s.horizontal i))
      (inner (s.vertical i))) r) [] = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ picked finish,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r)) [] picked finish ∧
      out = picked.flatten ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r) picked))
        [] = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) ∧ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out).IsChain (· ≠ ·) ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r) picked)).map
        Prod.fst = List.ofFn (fun j => List.ofFn (outer j).symm) ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r) picked)).length =
        d + 1 := by
  obtain ⟨picked, finish, hp, ho, hs, hchain⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_outer_recovery k s outer inner r [] out h hc
  have hne := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_outer_isChain_of_success k s outer inner r out h hc
  refine ⟨picked, finish, hp, ho, ?_, hchain, ?_, ?_⟩
  · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved_nil (m := m) (n := n) k hn] using hs
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_compressed_outer_rows_of_isChain k s outer inner r [] finish picked hp hne
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_compressed_outer_length k s outer inner r [] finish picked hp hne

/-- 概要：既存の実際の shuffle 合成単体から元の外側行列・行数を持つ成功表を得る（BF §1.5.8）。
方針：各頂点の部分合成公式で元の経路表へ戻し、成功からの全外側復元を使う。
規約：正の内側 arity。各頂点の一致や隣接条件を入力に要求しない。
使われ方：既存 Barratt–Eccles 合成の各 TR 成功項を逆構成へ渡す。 -/
lemma shuffleSimplex_outer_recovery {m n d e : ℕ} (hn : 0 < n)
    (k : Fin (m + 1)) (s : ShufflePath d e)
    (x : (simplicial (m + 1)) _⦋d⦌) (y : (simplicial n) _⦋e⦌)
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e)) (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (simplexEquiv (m + n) (d + e)
      (shuffleSimplex m n k s x y)) r) [] = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ table : List (List (Fin (m + 1)) × ℕ),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows table [] = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) ∧
      table.map Prod.fst = List.ofFn (fun j => List.ofFn (simplexEquiv (m + 1) d x j).symm) ∧
      table.length = d + 1 ∧ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out).IsChain (· ≠ ·) := by
  have hw : simplexEquiv (m + n) (d + e) (shuffleSimplex m n k s x y) =
      (fun i => permutationComposition m n k (simplexEquiv (m + 1) d x (s.horizontal i))
        (simplexEquiv n e y (s.vertical i))) := by
    funext i
    exact simplexEquiv_shuffleSimplex m n k s x y i
  rw [hw] at h
  obtain ⟨picked, finish, _, _, hs, hchain, hrows, hlen⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_outer_recovery_with_rows
    hn k s (simplexEquiv (m + 1) d x) (simplexEquiv n e y) r out h hc
  exact ⟨_, hs, hrows, hlen, hchain⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
