module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalRowSteps
public import Mathlib.Data.List.Chain

/-!
模型。文献の定義との比較は後で
# 復元行の一文字の移動と最終出現区間の不変性

概要：Berger–Fresse §1.4.2–3 の標準頂点列の隣接行の形を構成する。
方針：後続の最初の出現列を移動する文字の位置で分割する。
規約：移動する文字以外の相対順序は保ち、最終出現だけの区間では行を保つ。
使われ方：指定外の table 境界が隣接重複を作ることを証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {α : Type*} [DecidableEq α]

/-- 概要：再出現する文字の通過は一文字の後方への移動（BF §1.4.2–3）。
方針：後半を文字の唯一の出現で二分し、前の行ではそれを先頭へ出す。
規約：left と right には移動する文字が現れない。
使われ方：隣接する復元行を具体的な二つのリスト式で比較する。 -/
lemma canonicalRow_exists_move (xs : List α) (p : ℕ) (hp : p < xs.length)
    (ha : xs[p] ∈ xs.drop (p + 1)) :
    ∃ pre left right : List α,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs p = pre ++ [xs[p]] ++ left ++ right ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs (p + 1) = pre ++ left ++ [xs[p]] ++ right ∧
      xs[p] ∉ left ∧ xs[p] ∉ right := by
  have hm : xs[p] ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences (xs.drop (p + 1)) :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_firstOccurrences _ _).mpr ha
  obtain ⟨left, right, he⟩ := List.append_of_mem hm
  have hn : (left ++ xs[p] :: right).Nodup := by
    rw [← he]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences_nodup _
  have hleft : xs[p] ∉ left := by
    intro h
    exact (List.nodup_append.mp hn).2.2 _ h _ (by simp) rfl
  have hright : xs[p] ∉ right := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  have hfilter (ys : List α) (hy : xs[p] ∉ ys) :
      ys.filter (fun b => b ≠ xs[p]) = ys := by
    apply List.filter_eq_self.mpr
    intro b hb
    have hb' : b ≠ xs[p] := fun h => hy (h ▸ hb)
    simpa only [decide_eq_true_eq] using hb'
  refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals xs p, left, right, ?_, ?_, hleft, hright⟩
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_before_step xs p hp, he]
    simp only [List.filter_append, List.filter_cons, ne_eq, not_true_eq_false,
      decide_false, Bool.false_eq_true, ↓reduceIte, hfilter left hleft, hfilter right hright,
      List.append_assoc, List.cons_append, List.nil_append]
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_after_step_of_mem xs p hp ha, he]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- 概要：非退化な語の区切りで復元行は実際に変わる（BF §1.4.2–3）。
方針：前半を消去して後半の先頭を比較し、元の語の隣接非一致に反する。
規約：再出現する文字は直後の文字とは異なる。
使われ方：復元した BE 単体の隣接頂点が異なることを示す。 -/
lemma canonicalRow_ne_succ_of_mem (xs : List α) (p : ℕ) (hp : p < xs.length)
    (hxs : xs.IsChain (· ≠ ·)) (ha : xs[p] ∈ xs.drop (p + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs p ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs (p + 1) := by
  obtain ⟨k, hk, _⟩ := List.mem_drop_iff_getElem.mp ha
  have hp' : p + 1 < xs.length := by omega
  intro he
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_before_step xs p hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_after_step_of_mem xs p hp ha] at he
  have ht := List.append_cancel_left he
  have hh := congrArg List.head? ht
  rw [List.drop_eq_getElem_cons hp', _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences_cons] at hh
  simp only [List.head?_cons, Option.some.injEq] at hh
  exact (List.isChain_iff_getElem.mp hxs p hp') hh

/-- 概要：最終出現だけを通過する区間で復元行は不変（BF §1.4.2）。
方針：終点で帰納し、一文字の最終出現の不変性を反復する。
規約：区間は左端を含み、右端を含まない。
使われ方：一つの table 行の開始位置から区切り位置まで行を保つ。 -/
lemma canonicalRow_eq_of_final_interval (xs : List α) (p q : ℕ)
    (hpq : p ≤ q) (hq : q ≤ xs.length)
    (h : ∀ (k : ℕ) (hk : k < xs.length), p ≤ k → k < q →
      xs[k] ∉ xs.drop (k + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs q = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs p := by
  induction q with
  | zero =>
    have hp : p = 0 := by omega
    subst p
    rfl
  | succ q ih =>
    by_cases hp : p = q + 1
    · subst p
      rfl
    · have hpq' : p ≤ q := by omega
      have hq' : q < xs.length := by omega
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_succ_of_not_mem xs q hq' (h q hq' hpq' (by omega))]
      exact ih hpq' (by omega) (fun k hk hpk hkq => h k hk hpk (by omega))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
