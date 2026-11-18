module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalRowSteps
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowBoundary

/-!
模型。文献の定義との比較は後で
# 最終出現区間を通過した除外リストの更新

概要：Berger–Fresse §1.4.3 の table の先行行の正しい除外リストを追跡する。
方針：最終出現の各文字を前半へ追加する式を区間で反復する。
規約：区間は左端を含み右端を除く。
使われ方：標準頂点の行を除外した後の形と、正しい抽出後の状態を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：最終出現だけの区間は順に確定した前半へ加わる（BF §1.4.3）。
方針：終点で帰納し、各文字の前半への末尾追加を take の末尾追加と比較する。
規約：空の区間では空リストを加える。
使われ方：行内で処理する文字列を除外リストの差として同定する。 -/
lemma pastFinals_eq_append_segment (xs : List α) (p q : ℕ) (hpq : p ≤ q)
    (hq : q ≤ xs.length)
    (h : ∀ (k : ℕ) (hk : k < xs.length), p ≤ k → k < q →
      xs[k] ∉ xs.drop (k + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals xs q = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals xs p ++ (xs.drop p).take (q - p) := by
  induction q with
  | zero =>
    have hp : p = 0 := by omega
    subst p
    simp
  | succ q ih =>
    by_cases hp : p = q + 1
    · subst p
      simp
    · have hpq' : p ≤ q := by omega
      have hq' : q < xs.length := by omega
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals_succ xs q hq', ite_eq_right (h q hq' hpq' (by omega)),
        ih hpq' (by omega) (fun k hk hpk hkq => h k hk hpk (by omega))]
      have hk : q - p < (xs.drop p).length := by rw [List.length_drop]; omega
      have ht := List.take_concat_get' (xs.drop p) (q - p) hk
      rw [List.getElem_drop] at ht
      have hs : p + (q - p) = q := by omega
      simp only [hs] at ht
      have hd : q + 1 - p = (q - p) + 1 := by omega
      rw [hd, ← ht]
      simp only [List.append_assoc]

/-- 概要：重複しない行から既知の先頭全体を除けば後半だけが残る（BF §1.4.3）。
方針：先頭は全て除外し、重複がないので後半は一文字も除かれない。
規約：先頭と後半のどちらも空でよい。
使われ方：標準行から先行行で確定した値を除く。 -/
lemma available_prefix_of_nodup (pre rest : List α) (hn : (pre ++ rest).Nodup) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available pre (pre ++ rest) = rest := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_append]
  have hp : pre.filter (fun x => x ∉ pre) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp [hx]
  rw [hp, List.nil_append]
  apply List.filter_eq_self.mpr
  intro x hx
  have hnot : x ∉ pre := by
    intro hpre
    exact (List.nodup_append.mp hn).2.2 x hpre x hx rfl
  simpa only [decide_eq_true_eq] using hnot

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
