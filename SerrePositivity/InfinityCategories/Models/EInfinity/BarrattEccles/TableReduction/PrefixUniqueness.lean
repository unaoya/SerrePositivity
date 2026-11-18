module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.PrefixSuccess
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearchProperties

/-!
模型。文献の定義との比較は後で
# 指定した先行抽出の一意性と逆探索への接続

概要：Berger–Fresse §1.4.4 の順方向の中間行と逆探索の先行行を比較する。
方針：同じ抽出再帰の証跡を比較し、不出現を保つ各行を探索の skip へ移す。
規約：先行抽出の選択語と終端状態をともに一致させる。
使われ方：順から逆の復元で同じ状態から同じ停止行を探索する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：同じ先行行と初期状態の抽出証跡は一意（BF §1.4.4）。
方針：証跡の同じ一行の再帰を比較する。
規約：選択語も終端の除外リストも厳密に一致する。
使われ方：異なる構成から得た先行状態を同定する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.unique {rows : List (List α × ℕ)} {removed finish : List α}
    {picked : List (List α)} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix rows removed picked finish) :
    ∀ {picked' finish'}, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix rows removed picked' finish' →
      picked = picked' ∧ finish = finish' := by
  induction h with
  | nil => intro picked' finish' h'; cases h'; exact ⟨rfl, rfl⟩
  | cons hr hb ht ih =>
    intro picked' finish' h'
    cases h' with
    | cons hr' hb' ht' =>
      obtain ⟨he, hf⟩ := ih ht'
      exact ⟨congrArg (List.cons _) he, hf⟩

/-- 概要：解放値のない中間抽出は逆探索の通過行になる（BF §1.4.4）。
方針：各選択語の不出現から skip を構成し、停止行の探索へ連結する。
規約：停止行以降の探索は元の中間抽出の終端状態から始める。
使われ方：順方向の中間証跡から逆探索の同じ停止行を構成する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.prepend_releaseSearch {n : ℕ}
    {before rest selectedBefore after : List (List (Fin n) × ℕ)}
    {removed finish stop : List (Fin n)} {picked selected : List (List (Fin n))}
    {chosen : List (Fin n) × ℕ} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked finish)
    (a : Fin n) (ha : a ∉ picked.flatten)
    (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a rest finish selectedBefore selected stop chosen after) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a (before ++ rest) removed (before ++ selectedBefore)
      (picked ++ selected) stop chosen after := by
  induction h with
  | nil => simpa only [List.nil_append] using hs
  | cons hr hb ht ih =>
    simp only [List.flatten_cons, List.mem_append, not_or] at ha
    have hx := ha.1
    have hy := ha.2
    exact .skip hr hb hx (ih hy hs)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
