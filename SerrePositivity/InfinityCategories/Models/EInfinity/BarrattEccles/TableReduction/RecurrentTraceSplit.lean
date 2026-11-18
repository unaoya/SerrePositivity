module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalSingleton
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix

/-!
模型。文献の定義との比較は後で
# 抽出区間での行末再出現条件の制限

概要：Berger–Fresse §1.5.8 の内側逆構成で元の行末再出現を各実際の区間へ渡す。
方針：先行証跡と後続証跡を接続し、行ごとの再出現条件を後続へ制限する。
規約：任意の初期除外と実際の選択語列。出力の非退化性は不要。
使われ方：水平区間の最後の行末が次の復元内側語にも現れることを導く。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：先行抽出と後続の全抽出を実際の一つの証跡へ接続する（BF §1.5.8）。
方針：先行証跡で帰納し、同じ行長と更新を後続へ戻す。
規約：終端の除外状態は厳密に共有する。
使われ方：元の全行末の再出現条件を後続の抽出へ制限する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.trace_append {before rest : List (List α × ℕ)}
    {removed middle : List α} {picked selected : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked middle)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rest middle selected) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (before ++ rest) removed (picked ++ selected) := by
  induction h with
  | nil => exact ht
  | cons hr hb hp ih => exact .cons hr hb (ih ht)

/-- 概要：全証跡の行末再出現は実際の先行抽出後にも成り立つ（BF §1.5.8）。
方針：先行部を戻した全証跡の再出現条件から後続だけを取る。
規約：後続の選択語を固定せず、全ての実際の証跡を扱う。
使われ方：内側復元の各水平区間の入口で帰納条件を保つ。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.recurrent_tail {before rest : List (List α × ℕ)}
    {removed middle : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked middle)
    (hr : ∀ selected, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (before ++ rest) removed selected → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds selected) :
    ∀ selected, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rest middle selected → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds selected := by
  intro selected ht
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds.append_right picked selected (hr _ (h.trace_append ht))

omit [DecidableEq α] in
/-- 概要：再出現条件を持つ非最終行の指定末尾は後続出力に属する（BF §1.5.8）。
方針：Option で指定した末尾を getLast に移して再出現条件の先頭を使う。
規約：後続の選択行列は非空。
使われ方：実際の垂直直前の内側文字の再出現を取り出す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds.getLast?_mem {row : List α} {rest : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds (row :: rest)) (hne : rest ≠ []) (a : α)
    (ha : row.getLast? = some a) : a ∈ rest.flatten := by
  have hr : row ≠ [] := by intro he; simp only [he, List.getLast?_nil, reduceCtorEq] at ha
  have he : row.getLast hr = a := by
    rw [List.getLast?_eq_some_getLast hr] at ha
    exact Option.some.inj ha
  exact he ▸ h.1 hr hne

/-- 概要：本来の Schedule の任意の実際の抽出証跡は全行末再出現を持つ（BF §1.5.8）。
方針：成功語長 n+d と実際の行数 d+1 を分離行の飽和条件へ渡す。
規約：元の出力の非退化性を要求しない。
使われ方：shuffle 合成 Schedule の行末再出現を内側逆構成の入口へ供給する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace.recurrent_of_schedule {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    {picked : List (List (Fin n))} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] picked) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentEnds_of_length picked (h.separatedRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_nodup w r)) h.nonempty
  have hl : picked.length = d + 1 := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn] using h.length
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r picked.flatten h.reduceRows, hl, Nat.add_sub_cancel]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
