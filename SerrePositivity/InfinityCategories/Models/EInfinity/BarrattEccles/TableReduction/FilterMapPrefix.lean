module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapAvailable
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapSelection

/-!
模型。文献の定義との比較は後で
# 抽出の先行部分と終状態を保つ部分射影

概要：Berger–Fresse §1.5.8 の内側射影を実際の有限抽出証跡へ移す。
方針：選択末尾を残す部分単射で各行・選択語・除外状態を同時に射影する。
規約：射影行長は実際の選択語の射影長。元の表の末尾以外の除外規約を保つ。
使われ方：合成表の垂直成分から元の内側表の成功抽出を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α β : Type*}

/-- 概要：選択語から射影後の各行長を定めた実際の射影表（BF §1.5.8）。
方針：元の行と選択語を zipWith し、行を射影・行長を選択語の射影長とする。
規約：証跡を使う場合、二つのリストの長さは自動的に一致する。
使われ方：射影表の抽出成功を元の成功から導く。 -/
def filterMapRows (f : α → Option β) (rows : List (List α × ℕ))
    (picked : List (List α)) : List (List β × ℕ) :=
  List.zipWith (fun row word => (row.1.filterMap f, (word.filterMap f).length)) rows picked

/-- 概要：同じ行数の射影表は元の全行を一度ずつ射影した行列（BF §1.5.8）。
方針：二つのリストで同時に帰納し、zipWith の切り詰めが起こらないと示す。
規約：選択語の行数は元の行数に等しい。
使われ方：復元表の行が実際の元の内側置換列であることを確認する。 -/
lemma filterMapRows_fst (f : α → Option β) (rows : List (List α × ℕ))
    (picked : List (List α)) (hl : rows.length = picked.length) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows f rows picked).map Prod.fst = rows.map (fun row => row.1.filterMap f) := by
  induction rows generalizing picked with
  | nil => cases picked <;> simp_all [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows]
  | cons row rows ih =>
    cases picked with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons word picked =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows, List.zipWith_cons_cons, List.map_cons]
      exact congrArg ((row.1.filterMap f) :: ·) (ih picked hl)

variable [DecidableEq α] [DecidableEq β]

/-- 概要：末尾を残す部分単射は有限抽出とその終状態を保つ（BF §1.5.8）。
方針：証跡で帰納し、可用行・選択先頭部分・末尾以外の除外を同時に照合する。
規約：各選択行の実際の末尾に射影値があることを要求する。
使われ方：内側末尾を持つ合成表の垂直先行部分を元の内側抽出へ戻す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.filterMap {rows : List (List α × ℕ)}
    {removed finish : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix rows removed picked finish) (f : α → Option β)
    (hf : ∀ a a' b, f a = some b → f a' = some b → a = a')
    (he : ∀ word ∈ picked, ∃ a b, word.getLast? = some a ∧ f a = some b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows f rows picked) (removed.filterMap f)
      (picked.map (List.filterMap f)) (finish.filterMap f) := by
  induction h with
  | nil => exact .nil _
  | @cons row r rest removed picked finish hr hb ht ih =>
    have hlast := he _ List.mem_cons_self
    obtain ⟨hr', hb', hu⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_selection_retained_last f
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row) r hr hb hlast
    have hav := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_filterMap f hf removed row
    have hpick : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f)).take
        (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f).length =
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f := by
      rw [hav, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_take_prefix]
    have hstate : (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)).filterMap f =
        removed.filterMap f ++
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f)).take
            ((((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f).length - 1) := by
      rw [List.filterMap_append, hav, hu]
    have htail := ih (fun word hw => he word (List.mem_cons_of_mem _ hw))
    rw [hstate] at htail
    have hbound : (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f).length ≤
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f)).length := by
      rw [hav]
      exact hb'
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows, List.zipWith_cons_cons, List.map_cons, hpick] using
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.cons hr' hbound htail

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
