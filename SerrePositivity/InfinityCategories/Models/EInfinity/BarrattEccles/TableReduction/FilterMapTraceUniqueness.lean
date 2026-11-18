module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapPrefixInjectivity
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapTrace

/-!
模型。文献の定義との比較は後で
# 射影選択行から元の全成功出力を復元する

概要：Berger–Fresse §1.5.7–9 の空語合成で元の成功項の一意性に使う抽出比較を証明する。
方針：非最終行長は保持される末尾、最終行長は全出力長で揃える。
規約：元の逆行列と初期状態は同じ。選択長は初めから同じと仮定しない。
使われ方：指定値削除が同じ成功項の元の語を一意に復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α β : Type*} [DecidableEq α]

/-- 概要：同じ行列・全長・射影選択行を持つ保持条件付き成功出力は一致（BF §1.5.7–9）。
方針：各非最終行の末尾から行長を戻し、同じ除外状態で後続を比較する。
規約：最後の末尾は射影から消えてよい。
使われ方：nullary 順方向写像の単射性に必要な元の成功語の一意性。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace.eq_of_filterMap {rows : List (List α × ℕ)}
    {removed : List α} {picked : List (List α)} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows removed picked)
    (f : α → Option β) (hf : ∀ a a' b, f a = some b → f a' = some b → a = a') :
    (∀ p ∈ rows, p.1.Nodup) → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapReady f picked →
    ∀ (rows' : List (List α × ℕ)) (picked' : List (List α))
      (_h' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows' removed picked'),
      rows.map Prod.fst = rows'.map Prod.fst →
      picked.map (List.filterMap f) = picked'.map (List.filterMap f) →
      picked.flatten.length = picked'.flatten.length → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapReady f picked' →
      picked = picked' := by
  induction h with
  | nil =>
    intro _ _ rows' picked' h' hm _ _ _
    cases h' with
    | nil => rfl
    | cons => simp at hm
  | @cons row r rest removed picked hr hb ht ih =>
    intro hn hleft rows' picked' h' hm hp hl hright
    cases h' with
    | nil => simp at hm
    | @cons row' r' rest' _ tail' hr' hb' ht' =>
      have hmatrix := List.cons.inj hm
      have hrow : row = row' := hmatrix.1
      subst row'
      have hproj := List.cons.inj hp
      have htailLen : picked.length = tail'.length := by
        simpa only [List.length_map] using congrArg List.length hproj.2
      by_cases he : picked = []
      · subst picked
        have he' : tail' = [] := List.length_eq_zero_iff.mp (by simpa using htailLen.symm)
        subst tail'
        have hrs : r = r' := by
          simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_take,
            Nat.min_eq_left hb, Nat.min_eq_left hb'] using hl
        rw [hrs]
      · have he' : tail' ≠ [] := by
          intro hh
          rw [hh, List.length_nil] at htailLen
          exact he (List.length_eq_zero_iff.mp htailLen)
        have hrs : r = r' := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.take_length_eq_of_filterMap_eq f hf (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row)
          ((hn (row, r) List.mem_cons_self).filter _) r r' hr hr' hb hb' hproj.1
          (hleft.2.1 he) (hright.2.1 he')
        subst r'
        have htailSize : picked.flatten.length = tail'.flatten.length := by
          simp only [List.flatten_cons, List.length_append] at hl
          exact Nat.add_left_cancel hl
        have heq := ih (fun p hp => hn p (List.mem_cons_of_mem _ hp)) hleft.2.2 rest' tail'
          ht' hmatrix.2 hproj.2 htailSize hright.2.2
        exact congrArg (List.cons _) heq

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
