module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowDedupBudget

/-!
模型。文献の定義との比較は後で
# 長さの等式による非最終行末の再出現

概要：Berger–Fresse §1.4.4 の成功した table の各非最終行末が後でも現れることを示す。
方針：一つでも再出現しない行末があれば重複除去の損失が行数−1 より小さくなる。
規約：出力に隣接重複があってもよい。
使われ方：table の区切りがちょうど非最終行末であることを導く。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：最後以外の各行末の文字が後続行にも現れる（BF §1.4.4）。
方針：先頭行末の条件と後続の同じ条件を再帰的にまとめる。
規約：最終行には再出現を要求しない。
使われ方：各行末を区切りの位置と同定する。 -/
def RecurrentEnds : List (List α) → Prop
  | [] => True
  | row :: rest => (∀ hr : row ≠ [], rest ≠ [] → row.getLast hr ∈ rest.flatten) ∧
      RecurrentEnds rest

/-- 概要：損失が行数−1 と一致すれば全非最終行末は再出現する（BF §1.4.4）。
方針：再出現しない行末は損失を一つ減らすことを長さの式で排除する。
規約：全行が非空で分離条件を満たす。
使われ方：有限な値集合で実際の table の再出現を強制する。 -/
lemma recurrentEnds_of_saturated (picked : List (List α)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows picked →
    (∀ row ∈ picked, row ≠ []) →
    picked.flatten.length = picked.flatten.dedup.length + (picked.length - 1) →
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked := by
  induction picked with
  | nil => intro _ _ _; trivial
  | cons row rest ih =>
    intro hs hne hsat
    have hr := hne row (List.mem_cons_self ..)
    have hpos : 0 < row.length := List.length_pos_iff.mpr hr
    have hnrest : ∀ r ∈ rest, r ≠ [] := fun r hm => hne r (List.mem_cons_of_mem _ hm)
    have hb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.separatedRows_length_le rest hs.2.2 hnrest
    have hhead : ∀ hr : row ≠ [], rest ≠ [] → row.getLast hr ∈ rest.flatten := by
      intro hr hrest
      by_contra ha
      have hd := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.dedup_length_prepend_row row rest.flatten hr hs.1 hs.2.1
      simp only [ha, ↓reduceIte] at hd
      have hl : 0 < rest.length := List.length_pos_iff.mpr hrest
      simp only [List.flatten_cons, List.length_append, List.length_cons] at hsat
      omega
    refine ⟨hhead, ?_⟩
    by_cases hrest : rest = []
    · subst rest
      trivial
    · apply ih hs.2.2 hnrest
      have hd := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.dedup_length_prepend_row row rest.flatten hr hs.1 hs.2.1
      simp only [hhead hr hrest, ↓reduceIte, Nat.add_zero] at hd
      have hl : 0 < rest.length := List.length_pos_iff.mpr hrest
      simp only [List.flatten_cons, List.length_append, List.length_cons] at hsat
      omega

/-- 概要：Fin n の語の重複除去後の長さは n 以下（BF §1.4.4）。
方針：重複除去後の位置から値への単射を有限濃度で評価する。
規約：元の語の全射性を仮定しない。
使われ方：出力の長さで損失が最大となることを示す。 -/
lemma dedup_length_le_arity {n : ℕ} (xs : List (Fin n)) : xs.dedup.length ≤ n := by
  have hi := List.nodup_iff_injective_get.mp (List.nodup_dedup xs)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective xs.dedup.get hi

/-- 概要：長さ n+行数−1 の分離した行では全ての非最終行末が再出現（BF §1.4.4）。
方針：重複除去後の長さ n 以下と損失の上界を合わせ、等号を強制する。
規約：各行の値は Fin n。
使われ方：成功した TR の行の分割に適用する。 -/
lemma recurrentEnds_of_length {n : ℕ} (picked : List (List (Fin n)))
    (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows picked) (hne : ∀ row ∈ picked, row ≠ [])
    (hlen : picked.flatten.length = n + (picked.length - 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked := by
  have hb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.separatedRows_length_le picked hs hne
  have hd := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.dedup_length_le_arity picked.flatten
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentEnds_of_saturated picked hs hne
  omega

/-- 概要：成功した TR 出力は行内部が最終出現で非最終行末が再出現する（BF §1.4.4）。
方針：実際の抽出証跡と出力長 n+d を行数 d+1 と合わせる。
規約：Schedule の抽出に成功した全ての項で成立する。
使われ方：table の区切り・削除位置・符号の対応を構成する。 -/
lemma recurrentEnds_of_reduction {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    ∃ picked, picked.flatten = out ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows picked ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked ∧
      (∀ row ∈ picked, row ≠ []) ∧ picked.length = d + 1 ∧
      picked.map List.length = List.ofFn (fun i => (r.val i).val) := by
  obtain ⟨picked, he, hs, hn, hl, hlengths⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.separatedRows_of_reduction w r out h
  refine ⟨picked, he, hs, ?_, hn, hl, hlengths⟩
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentEnds_of_length picked hs hn
  rw [he, hl, Nat.add_sub_cancel]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
