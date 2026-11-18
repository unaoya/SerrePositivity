module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceSuffixes

/-!
模型。文献の定義との比較は後で
# リストの再出現位置の列

概要：Berger–Fresse §1.2.2・§1.4.4 の区切り位置をリストの自然数添字で列挙する。
方針：先頭の値が尾部にあるかを判定し、尾部の位置に 1 を加える。
規約：列は元の語の位置の順。最終出現の位置は含めない。
使われ方：table の非最終行末の列と有限語の Caesura を同定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {α : Type*} [DecidableEq α]

/-- 概要：後でも同じ値が現れる位置の列（BF §1.2.2）。
方針：語の先頭から位置を再帰的に列挙する。
規約：自然数添字を零から数える。
使われ方：行の連結に沿って区切り位置を計算する。 -/
def repeatPositions : List α → List ℕ
  | [] => []
  | a :: xs => if a ∈ xs then 0 :: (repeatPositions xs).map Nat.succ
      else (repeatPositions xs).map Nat.succ

/-- 概要：再出現位置への所属は尾部への同値の所属（BF §1.2.2）。
方針：語と位置で帰納し、先頭と後続の添字を比較する。
規約：有効な位置の存在も同時に指定する。
使われ方：リストの位置の列を有限語の区切り条件へ渡す。 -/
lemma mem_repeatPositions (xs : List α) (k : ℕ) :
    k ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions xs ↔ ∃ hk : k < xs.length, xs[k] ∈ xs.drop (k + 1) := by
  induction xs generalizing k with
  | nil => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions]
  | cons a xs ih =>
    cases k with
    | zero =>
      by_cases ha : a ∈ xs <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions, ha]
    | succ k =>
      by_cases ha : a ∈ xs <;>
        simpa [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions, ha, List.mem_map] using ih k

/-- 概要：最終出現だけの先頭部分は区切り位置をずらすだけ（BF §1.4.4）。
方針：先頭部分を帰納し、重複のなさと後続との分離で各先頭を除く。
規約：先頭部分と後続の値は互いに素。
使われ方：一行の内部を通過して末尾だけを区切り候補として残す。 -/
lemma repeatPositions_fresh_prepend (pre tail : List α) (hn : pre.Nodup)
    (hf : ∀ a ∈ pre, a ∉ tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions (pre ++ tail) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions tail).map (fun k => pre.length + k) := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    have hnot : a ∉ pre ++ tail := by
      intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact (List.nodup_cons.mp hn).1 hm
      · exact hf a (by simp) hm
    rw [List.cons_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions, ite_eq_right hnot,
      ih (List.nodup_cons.mp hn).2 (fun a ha => hf a (List.mem_cons_of_mem _ ha))]
    simp only [List.map_map, List.length_cons]
    congr 1
    funext k
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    omega

/-- 概要：重複しない語には再出現位置がない（BF §1.2.2）。
方針：空の後続語の前に置く場合として前置の式を使う。
規約：空語も含む。
使われ方：table の最後の行の区切りが空であることを示す。 -/
lemma repeatPositions_eq_nil_of_nodup (xs : List α) (hn : xs.Nodup) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions xs = [] := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions_fresh_prepend xs [] hn (by simp)
  simpa only [List.append_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions, List.map_nil] using h

/-- 概要：有限語の区切りはリストの再出現位置に一致（BF §1.2.2）。
方針：尾部の所属による二つの特徴づけを合わせる。
規約：全射性と非退化性は不要。
使われ方：table の行末と削除係数の区切り順位を接続する。 -/
lemma caesura_iff_mem_repeatPositions {n l : ℕ} (v : Fin l → Fin n) (i : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i ↔ i.val ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions (List.ofFn v) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_repeatPositions]
  constructor
  · intro hi
    refine ⟨by simpa only [List.length_ofFn] using i.isLt, ?_⟩
    simpa only [List.getElem_ofFn, Fin.eta] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_drop v i).mp hi
  · rintro ⟨_, hi⟩
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_drop v i).mpr
    simpa only [List.getElem_ofFn, Fin.eta] using hi

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
