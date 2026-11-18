module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.AvailableCardinality

/-!
模型。文献の定義との比較は後で
# 全ての値を一度ずつ含む行の列

概要：Berger–Fresse §1.4.4 の逆探索で使う置換行の性質を行リストの切断後も保持する。
方針：行の重複のなさ・長さ・全値の所属と正の選択長を束ねる。
規約：新しいオペラッドや抽出模型ではなく、元の rows の性質。
使われ方：後続行での帰納的な解放値の探索に適用する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：逆探索で使う完全な置換行と正の行長の条件（BF §1.4.4）。
方針：各行の四つの有限的な性質を保持する。
規約：切り取った任意の後続行にも適用できる。
使われ方：解放値が各利用可能行に現れ、その長さを数えられることを保証する。 -/
def CompleteRows {n : ℕ} (rs : List (List (Fin n) × ℕ)) : Prop :=
  ∀ p ∈ rs, p.1.Nodup ∧ p.1.length = n ∧ (∀ a : Fin n, a ∈ p.1) ∧ 0 < p.2

/-- 概要：実際の Schedule の全ての行は逆探索の完全行条件を満たす（BF §1.4.4）。
方針：各行を元の有限列の頂点として取り出す。
規約：行長の正値性は Schedule の条件から得る。
使われ方：一般の table の逆構成へ完全行の探索を適用する。 -/
lemma completeRows_rows {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompleteRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow_nodup w i, List.length_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.mem_vertexRow w i, r.property.1 i⟩

/-- 概要：完全な行の利用可能長と除外長の和は arity（BF §1.4.4）。
方針：除外された部分は除外リストの並べ替えであることを使う。
規約：除外状態には重複がない。
使われ方：探索の最後の行で解放値が延長選択に入ることを導く。 -/
lemma available_complete_length_add {n : ℕ} (row removed : List (Fin n))
    (hr : row.Nodup) (hl : row.length = n) (hc : ∀ a : Fin n, a ∈ row) (hn : removed.Nodup) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length + removed.length = n := by
  have hp : (row.filter (fun x => x ∈ removed)).Perm removed := by
    apply (List.perm_ext_iff_of_nodup (hr.filter _) hn).mpr
    intro a
    simp only [List.mem_filter, hc a, true_and, decide_eq_true_eq]
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_length_add_removed_filter removed row
  rw [hp.length_eq, hl] at hs
  exact hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
