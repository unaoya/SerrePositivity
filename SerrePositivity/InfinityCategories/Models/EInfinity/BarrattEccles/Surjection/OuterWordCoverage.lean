module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapseMembership
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OuterTraceNondegenerate
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.OutputCoverage

/-!
模型。文献の定義との比較は後で
# 外側復元語の全射性と行末の再出現

概要：Berger–Fresse §1.5.8 の外側復元へ全ラベルの出現と非最終行末の再出現を移す。
方針：外側射影の全射性と縮約の所属・末尾保存を使う。
規約：全射性では内側 arity を正とし、行末の再出現の保存自体は零 arity も含む。
使われ方：復元外側表の行長総和を元の arity と次数に一致させる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：外側復元語の所属は射影前の同じ値の出現と一致（BF §1.5.8）。
方針：縮約の所属保存と map の所属公式を使う。
規約：全ての文字が同じ場合も一つの出現は残る。
使われ方：元の合成語から値の存在を外側復元語へ移す。 -/
lemma mem_outerWord {m n : ℕ} (k : Fin (m + 1)) (a : Fin (m + 1))
    (xs : List (Fin (m + n))) :
    a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k xs ↔ ∃ b ∈ xs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k b = a := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.mem_collapse, List.mem_map]

/-- 概要：正の内側 arity では外側射影は全射（BF §1.5.8）。
方針：指定値は一つの内側ラベルから、他の値は残る外側ラベルから得る。
規約：指定値の原像の選択には内側の第零ラベルを使う。
使われ方：元の合成語が全ラベルを含むことから外側の全射性を得る。 -/
lemma outerLabel_surjective {m n : ℕ} (hn : 0 < n) (k : Fin (m + 1)) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel (n := n) k) := by
  intro a
  by_cases he : a = k
  · subst a
    exact ⟨insertedPosition m n k ⟨0, hn⟩, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_inserted k _⟩
  · exact ⟨remainingPosition m n k ⟨a, he⟩, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_remaining k _⟩

/-- 概要：全射な合成語の外側復元は全ての外側ラベルを含む（BF §1.5.8）。
方針：外側射影の各原像を元の全射性で語に出現させ、縮約後の所属へ移す。
規約：正の内側 arity。語長や非退化性には依存しない。
使われ方：復元する元の外側語の全射性を供給する。 -/
lemma outerWord_covers {m n : ℕ} (hn : 0 < n) (k : Fin (m + 1))
    (xs : List (Fin (m + n))) (h : ∀ b, b ∈ xs) : ∀ a, a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k xs := by
  intro a
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_surjective hn k a
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mem_outerWord k a xs).mpr ⟨b, h b, hb⟩

/-- 概要：行ごとの外側復元の連結と全語の復元は同じ値を含む（BF §1.5.8）。
方針：各行の縮約をまとめた全縮約の一致と所属保存を使う。
規約：行境界で同じ値が重なってもよい。
使われ方：全語の全射性を元の外側抽出の行分割へ移す。 -/
lemma mem_outer_picked {m n : ℕ} (k : Fin (m + 1)) (a : Fin (m + 1))
    (picked : List (List (Fin (m + n)))) :
    a ∈ (picked.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k)).flatten ↔ a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k picked.flatten := by
  calc
    _ ↔ a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (picked.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k)).flatten :=
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.mem_collapse _ _).symm
    _ ↔ _ := by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.collapse_outer_picked]

/-- 概要：非最終行末の後続での再出現は外側復元でも保たれる（BF §1.5.8）。
方針：縮約の末尾保存で行末を外側へ戻し、元の後続出現を所属保存で移す。
規約：内側 arity 零も含み、元の各行の非空性を追加仮定にしない。
使われ方：復元外側表の行長から最終出現の個数を計数する。 -/
lemma recurrentEnds_outerWord {m n : ℕ} (k : Fin (m + 1))
    (picked : List (List (Fin (m + n)))) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds (picked.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k)) := by
  induction picked with
  | nil => trivial
  | cons row rest ih =>
    refine ⟨?_, ih h.2⟩
    intro hnew hrestnew
    have hr : row ≠ [] := by intro he; subst row; exact hnew rfl
    have hrest : rest ≠ [] := by intro he; subst rest; exact hrestnew rfl
    let a := row.getLast hr
    have hm : a ∈ rest.flatten := h.1 hr hrest
    have hl : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k row).getLast? = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k a) := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord_getLast?, List.getLast?_eq_some_getLast hr, Option.map_some]
    have hv : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k row).getLast hnew = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k a :=
      Option.some.inj ((List.getLast?_eq_some_getLast hnew).symm.trans hl)
    rw [hv]
    obtain ⟨word, hw, ha⟩ := List.mem_flatten.mp hm
    exact List.mem_flatten.mpr ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k word, List.mem_map.mpr ⟨word, hw, rfl⟩,
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mem_outerWord k _ word).mpr ⟨a, ha, rfl⟩⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
