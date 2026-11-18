module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalMoves
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceSuffixes

/-!
模型。文献の定義との比較は後で
# 全射語の区切りでの復元行の非自明な移動

概要：Berger–Fresse §1.4.2–3 の一文字の移動を実際の非退化全射語に適用する。
方針：区切りを尾部の所属に直し、元の非退化性で移動が非自明であると示す。
規約：最終出現だけを通過する区間では行を変えない。
使われ方：標準頂点列の隣接行の移動と、行長選択の一意性を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：全射語の最終出現を通過すると復元行は不変（BF §1.4.2）。
方針：区切りでないことを後続に同値がない条件に直す。
規約：位置自体は語の範囲内にある。
使われ方：同じ table 行の内部で復元行を保つ。 -/
lemma canonicalRow_word_succ_of_not_caesura {n l : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (i : Fin l)
    (hi : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (i.val + 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) i.val := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_succ_of_not_mem _ _ (by simpa only [List.length_ofFn] using i.isLt)
  simpa only [List.getElem_ofFn, Fin.eta] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_drop v.val i).not.mp hi

/-- 概要：区切りのない区間では全射語の復元行は不変（BF §1.4.2）。
方針：各位置の最終出現条件を一般のリストの区間不変性へ渡す。
規約：区間は左端を含み右端を含まない。
使われ方：行の開始位置から次の区切りまで行を保つ。 -/
lemma canonicalRow_word_eq_of_no_caesura {n l : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (p q : ℕ)
    (hpq : p ≤ q) (hq : q ≤ l)
    (h : ∀ i : Fin l, p ≤ i.val → i.val < q → ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) q = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) p := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_eq_of_final_interval _ _ _ hpq
    (by simpa only [List.length_ofFn] using hq)
  intro k hk hpk hkq
  have hk' : k < l := by simpa only [List.length_ofFn] using hk
  have hc := h ⟨k, hk'⟩ hpk hkq
  simpa only [List.getElem_ofFn] using
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_drop v.val ⟨k, hk'⟩).not.mp hc

/-- 概要：非退化全射語の区切りで前後の復元行は異なる（BF §1.4.2–3）。
方針：元の語の隣接非一致と、後続に同値があることを使う。
規約：係数環や非零性の仮定によらない組合せ的な主張。
使われ方：標準 BE 単体の非退化性を直接証明する。 -/
lemma canonicalRow_word_ne_succ_of_caesura {n l : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (i : Fin l)
    (hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) i.val ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (i.val + 1) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_ne_succ_of_mem _ _ (by simpa only [List.length_ofFn] using i.isLt)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.isChain_ofFn_of_nondegenerate v.val v.nondegenerate)
  simpa only [List.getElem_ofFn, Fin.eta] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_drop v.val i).mp hi

/-- 概要：全射語の区切りで復元行は非自明に一文字だけ移動する（BF §1.4.2–3）。
方針：リストの移動の式に語の非退化性を適用し、移動距離零を排除する。
規約：left は空でなく、left・right に移動する値は含まれない。
使われ方：標準頂点列の各遷移を境界選択の一意性に必要な形にする。 -/
lemma canonicalRow_word_exists_move {n l : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (i : Fin l)
    (hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val i) :
    ∃ pre left right : List (Fin n),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) i.val = pre ++ [v.val i] ++ left ++ right ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (i.val + 1) = pre ++ left ++ [v.val i] ++ right ∧
      left ≠ [] ∧ v.val i ∉ left ∧ v.val i ∉ right := by
  have hp : i.val < (List.ofFn v.val).length := by
    simpa only [List.length_ofFn] using i.isLt
  have ha : (List.ofFn v.val)[i.val] ∈ (List.ofFn v.val).drop (i.val + 1) := by
    simpa only [List.getElem_ofFn, Fin.eta] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_drop v.val i).mp hi
  obtain ⟨pre, left, right, hpre, hpost, hleft, hright⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_exists_move _ _ hp ha
  have hne := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_ne_succ_of_mem _ _ hp
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.isChain_ofFn_of_nondegenerate v.val v.nondegenerate) ha
  simp only [List.getElem_ofFn, Fin.eta] at hpre hpost hleft hright
  refine ⟨pre, left, right, hpre, hpost, ?_, hleft, hright⟩
  intro hl
  subst left
  apply hne
  rw [hpre, hpost]
  simp only [List.append_nil]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
