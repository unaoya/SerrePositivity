module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalFilteredRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ForcedBoundary

/-!
模型。文献の定義との比較は後で
# 標準逆像の非退化出力による正しい行長の強制

概要：Berger–Fresse §1.4.3 の標準置換列で各行長が指定されることを証明する。
方針：正しい先行除外の後の二行を一文字の移動の形に直し、一般の強制補題を使う。
規約：最後の行以外の各行を対象とし、出力の非退化性を隣接非一致で指定する。
使われ方：標準 TR の非零項が一つであることを帰納的に証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：重複しない文字列から指定された一文字だけを除く（BF §1.4.3）。
方針：前後の部分に同値がないことを重複のなさから取り出す。
規約：文字自体の前後の順序を保つ。
使われ方：移動前後の二行を同じ前後の部分で表す。 -/
lemma filter_ne_split_of_nodup {α : Type*} [DecidableEq α] (left right : List α) (a : α)
    (hn : (left ++ a :: right).Nodup) :
    (left ++ a :: right).filter (fun x => x ≠ a) = left ++ right := by
  have hl : a ∉ left := by
    intro h
    exact (List.nodup_append.mp hn).2.2 a h a (by simp) rfl
  have hr : a ∉ right := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  have hf (xs : List α) (hx : a ∉ xs) : xs.filter (fun x => x ≠ a) = xs := by
    apply List.filter_eq_self.mpr
    intro x h
    have hxa : x ≠ a := fun he => hx (he ▸ h)
    simpa only [decide_eq_true_eq] using hxa
  simp only [List.filter_append, List.filter_cons, ne_eq, not_true_eq_false,
    decide_false, Bool.false_eq_true, ↓reduceIte, hf left hl, hf right hr]

/-- 概要：標準行の非退化な抽出では行長が cut−start+1（BF §1.4.3）。
方針：正しい除外後の二行に移動文字の唯一の出現の分割を適用する。
規約：先行行は正しく処理された状態 pastFinals から始める。
使われ方：標準逆像の全ての非零 table 項の行長を一つずつ確定する。 -/
lemma canonicalRows_force_length {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d)
    (r s : ℕ) (rest : List (List (Fin n) × ℕ)) (out : List (Fin n))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc), r) ::
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.succ), s) :: rest)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc)) = some out)
    (hc : out.IsChain (· ≠ ·)) :
    r = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc + 1 := by
  have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val < (List.ofFn v.val).length := by
    simpa only [List.length_ofFn] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).isLt
  have hm : v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i) ∈
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences ((List.ofFn v.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val + 1)) :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_firstOccurrences _ _).mpr
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_drop v.val _).mp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt_caesura v i))
  obtain ⟨left, right, he⟩ := List.append_of_mem hm
  have hn : (left ++ v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i) :: right).Nodup := by
    rw [← he]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences_nodup _
  have hrow : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc)) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.finalSegment v i ++ v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i) :: (left ++ right) := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_canonicalRow_start, List.drop_eq_getElem_cons hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences_cons]
    simp only [List.getElem_ofFn, Fin.eta]
    rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filter_ne_split_of_nodup left right _ hn]
  have hnext : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.succ)) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.finalSegment v i ++ left ++ v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i) :: right := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_canonicalRow_next, he, List.append_assoc]
  have hnodup := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_nodup (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc)).filter
    (fun x => x ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc))
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available _ _).Nodup at hnodup
  rw [hrow] at hnodup
  have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_forces_move_length _ _ _ _ _ _ _ hrow hnext hnodup r s rest out h hc
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.finalSegment_length] using hr

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
