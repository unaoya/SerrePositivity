module

public import SerrePositivity.EInfinity.IntervalCuts.InsertionFamilies
public import SerrePositivity.EInfinity.IntervalCuts.TupleUpdates

/-!
# 指定因子での出力族と次数の分割

概要：Berger–Fresse §2.2.6 の外側出力族を指定因子の前後へ分ける。
方針：前方と後方の有限添字を元の添字と照合し、全次数を有限和で比較する。
規約：前方次数は既存の prefixDegree と一致させる。
使われ方：二段作用の係数交換符号と入力全次数の一致。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

/-- 概要：元の族は前方・指定因子・後方の連結（BF §2.2.6）。
方針：連結の前半・後半と後半の先頭・尾で有限添字を比較する。
規約：最後の arity の移送は添字の値を保つ。
使われ方：実際の面テンソルを指定出力の前後へ分割する。 -/
lemma family_eq_blocks {α : Type*} {m : ℕ} (f : Fin (m + 1) → α) (i : Fin (m + 1)) :
    f = Fin.append (prefixFamily f i) (Fin.cons (f i) (suffixFamily f i)) ∘
      Fin.cast (by omega : m + 1 = i.val + (m - i.val + 1)) := by
  let h : m + 1 = i.val + (m - i.val + 1) := by omega
  have H : f ∘ Fin.cast h.symm =
      Fin.append (prefixFamily f i) (Fin.cons (f i) (suffixFamily f i)) := by
    funext j
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · rw [Fin.append_left]
      rfl
    · rw [Fin.append_right]
      refine Fin.cases ?_ (fun b => ?_) b
      · rw [Fin.cons_zero]
        apply congrArg f
        exact Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd,
          Fin.val_zero, Nat.add_zero])
      · rw [Fin.cons_succ]
        apply congrArg f
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
        omega
  funext j
  have hj := congrFun H (Fin.cast h j)
  simpa only [Function.comp_apply, Fin.cast_cast, Fin.cast_refl, id_eq] using hj

/-- 概要：前方ブロックの全次数は既存の前方次数（BF §2.2.7）。
方針：前方の有限添字と指定位置未満の添字のフィルターを全単射で比較する。
規約：指定因子自身の次数を含めない。
使われ方：余代入の交換符号を既存の prefixDegree で記述する。 -/
lemma tupleDegree_prefixFamily {m : ℕ} (f : Fin (m + 1) → Simplex) (i : Fin (m + 1)) :
    tupleDegree i.val (prefixFamily f i) = prefixDegree (m + 1) f i := by
  rw [tupleDegree_eq_sum, prefixDegree]
  apply Finset.sum_bij (fun j _ => (⟨j.val, by have := j.isLt; have := i.isLt; omega⟩ :
    Fin (m + 1)))
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
  · intro j _ k _ he
    have hv := congrArg Fin.val he
    exact Fin.ext hv
  · intro j hj
    exact ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, rfl⟩
  · intro j _
    rfl

/-- 概要：外側族の全次数は前方・指定因子・後方次数の和（BF §2.2.3）。
方針：族の三ブロック表示を全次数の連結公式へ渡す。
規約：全て自然数の次数で述べる。
使われ方：実際の余代入の入力の整数次数の整合性。 -/
lemma tupleDegree_family_blocks {m : ℕ} (f : Fin (m + 1) → Simplex) (i : Fin (m + 1)) :
    tupleDegree (m + 1) f = tupleDegree i.val (prefixFamily f i) +
      simplexDegree (f i) + tupleDegree (m - i.val) (suffixFamily f i) := by
  conv_lhs => rw [family_eq_blocks f i]
  rw [tupleDegree_arity_transport (by omega : i.val + (m - i.val + 1) = m + 1),
    tupleDegree_append, tupleDegree_cons]
  omega

/-- 概要：置換した出力族の全次数は前方・内側・後方次数の和（BF §2.2.3）。
方針：置換族の三ブロック表示で連結の全次数を二回評価する。
規約：内側 arity 零も含む。
使われ方：余代入の出力の整数次数の整合性。 -/
lemma tupleDegree_insertionFamily {m n : ℕ} (f : Fin (m + 1) → Simplex)
    (g : Fin n → Simplex) (i : Fin (m + 1)) :
    tupleDegree (m + n) (insertionFamily f g i) = tupleDegree i.val (prefixFamily f i) +
      tupleDegree n g + tupleDegree (m - i.val) (suffixFamily f i) := by
  rw [insertionFamily_eq_blocks]
  rw [tupleDegree_arity_transport (by omega : i.val + (n + (m - i.val)) = m + n),
    tupleDegree_append, tupleDegree_append]
  omega

end SerrePositivity.EInfinity.IntervalCuts
