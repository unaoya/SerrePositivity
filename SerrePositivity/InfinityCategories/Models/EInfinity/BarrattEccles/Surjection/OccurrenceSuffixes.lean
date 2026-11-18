module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesuras
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Chain

/-!
模型。文献の定義との比較は後で
# 有限語の再出現とリストの尾部

概要：Berger–Fresse §1.4.2 の区切り条件を復元行のリストの計算へ移す。
方針：有限語を ofFn でリスト化し、後の同値の存在を drop の所属へ直す。
規約：位置は零から数える。
使われ方：復元行の移動則と非退化性を実際の全射語へ適用する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：区切りであることは後続の尾部に同値が現れること（BF §1.4.2）。
方針：drop の所属を元のリストの添字で表す。
規約：位置自身は尾部に含めない。
使われ方：有限語の区切りをリストの一文字の移動則へ渡す。 -/
lemma caesura_iff_mem_drop {n l : ℕ} (v : Fin l → Fin n) (i : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i ↔ v i ∈ (List.ofFn v).drop (i.val + 1) := by
  constructor
  · rintro ⟨j, hij, he⟩
    apply List.mem_drop_iff_getElem.mpr
    have hj := j.isLt
    change i.val < j.val at hij
    refine ⟨j.val - (i.val + 1), by rw [List.length_ofFn]; omega, ?_⟩
    simp only [List.getElem_ofFn]
    have hi : (⟨i.val + 1 + (j.val - (i.val + 1)), by omega⟩ : Fin l) = j := by
      apply Fin.ext
      change i.val + 1 + (j.val - (i.val + 1)) = j.val
      omega
    rw [hi]
    exact he
  · intro h
    obtain ⟨k, hk, he⟩ := List.mem_drop_iff_getElem.mp h
    have hk' : k + (i.val + 1) < l := by simpa only [List.length_ofFn] using hk
    refine ⟨⟨i.val + 1 + k, by omega⟩, ?_, ?_⟩
    · change i.val < i.val + 1 + k
      omega
    · simpa only [List.getElem_ofFn] using he

/-- 概要：非退化な有限語のリストは隣接非一致を満たす（BF §1.2.1）。
方針：隣接する自然数添字を有限添字へ直す。
規約：全射性は不要。
使われ方：復元行の変化が非自明であることを元の語から導く。 -/
lemma isChain_ofFn_of_nondegenerate {n l : ℕ} (v : Fin l → Fin n)
    (hv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate v) : (List.ofFn v).IsChain (· ≠ ·) := by
  apply List.isChain_iff_getElem.mpr
  intro k hk
  have hk' : k + 1 < l := by simpa only [List.length_ofFn] using hk
  simpa only [List.getElem_ofFn] using
    hv ⟨k, by omega⟩ ⟨k + 1, hk'⟩ rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
