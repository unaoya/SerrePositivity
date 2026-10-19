module

public import SerrePositivity.EInfinity.Surjection.ComplexParallelPreparation
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionParallel

/-!
# 全射語の複体射の並列結合則

概要：Berger–Fresse §1.2.4–5 の独立な二代入の交換を整数複体の射で証明する。
方針：三重テンソル TR の全射で消去し、出力移送・因子交換の自然性と BE の法則を使う。
規約：零 arity を含み、交換符号は既存の Koszul braiding に含まれる。
使われ方：χ の Operad の parallel_assoc。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Surjection

open CategoryTheory MonoidalCategory TableReduction
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：χ の二つの独立な代入は出力 arity の移送後に交換できる（BF §1.2.4–5）。
方針：全射 TR の三重テンソルで消去し、BE の前向き並列結合則へ戻す。
規約：二つの挿入位置は異なればよく、順序は要求しない。
使われ方：Operad の並列結合則へ位置と出力移送を整える。 -/
lemma complexPartialComposition_parallel_assoc_forward (m n k : ℕ)
    (i j : Fin (m + 2)) (hji : j ≠ i) :
    (complexCompositionAfterInsertion A m n i ▷ complex A k) ≫
        complexPartialComposition A (m + n) k (BarrattEccles.parallelSlot m n i j hji) ≫
        eqToHom (congrArg (complex A) (by omega : m + n + k = m + k + n)) =
      BarrattEccles.exchangeLastFactors (complex A (m + 2)) (complex A n) (complex A k) ≫
        (complexCompositionAfterInsertion A m k j ▷ complex A n) ≫
        complexPartialComposition A (m + k) n (BarrattEccles.parallelSlot m k j i hji.symm) := by
  let _ := triple_cochainMap_epi A (m + 2) n k
  apply (cancel_epi ((cochainMap A (m + 2) ⊗ₘ cochainMap A n) ⊗ₘ cochainMap A k)).1
  have hL := tensor_square_right A (BarrattEccles.partialCompositionAfterInsertion A m n i)
    (complexCompositionAfterInsertion A m n i) (cochainMap A (m + 2)) (cochainMap A n)
    (cochainMap A (m + n + 1)) (cochainMap A k) (complexCompositionAfterInsertion_comm A m n i)
  have hR := tensor_square_right A (BarrattEccles.partialCompositionAfterInsertion A m k j)
    (complexCompositionAfterInsertion A m k j) (cochainMap A (m + 2)) (cochainMap A k)
    (cochainMap A (m + k + 1)) (cochainMap A n) (complexCompositionAfterInsertion_comm A m k j)
  calc
    _ = (BarrattEccles.partialCompositionAfterInsertion A m n i ▷ BarrattEccles.complex A k) ≫
        BarrattEccles.partialComposition A (m + n) k (BarrattEccles.parallelSlot m n i j hji) ≫
        eqToHom (congrArg (BarrattEccles.complex A) (by omega : m + n + k = m + k + n)) ≫
          cochainMap A (m + k + n) := by
      rw [reassoc_of% hL,
        ← reassoc_of% (complexPartialComposition_comm A (m + n) k
          (BarrattEccles.parallelSlot m n i j hji)),
        ← cochainMap_arity A (by omega : m + n + k = m + k + n)]
    _ = BarrattEccles.exchangeLastFactors (BarrattEccles.complex A (m + 2))
        (BarrattEccles.complex A n) (BarrattEccles.complex A k) ≫
        (BarrattEccles.partialCompositionAfterInsertion A m k j ▷ BarrattEccles.complex A n) ≫
        BarrattEccles.partialComposition A (m + k) n
          (BarrattEccles.parallelSlot m k j i hji.symm) ≫ cochainMap A (m + k + n) := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ cochainMap A (m + k + n))
        (BarrattEccles.partialComposition_parallel_assoc_forward A m n k i j hji)
    _ = _ := by
      symm
      rw [exchangeLastFactors_naturality_assoc, reassoc_of% hR,
        ← (complexPartialComposition_comm A (m + k) n
          (BarrattEccles.parallelSlot m k j i hji.symm))]

/-- 概要：χ の複体射の部分合成は並列結合則を満たす（BF §1.2.4–5）。
方針：前向きの移送を逆の移送で打ち消し、i<j の挿入位置を評価する。
規約：交換子の符号と結合子は既存の複体テンソルのもの。
使われ方：χ の Operad 構造の parallel_assoc の証明。 -/
lemma complexPartialComposition_parallel_assoc (m n k : ℕ)
    (i j : Fin (m + 2)) (hij : i.val < j.val) :
    (complexPartialComposition A (m + 1) n i ▷ complex A k) ≫
        eqToHom (congrArg (fun q => complex A q ⊗ complex A k)
          (by omega : m + 1 + n = m + n + 1)) ≫
        complexPartialComposition A (m + n) k ⟨j.val + n - 1, by omega⟩ =
      (α_ (complex A (m + 2)) (complex A n) (complex A k)).hom ≫
        (complex A (m + 2) ◁ (β_ (complex A n) (complex A k)).hom) ≫
        (α_ (complex A (m + 2)) (complex A k) (complex A n)).inv ≫
        (complexPartialComposition A (m + 1) k j ▷ complex A n) ≫
        eqToHom (congrArg (fun q => complex A q ⊗ complex A n)
          (by omega : m + 1 + k = m + k + 1)) ≫
        complexPartialComposition A (m + k) n ⟨i.val, by omega⟩ ≫
        eqToHom (congrArg (complex A) (by omega : m + k + n = m + n + k)) := by
  have hji : j ≠ i := fun h => by have hv := congrArg Fin.val h; omega
  have hL : BarrattEccles.parallelSlot m n i j hji = ⟨j.val + n - 1, by omega⟩ := by
    apply Fin.ext
    rw [BarrattEccles.parallelSlot_val]
    exact ite_eq_right (by omega)
  have hR : BarrattEccles.parallelSlot m k j i hji.symm = ⟨i.val, by omega⟩ := by
    apply Fin.ext
    rw [BarrattEccles.parallelSlot_val]
    exact ite_eq_left hij
  have h := congrArg
    (fun f => f ≫ eqToHom (congrArg (complex A) (by omega : m + k + n = m + n + k)))
    (complexPartialComposition_parallel_assoc_forward A m n k i j hji)
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, hL, hR,
    complexCompositionAfterInsertion, BarrattEccles.exchangeLastFactors, comp_whiskerRight] at h
  rw [← arity_tensor_eqToHom A (by omega : m + 1 + n = m + n + 1) (complex A k),
    ← arity_tensor_eqToHom A (by omega : m + 1 + k = m + k + 1) (complex A n)] at h
  simpa only [Category.assoc] using h

end SerrePositivity.EInfinity.Surjection
