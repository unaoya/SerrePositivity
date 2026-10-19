module

public import SerrePositivity.EInfinity.TableReduction.CompositionNaturality
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionNested

/-!
# 全射語の複体射の入れ子結合則

概要：Berger–Fresse §1.2.4–5 の入れ子結合則を整数複体の射で証明する。
方針：三因子 TR の全射で消去し、テンソル自然性・合成保存・BE の結合則を使う。
規約：arity 零を含み、最後に出力 arity の括弧を等式の射で揃える。
使われ方：χ の Operad の nested_assoc。
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

/-- 概要：χ の複体射の部分合成は入れ子結合則を満たす（BF §1.2.4–5）。
方針：全射 TR の三重テンソルを前合成し、両合成を BE の結合則へ戻す。
規約：内側の二回目の挿入位置は i+j。
使われ方：χ の Operad 構造の nested_assoc の証明。 -/
lemma complexPartialComposition_nested_assoc (m n k : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (complexPartialComposition A m (n + 1) i ▷ complex A k) ≫
        complexPartialComposition A (m + n) k ⟨i.val + j.val, by omega⟩ =
      (α_ (complex A (m + 1)) (complex A (n + 1)) (complex A k)).hom ≫
        (complex A (m + 1) ◁ complexPartialComposition A n k j) ≫
        complexPartialComposition A m (n + k) i ≫
        eqToHom (congrArg (complex A) (Nat.add_assoc m n k).symm) := by
  let _ := triple_cochainMap_epi A (m + 1) (n + 1) k
  apply (cancel_epi ((cochainMap A (m + 1) ⊗ₘ cochainMap A (n + 1)) ⊗ₘ cochainMap A k)).1
  have hL := tensor_square_right A (BarrattEccles.partialComposition A m (n + 1) i)
    (complexPartialComposition A m (n + 1) i) (cochainMap A (m + 1))
    (cochainMap A (n + 1)) (cochainMap A (m + n + 1)) (cochainMap A k)
    (complexPartialComposition_comm A m (n + 1) i)
  have hR := tensor_square_left A (BarrattEccles.partialComposition A n k j)
    (complexPartialComposition A n k j) (cochainMap A (m + 1))
    (cochainMap A (n + 1)) (cochainMap A k) (cochainMap A (n + k))
    (complexPartialComposition_comm A n k j)
  calc
    _ = (BarrattEccles.partialComposition A m (n + 1) i ▷ BarrattEccles.complex A k) ≫
        BarrattEccles.partialComposition A (m + n) k ⟨i.val + j.val, by omega⟩ ≫
          cochainMap A (m + n + k) := by
      rw [← Category.assoc, hL, Category.assoc,
        ← complexPartialComposition_comm A (m + n) k ⟨i.val + j.val, by omega⟩]
    _ = (α_ (BarrattEccles.complex A (m + 1)) (BarrattEccles.complex A (n + 1))
        (BarrattEccles.complex A k)).hom ≫
        (BarrattEccles.complex A (m + 1) ◁ BarrattEccles.partialComposition A n k j) ≫
        BarrattEccles.partialComposition A m (n + k) i ≫
        eqToHom (congrArg (BarrattEccles.complex A) (Nat.add_assoc m n k).symm) ≫
          cochainMap A (m + n + k) := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ cochainMap A (m + n + k))
        (BarrattEccles.partialComposition_nested_assoc A m n k i j)
    _ = _ := by
      symm
      rw [associator_naturality_assoc, reassoc_of% hR,
        ← reassoc_of% (complexPartialComposition_comm A m (n + k) i),
        ← cochainMap_arity A (Nat.add_assoc m n k).symm]

end SerrePositivity.EInfinity.Surjection
