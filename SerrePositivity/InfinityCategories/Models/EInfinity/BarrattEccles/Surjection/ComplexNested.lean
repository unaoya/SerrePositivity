module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompositionNaturality
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionNested

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：χ の複体射の部分合成は入れ子結合則を満たす（BF §1.2.4–5）。
方針：全射 TR の三重テンソルを前合成し、両合成を BE の結合則へ戻す。
規約：内側の二回目の挿入位置は i+j。
使われ方：χ の Operad 構造の nested_assoc の証明。 -/
lemma complexPartialComposition_nested_assoc (m n k : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m (n + 1) i ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A k) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A (m + n) k ⟨i.val + j.val, by omega⟩ =
      (α_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (n + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A k)).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A n k j) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m (n + k) i ≫
        eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A) (Nat.add_assoc m n k).symm) := by
  let _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.triple_cochainMap_epi A (m + 1) (n + 1) k
  apply (cancel_epi ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (n + 1)) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A k)).1
  have hL := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.tensor_square_right A (_root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A m (n + 1) i)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m (n + 1) i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (n + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A k)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.complexPartialComposition_comm A m (n + 1) i)
  have hR := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.tensor_square_left A (_root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A n k j)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A n k j) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (n + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (n + k))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.complexPartialComposition_comm A n k j)
  calc
    _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A m (n + 1) i ▷ _root_.SerrePositivity.EInfinity.BarrattEccles.complex A k) ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A (m + n) k ⟨i.val + j.val, by omega⟩ ≫
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n + k) := by
      rw [← Category.assoc, hL, Category.assoc,
        ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.complexPartialComposition_comm A (m + n) k ⟨i.val + j.val, by omega⟩]
    _ = (α_ (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A (m + 1)) (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A (n + 1))
        (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A k)).hom ≫
        (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A (m + 1) ◁ _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A n k j) ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A m (n + k) i ≫
        eqToHom (congrArg (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A) (Nat.add_assoc m n k).symm) ≫
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n + k) := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n + k))
        (_root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition_nested_assoc A m n k i j)
    _ = _ := by
      symm
      rw [associator_naturality_assoc, reassoc_of% hR,
        ← reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.complexPartialComposition_comm A m (n + k) i),
        ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_arity A (Nat.add_assoc m n k).symm]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
