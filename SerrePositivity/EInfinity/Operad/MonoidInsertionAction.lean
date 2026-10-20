module

public import SerrePositivity.EInfinity.Operad.MonoidInsertion

/-!
# 任意の入力位置への反復積の代入

概要：BM §1 の部分合成則を標準の入力位置の表示で得る。
方針：三ブロックの代入に移し、入出力の arity の移送を相殺する。
規約：全 arity と全入力位置、零入力も含む。
使われ方：Com の代数作用の公理。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] (X : Complex A) [MonObj X]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：任意の入力位置へ反復積を代入しても全体の積になる（BM §1）。
方針：区間長を明示した既存の代入へ移し、反復積の arity 移送則を使う。
規約：零入力・全入力位置。
使われ方：Com の代数の部分合成則。 -/
lemma powerProduct_insertion (m n : ℕ) (i : Fin (m + 1)) :
    tensorInsertionAction X (𝟙_ (Complex A)) m n i
      ((λ_ (power X n)).hom ≫ powerProduct X n) ≫ powerProduct X (m + 1) =
    (λ_ (power X (m + n))).hom ≫ powerProduct X (m + n) := by
  rw [tensorInsertionAction_eq_core]
  simp only [Category.assoc]
  rw [    powerProduct_index X (by omega : i.val + (m - i.val + 1) = m + 1),
    powerProduct_insertionCore, leftUnitor_naturality_assoc,
    powerProduct_index X (by omega : m + n = i.val + (n + (m - i.val)))]

end SerrePositivity.EInfinity
