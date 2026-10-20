module

public import SerrePositivity.EInfinity.Operad.MonoidPowers
public import SerrePositivity.EInfinity.Operad.InsertionCoreBlocks

/-!
# 反復積へのブロック代入

概要：BM §1 の Com 代数の部分合成則を反復積の結合性から得る。
方針：三ブロックへの代入を連結同型の上で比較し、二ブロックの積の公式を使う。
規約：零入力と空の前後ブロックも含む。
使われ方：可換モノイド対象から Com 代数を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] (X : Complex A) [MonObj X]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power

/-- 概要：明示的な三ブロックへの反復積の代入は全体の積（BM §1）。
方針：ブロック連結で前合成し、代入公式と連結積の公式を使う。
規約：係数は単位対象、ブロック長は零でもよい。
使われ方：Com 代数の任意入力位置の部分合成則。 -/
lemma powerProduct_insertionCore (s n t : ℕ) :
    tensorInsertionCore X (𝟙_ (Complex A)) s n t
      ((λ_ (power X n)).hom ≫ powerProduct X n) ≫ powerProduct X (s + (t + 1)) =
    (λ_ (power X (s + (n + t)))).hom ≫ powerProduct X (s + (n + t)) := by
  apply (cancel_epi ((𝟙_ (Complex A)) ◁
    ((power X s ◁ (appendIso X n t).hom) ≫ (appendIso X s (n + t)).hom))).mp
  rw [← Category.assoc, tensorInsertionCore_on_blocks]
  simp only [Category.assoc]
  rw [powerProduct_append]
  rw [leftUnitor_naturality_assoc]
  simp only [Category.assoc]
  rw [powerProduct_append]
  simp only [tensorHom_def', Category.assoc]
  conv_rhs => rw [← whiskerLeft_comp_assoc, powerProduct_append]
  simp only [powerProduct, mon_tauto]
  rw [braiding_tensorUnit_left]
  monoidal

end SerrePositivity.EInfinity
