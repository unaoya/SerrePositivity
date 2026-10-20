module
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # tensor 右端の積の結合と単位
概要：任意の monoidal 圏で、固定した左因子の右端にある二つのモノイド因子を結合する。
方針：元の結合の自然性・五角形・モノイドの結合単位則を使う。
規約：因子順を変えない。使われ方：全鎖立方体の隣接 connection と面の関係式。
-/
@[expose] public section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category.{v} V] [MonoidalCategory V] (L P : V) [MonObj P]

/-- 元の結合射と積による、固定左因子の右端二因子の結合。 -/
def tensorRightMultiplication : (L ⊗ P) ⊗ P ⟶ L ⊗ P :=
  (α_ L P P).hom ≫ (L ◁ MonObj.mul (X := P))

/-- 右端の隣接三因子の二つの結合順は、同じ元の射を与える。 -/
lemma tensorRightMultiplication_assoc :
    tensorRightMultiplication (L ⊗ P) P ≫ tensorRightMultiplication L P =
      (tensorRightMultiplication L P ▷ P) ≫ tensorRightMultiplication L P := by
  dsimp only [tensorRightMultiplication]
  simp only [Category.assoc, comp_whiskerRight_assoc, associator_naturality_right_assoc,
    associator_naturality_middle_assoc]
  rw [← pentagon_assoc]
  simp only [← whiskerLeft_comp, ← MonObj.mul_assoc]

/-- 右端へ単位を挿入して右端二因子を結合すると、元の恒等射。 -/
lemma tensorRightMultiplication_right_unit :
    (ρ_ (L ⊗ P)).inv ≫ ((L ⊗ P) ◁ MonObj.one (X := P)) ≫
      tensorRightMultiplication L P = 𝟙 (L ⊗ P) := by
  dsimp only [tensorRightMultiplication]
  simp only [associator_naturality_right_assoc, ← whiskerLeft_comp]
  rw [MonObj.mul_one]
  monoidal

/-- 右から二番目へ単位を挿入して結合すると、元の恒等射。 -/
lemma tensorRightMultiplication_left_unit :
    (((ρ_ L).inv ≫ (L ◁ MonObj.one (X := P))) ▷ P) ≫
      tensorRightMultiplication L P = 𝟙 (L ⊗ P) := by
  dsimp only [tensorRightMultiplication]
  simp only [comp_whiskerRight_assoc, associator_naturality_middle_assoc,
    ← whiskerLeft_comp]
  rw [MonObj.one_mul]
  monoidal

end SerrePositivity.KST.SConstruction
