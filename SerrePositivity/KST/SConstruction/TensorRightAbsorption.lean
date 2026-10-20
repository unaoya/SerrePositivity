module
public import SerrePositivity.KST.SConstruction.TensorRightMultiplication

/-! # 固定左因子を保つ右端の吸収
概要：左右の吸収式を、固定左因子の右端二因子の結合へ移す。
方針：結合の自然性と単位の coherence で、吸収を削除・挿入の元の合成へ分解する。
規約：因子順を保ち、対称性を仮定しない。使われ方：鎖立方体の一端点の面と connection。
-/
@[expose] public section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category.{v} V] [MonoidalCategory V] (L P : V) [MonObj P]
  (a : 𝟙_ V ⟶ P) (t : P ⟶ 𝟙_ V)

/-- 右端に吸収点を挿入して結合すると、元の削除と同じ点の挿入になる。 -/
lemma tensorRightMultiplication_right_absorption
    (h : (P ◁ a) ≫ MonObj.mul = (ρ_ P).hom ≫ t ≫ a) :
    (ρ_ (L ⊗ P)).inv ≫ ((L ⊗ P) ◁ a) ≫ tensorRightMultiplication L P =
      (L ◁ t) ≫ (ρ_ L).hom ≫ (ρ_ L).inv ≫ (L ◁ a) := by
  dsimp only [tensorRightMultiplication]
  simp only [associator_naturality_right_assoc, ← whiskerLeft_comp]
  rw [h]
  simp only [whiskerLeft_comp, Iso.hom_inv_id_assoc]
  have hc : (ρ_ (L ⊗ P)).inv ≫ (α_ L P (𝟙_ V)).hom ≫
      (L ◁ (ρ_ P).hom) = 𝟙 (L ⊗ P) := by monoidal
  slice_lhs 1 3 => rw [hc]
  simp only [Category.id_comp]

/-- 右から二番目に吸収点を挿入しても、元の削除と同じ点の挿入になる。 -/
lemma tensorRightMultiplication_left_absorption
    (h : (a ▷ P) ≫ MonObj.mul = (λ_ P).hom ≫ t ≫ a) :
    (((ρ_ L).inv ≫ (L ◁ a)) ▷ P) ≫ tensorRightMultiplication L P =
      (L ◁ t) ≫ (ρ_ L).hom ≫ (ρ_ L).inv ≫ (L ◁ a) := by
  dsimp only [tensorRightMultiplication]
  simp only [comp_whiskerRight_assoc, associator_naturality_middle_assoc,
    ← whiskerLeft_comp]
  rw [h]
  simp only [whiskerLeft_comp, Iso.hom_inv_id_assoc]
  have hc : (ρ_ L).inv ▷ P ≫ (α_ L (𝟙_ V) P).hom ≫
      (L ◁ (λ_ P).hom) = 𝟙 (L ⊗ P) := by monoidal
  slice_lhs 1 3 => rw [hc]
  simp only [Category.id_comp]

end SerrePositivity.KST.SConstruction
