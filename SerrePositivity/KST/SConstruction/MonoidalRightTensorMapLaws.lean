module
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-! # 対象を明示した右 tensor の恒等・合成則
概要：元の右 tensor 射の恒等・合成保存を、値域の圏を抽象化して証明する。
方針：tensor 射の全対象を明示し、元の monoidal category の法則を適用する。
規約：因子順は元のまま。使われ方：鎖立方体の型を固定した右 tensor 関手性。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory

/-- 全対象を明示した右 tensor は、元の恒等射を保つ。 -/
lemma monoidalRightTensorMap_id {C : Type u} [Category.{v} C] [MonoidalCategory C] (X I : C) :
    @tensorHom C _ _ X X I I (𝟙 X) (𝟙 I) = 𝟙 (X ⊗ I) := by
  simp only [tensorHom_id, id_whiskerRight]

/-- 全対象を明示した右 tensor は、元の合成を保つ。 -/
lemma monoidalRightTensorMap_comp {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {X Y Z I : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    @tensorHom C _ _ X Z I I (f ≫ g) (𝟙 I) =
      @tensorHom C _ _ X Y I I f (𝟙 I) ≫ @tensorHom C _ _ Y Z I I g (𝟙 I) := by
  simp only [tensorHom_comp_tensorHom, Category.comp_id]

/-- 元の右単位比較は、全対象を明示した右 tensor について自然。 -/
lemma monoidalRightTensorMap_unit {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {X Y : C} (f : X ⟶ Y) :
    f ≫ (ρ_ Y).inv = (ρ_ X).inv ≫
      @tensorHom C _ _ X Y (𝟙_ C) (𝟙_ C) f (𝟙 (𝟙_ C)) := by
  simpa only [tensorHom_id] using rightUnitor_inv_naturality f

end SerrePositivity.KST.SConstruction
