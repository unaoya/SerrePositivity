module
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-! # 元の二出力の増大と単位の回収
概要：元の二出力を対角で束ねた後、一方を増大すると他方の元の出力へ戻る。
方針：元の余モノイド射の増大保存と左右の余単位則を使う。
規約：元の二つの出力を変更しない。使われ方：Λ の実 oplax 単位則。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open scoped ComonObj
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- 元の第一出力を増大し元の左単位で戻すと、同じ第二出力を回収する。 -/
lemma comonoidPair_left_unit {P Q : Comon C} {Y : C} (f : P ⟶ Q) (b : P.X ⟶ Y) :
    ((Δ[P.X] ≫ (f.hom ⊗ₘ b)) ≫ (ε[Q.X] ⊗ₘ 𝟙 Y)) ≫ (λ_ Y).hom = b := by
  rw [Category.assoc Δ[P.X], tensorHom_comp_tensorHom, IsComonHom.hom_counit,
    Category.comp_id, ComonObj.counit_comul_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- 元の第二出力を増大し元の右単位で戻すと、同じ第一出力を回収する。 -/
lemma comonoidPair_right_unit {P Q : Comon C} {X : C} (a : P.X ⟶ X) (f : P ⟶ Q) :
    ((Δ[P.X] ≫ (a ⊗ₘ f.hom)) ≫ (𝟙 X ⊗ₘ ε[Q.X])) ≫ (ρ_ X).hom = a := by
  rw [Category.assoc Δ[P.X], tensorHom_comp_tensorHom, IsComonHom.hom_counit,
    Category.comp_id, ComonObj.comul_counit_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end SerrePositivity.KST.SConstruction
