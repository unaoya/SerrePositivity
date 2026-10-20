module
public import Mathlib.CategoryTheory.Monoidal.Category

/-! # 右端の挿入・削除・結合の左因子自然性
概要：左因子の任意の射は、右端の点挿入・増大・二因子結合と厳密に交換する。
方針：元の単位・結合の自然性と whisker の交換則を使う。
規約：対称性や可逆性は仮定しない。使われ方：離れた cubical 座標の交換関係。
-/
@[expose] public section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category.{v} V] [MonoidalCategory V] {L M P : V} (f : L ⟶ M)

/-- 左因子の任意の射と、元の右端の点挿入は自然に交換する。 -/
lemma tensorRightPoint_naturality (a : 𝟙_ V ⟶ P) :
    f ≫ (ρ_ M).inv ≫ (M ◁ a) = (ρ_ L).inv ≫ (L ◁ a) ≫ (f ▷ P) := by
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange]

/-- 左因子の任意の射と、元の右端の削除は自然に交換する。 -/
lemma tensorRightDeletion_naturality (t : P ⟶ 𝟙_ V) :
    (f ▷ P) ≫ (M ◁ t) ≫ (ρ_ M).hom = (L ◁ t) ≫ (ρ_ L).hom ≫ f := by
  rw [← whisker_exchange_assoc, rightUnitor_naturality]

/-- 左因子の任意の射と、元の右端二因子の結合は自然に交換する。 -/
lemma tensorRightConnection_naturality (m : P ⊗ P ⟶ P) :
    (f ▷ P ▷ P) ≫ (α_ M P P).hom ≫ (M ◁ m) =
      (α_ L P P).hom ≫ (L ◁ m) ≫ (f ▷ P) := by
  rw [associator_naturality_left_assoc, ← whisker_exchange]

end SerrePositivity.KST.SConstruction
