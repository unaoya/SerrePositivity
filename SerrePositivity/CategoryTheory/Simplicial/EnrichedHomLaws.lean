module

public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic

/-!
# 単体的写像対象の単位と合成
-/

/-! # 単体的豊穣圏の零次単体と通常の射の法則 -/

@[expose] public section SimplicialHomLaws
universe v u

namespace SerrePositivity.SimplicialHomLaws

open CategoryTheory CategoryTheory.SimplicialCategory
open scoped Simplicial

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 通常の恒等射の零次単体は豊穣の単位の零次単体。 -/
def identityLaw (X : C) : Prop :=
  homEquiv' X X (𝟙 X) = (eId SSet.{v} X).app (Opposite.op ⦋0⦌) PUnit.unit

/-- 通常の射の合成の零次単体は豊穣の合成を零次で適用したもの。 -/
def compositionLaw {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  homEquiv' X Z (f ≫ g) =
    (sHomComp X Y Z).app (Opposite.op ⦋0⦌) (homEquiv' X Y f, homEquiv' Y Z g)

/-- Hom同値の恒等射の保存を零次単体へ評価する。 -/
lemma identity (X : C) : identityLaw X := by
  unfold identityLaw homEquiv'
  rw [Equiv.trans_apply, eHomEquiv_id]
  rfl

/-- Hom同値の合成の保存を零次単体へ評価する。 -/
lemma composition {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : compositionLaw f g := by
  unfold compositionLaw homEquiv'
  rw [Equiv.trans_apply, eHomEquiv_comp]
  rfl

end SerrePositivity.SimplicialHomLaws

end SimplicialHomLaws
