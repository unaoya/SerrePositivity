-- Build SerrePositivity.HomotopicalAlgebra.Foundations before running this file.
import SerrePositivity.HomotopicalAlgebra.Foundations

universe u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory HomotopicalAlgebra SerrePositivity.Quillen

section Quillen

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {E : Type u₃} [Category.{v₃} E] [ModelCategory E]

-- Consumers can use the identity and composition instances at independent universes.
example : IsLeftQuillen (𝟭 C) := inferInstance
example : IsRightQuillen (𝟭 C) := inferInstance

example (L : C ⥤ D) (L' : D ⥤ E) [IsLeftQuillen L] [IsLeftQuillen L'] :
    IsLeftQuillen (L ⋙ L') := inferInstance

example (R : D ⥤ C) (R' : E ⥤ D) [IsRightQuillen R] [IsRightQuillen R'] :
    IsRightQuillen (R' ⋙ R) := inferInstance

-- An ordinary adjunction suffices; there is no parallel Quillen adjunction type.
example {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [IsLeftQuillen L] :
    IsRightQuillen R := isRightQuillen_of_isLeftQuillen adj

example {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [IsRightQuillen R] :
    IsLeftQuillen L := isLeftQuillen_of_isRightQuillen adj

example (L : C ⥤ D) [IsLeftQuillen L] {X Y : C} (i : X ⟶ Y)
    [Cofibration i] [WeakEquivalence i] :
    Cofibration (L.map i) ∧ WeakEquivalence (L.map i) :=
  ⟨map_cofibration L i, map_weakEquivalence_of_cofibration L i⟩

example (R : D ⥤ C) [IsRightQuillen R] {X Y : D} (p : X ⟶ Y)
    [Fibration p] [WeakEquivalence p] :
    Fibration (R.map p) ∧ WeakEquivalence (R.map p) :=
  ⟨map_fibration R p, map_weakEquivalence_of_fibration R p⟩

end Quillen
