-- Build SerrePositivity.HomotopicalAlgebra.Foundations before running this file.
import SerrePositivity.HomotopicalAlgebra.Foundations
import SerrePositivity.Spectra.StageTwo

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

section Under

variable {C : Type u₁} [Category.{v₁} C]

-- Finite limits are specialized from StructuredArrow even without a model structure.
example [Limits.HasFiniteLimits C] (S : C) : Limits.HasFiniteLimits (Under S) := inferInstance
example [Limits.HasFiniteColimits C] (S : C) : Limits.HasFiniteColimits (Under S) := inferInstance

-- A supplied underlying factorization is lifted, with its two factors unchanged.
example (W₁ W₂ : MorphismProperty C) {S : C} {X Y : Under S} {f : X ⟶ Y}
    (hf : MorphismProperty.MapFactorizationData W₁ W₂ f.right) :
    hf.under.i.right = hf.i ∧ hf.under.p.right = hf.p ∧
      hf.under.Z.hom = X.hom ≫ hf.i := ⟨rfl, rfl, rfl⟩

example (W₁ W₂ : MorphismProperty C) [W₁.HasFactorization W₂] (S : C) :
    (W₁.under (X := S)).HasFactorization W₂.under := inferInstance

variable [ModelCategory C] (S : C)

example : ModelCategory (Under S) := inferInstance
example (X : Under S) : ModelCategory (Under X) := inferInstance

-- The chosen classes are exactly inverse images, including both trivial classes.
example : cofibrations (Under S) = (cofibrations C).inverseImage (Under.forget S) := rfl
example : fibrations (Under S) = (fibrations C).inverseImage (Under.forget S) := rfl
example : weakEquivalences (Under S) =
    (weakEquivalences C).inverseImage (Under.forget S) := rfl
example : trivialCofibrations (Under S) =
    (trivialCofibrations C).inverseImage (Under.forget S) := rfl
example : trivialFibrations (Under S) =
    (trivialFibrations C).inverseImage (Under.forget S) := rfl

example {X Y : Under S} (f : X ⟶ Y) [Cofibration f.right] : Cofibration f :=
  (cofibrations_under_iff S f).2 inferInstance
example {X Y : Under S} (f : X ⟶ Y) [Fibration f.right] : Fibration f :=
  (fibrations_under_iff S f).2 inferInstance
example {X Y : Under S} (f : X ⟶ Y) [WeakEquivalence f.right] : WeakEquivalence f :=
  (weakEquivalences_under_iff S f).2 inferInstance

-- Both CM5 factorizations and both CM4 lifting conditions are usable at the entry point.
example : (cofibrations (Under S)).HasFactorization (trivialFibrations (Under S)) := inferInstance
example : (trivialCofibrations (Under S)).HasFactorization (fibrations (Under S)) := inferInstance

example {A B X Y : Under S} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [WeakEquivalence i] [Fibration p] : HasLiftingProperty i p := inferInstance
example {A B X Y : Under S} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [WeakEquivalence p] : HasLiftingProperty i p := inferInstance

end Under

-- Existing StageTwo APIs still resolve when the shared model-category entry is imported.
noncomputable example (X : SerrePositivity.PointedSimplicialSet.{u₁}) :
    SerrePositivity.SymmetricSpectrum.pointwiseTensorFunctor X ⊣
      SerrePositivity.SymmetricSpectrum.cotensorFunctor X :=
  SerrePositivity.SymmetricSpectrum.pointwiseTensorCotensorAdjunction X
