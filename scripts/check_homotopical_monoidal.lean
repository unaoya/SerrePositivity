import SerrePositivity.HomotopicalAlgebra.Foundations

universe u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory HomotopicalAlgebra SerrePositivity.Quillen

section Bifunctor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [ModelCategory C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [ModelCategory C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [ModelCategory C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} (adj : F ⊣₂ G)

example [IsQuillenBifunctor F] : HasQuillenPullbackHom G :=
  (isQuillenBifunctor_iff_pullbackHom adj).1 inferInstance

example [HasQuillenPullbackHom G] : IsQuillenBifunctor F :=
  (isQuillenBifunctor_iff_pullbackHom adj).2 inferInstance

example [IsQuillenBifunctor F] : IsQuillenBifunctor F.flip := inferInstance

-- Both trivial input alternatives work on arbitrary choices of pushout and pullback squares.
example [IsQuillenBifunctor F] {A B : C₁} {X Y : C₂}
    (i : A ⟶ B) (j : X ⟶ Y) (s : F.PushoutObjObj i j)
    [Cofibration i] [Cofibration j] [WeakEquivalence j] :
    Cofibration s.ι ∧ WeakEquivalence s.ι :=
  ⟨IsQuillenBifunctor.cofibration i j s inferInstance inferInstance,
    IsQuillenBifunctor.weakEquivalence i j s inferInstance inferInstance (Or.inr inferInstance)⟩

example [HasQuillenPullbackHom G] {A B : C₁} {X Y : C₃}
    (i : A ⟶ B) (p : X ⟶ Y) (s : G.PullbackObjObj i p)
    [Cofibration i] [WeakEquivalence i] [Fibration p] :
    Fibration s.π ∧ WeakEquivalence s.π :=
  ⟨HasQuillenPullbackHom.fibration i p s inferInstance inferInstance,
    HasQuillenPullbackHom.weakEquivalence i p s inferInstance inferInstance (Or.inl inferInstance)⟩

end Bifunctor

open CategoryTheory.MonoidalCategory

section Monoidal
variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  [MonoidalCategory C] [MonoidalClosed C]

example [IsCofibrant (𝟙_ C)] : HasUnitAxiom C := unitAxiom_of_cofibrant_unit C

example : MonoidalModelCategory C ↔
    HasQuillenPullbackHom (MonoidalClosed.internalHom (C := C)) ∧ HasUnitAxiom C :=
  monoidalModelCategory_iff C

example [MonoidalModelCategory C] {A B X Y : C}
    (i : A ⟶ B) (j : X ⟶ Y) [Cofibration i] [Cofibration j] [WeakEquivalence i] :
    Cofibration (Arrow.mk i □ Arrow.mk j).hom ∧ WeakEquivalence (Arrow.mk i □ Arrow.mk j).hom :=
  ⟨pushoutProduct_cofibration C i j,
    pushoutProduct_weakEquivalence C i j (Or.inl inferInstance)⟩

example [MonoidalModelCategory C] {A B X Y : C}
    (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p] [WeakEquivalence p] :
    Fibration ((.op (Arrow.mk i)) ⋔ Arrow.mk p).hom ∧
      WeakEquivalence ((.op (Arrow.mk i)) ⋔ Arrow.mk p).hom := by
  have := ((monoidalModelCategory_iff C).1 inferInstance).1
  exact ⟨pullbackHom_fibration C i p,
    pullbackHom_weakEquivalence C i p (Or.inr inferInstance)⟩
end Monoidal
