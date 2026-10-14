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
