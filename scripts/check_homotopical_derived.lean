import SerrePositivity.HomotopicalAlgebra.Foundations

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅

open CategoryTheory HomotopicalAlgebra SerrePositivity.Quillen

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {HC : Type u₃} [Category.{v₃} HC] {HD : Type u₄} [Category.{v₄} HD]
  (QC : C ⥤ HC) [QC.IsLocalization (weakEquivalences C)]
  (QD : D ⥤ HD) [QD.IsLocalization (weakEquivalences D)]

example (L : C ⥤ D) [IsLeftQuillen L] {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence (L.map f) :=
  map_weakEquivalence_of_cofibrant L f

example (R : D ⥤ C) [IsRightQuillen R] {X Y : D} [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence (R.map f) :=
  map_weakEquivalence_of_fibrant R f

-- Derived existence follows from the Quillen conditions and a localization.
example (L : C ⥤ D) [IsLeftQuillen L] :
    (L ⋙ QD).HasPointwiseLeftDerivedFunctor (weakEquivalences C) := inferInstance

example (R : D ⥤ C) [IsRightQuillen R] :
    (R ⋙ QC).HasPointwiseRightDerivedFunctor (weakEquivalences D) := inferInstance

-- Both canonical total derived functors exist without a chosen resolution functor.
noncomputable example (L : C ⥤ D) [IsLeftQuillen L] : HC ⥤ HD :=
  (L ⋙ QD).totalLeftDerived QC (weakEquivalences C)

noncomputable example (R : D ⥤ C) [IsRightQuillen R] : HD ⥤ HC :=
  (R ⋙ QC).totalRightDerived QD (weakEquivalences D)

example {L : C ⥤ D} [IsLeftQuillen L] {LF : HC ⥤ HD}
    (α : QC ⋙ LF ⟶ L ⋙ QD) [LF.IsLeftDerivedFunctor α (weakEquivalences C)]
    (X : C) [IsCofibrant X] : IsIso (α.app X) := leftComparison_isIso QC QD α X

example {R : D ⥤ C} [IsRightQuillen R] {RF : HD ⥤ HC}
    (β : R ⋙ QC ⟶ QD ⋙ RF) [RF.IsRightDerivedFunctor β (weakEquivalences D)]
    (Y : D) [IsFibrant Y] : IsIso (β.app Y) := rightComparison_isIso QC QD β Y

-- Arbitrary postcomposition, rather than merely adjoint postcomposition, is derived.
example {H : Type u₅} [Category.{v₅} H] (T : HD ⥤ H)
    {L : C ⥤ D} [IsLeftQuillen L] {LF : HC ⥤ HD}
    (α : QC ⋙ LF ⟶ L ⋙ QD) [LF.IsLeftDerivedFunctor α (weakEquivalences C)] :
    (LF ⋙ T).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α T) (weakEquivalences C) :=
  leftDerived_postcomp QC QD α T

example {H : Type u₅} [Category.{v₅} H] (T : HC ⥤ H)
    {R : D ⥤ C} [IsRightQuillen R] {RF : HD ⥤ HC}
    (β : R ⋙ QC ⟶ QD ⋙ RF) [RF.IsRightDerivedFunctor β (weakEquivalences D)] :
    (RF ⋙ T).IsRightDerivedFunctor
      (Functor.whiskerRight β T ≫ (Functor.associator _ _ _).hom) (weakEquivalences D) :=
  rightDerived_postcomp QC QD β T

section Adjunction

variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [IsLeftQuillen L] [IsRightQuillen R]

-- The actual Mathlib total derived functors admit a derived adjunction.
noncomputable example :
    (L ⋙ QD).totalLeftDerived QC (weakEquivalences C) ⊣
      (R ⋙ QC).totalRightDerived QD (weakEquivalences D) :=
  derivedAdjunction QC QD adj
    ((L ⋙ QD).totalLeftDerivedCounit QC (weakEquivalences C))
    ((R ⋙ QC).totalRightDerivedUnit QD (weakEquivalences D))

variable {LF : HC ⥤ HD} {RF : HD ⥤ HC}
  (α : QC ⋙ LF ⟶ L ⋙ QD) (β : R ⋙ QC ⟶ QD ⋙ RF)
  [LF.IsLeftDerivedFunctor α (weakEquivalences C)]
  [RF.IsRightDerivedFunctor β (weakEquivalences D)]

example (X : C) (Y : D) (f : L.obj X ⟶ Y) :
    (derivedAdjunction QC QD adj α β).homEquiv (QC.obj X) (QD.obj Y)
      (α.app X ≫ QD.map f) = QC.map (adj.homEquiv X Y f) ≫ β.app Y :=
  derivedAdjunction_homEquiv QC QD adj α β X Y f

-- The consumer may use the result as an ordinary adjunction, including its triangle identities.
example (X : HC) :
    LF.map ((derivedAdjunction QC QD adj α β).unit.app X) ≫
      (derivedAdjunction QC QD adj α β).counit.app (LF.obj X) = 𝟙 _ :=
  (derivedAdjunction QC QD adj α β).left_triangle_components X

example (Y : HD) :
    (derivedAdjunction QC QD adj α β).unit.app (RF.obj Y) ≫
      RF.map ((derivedAdjunction QC QD adj α β).counit.app Y) = 𝟙 _ :=
  (derivedAdjunction QC QD adj α β).right_triangle_components Y

example (hu : ∀ (X : C), IsCofibrant X →
    IsIso ((derivedAdjunction QC QD adj α β).unit.app (QC.obj X)))
    (hc : ∀ (Y : D), IsFibrant Y →
    IsIso ((derivedAdjunction QC QD adj α β).counit.app (QD.obj Y))) :
    LF.IsEquivalence := (derived_isEquivalence_iff QC QD adj α β).2 ⟨hu, hc⟩

-- The usual model-level weak-equivalence mate condition suffices, without a
-- separately supplied functorial replacement or an equivalence assumption.
example (h : ∀ (X : C), IsCofibrant X → ∀ (Y : D), IsFibrant Y →
    ∀ (f : L.obj X ⟶ Y), WeakEquivalence f ↔ WeakEquivalence (adj.homEquiv X Y f)) :
    LF.IsEquivalence := derived_isEquivalence_of_mate_weakEquivalences QC QD adj α β h

variable {LF' : HC ⥤ HD} {RF' : HD ⥤ HC}
  (α' : QC ⋙ LF' ⟶ L ⋙ QD) (β' : R ⋙ QC ⟶ QD ⋙ RF')
  [LF'.IsLeftDerivedFunctor α' (weakEquivalences C)]
  [RF'.IsRightDerivedFunctor β' (weakEquivalences D)]

-- Both adjunction transformations transport naturally across changes of derived choices.
example : (derivedAdjunction QC QD adj α β).unit ≫
    Functor.whiskerRight (leftChoiceIso QC QD α α').hom RF ≫
    Functor.whiskerLeft LF' (rightChoiceIso QC QD β β').hom =
      (derivedAdjunction QC QD adj α' β').unit :=
  derivedAdjunction_unit_choice QC QD adj α β α' β'

example : Functor.whiskerRight (rightChoiceIso QC QD β β').hom LF ≫
    Functor.whiskerLeft RF' (leftChoiceIso QC QD α α').hom ≫
    (derivedAdjunction QC QD adj α' β').counit =
      (derivedAdjunction QC QD adj α β).counit :=
  derivedAdjunction_counit_choice QC QD adj α β α' β'

end Adjunction
