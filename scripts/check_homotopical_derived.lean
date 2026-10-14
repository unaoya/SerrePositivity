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
