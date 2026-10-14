module

public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown
public import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureCofibrant
public import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureFibrant
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Deriving Quillen functors using cofibrant and fibrant derivability structures

The derived functors and comparison transformations are Mathlib's existing
total derived functors. Existence, computation on good objects and arbitrary
postcomposition follow from the established derivability structures.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅

open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {HC : Type u₃} [Category.{v₃} HC] {HD : Type u₄} [Category.{v₄} HD]
  (QC : C ⥤ HC) [QC.IsLocalization (weakEquivalences C)]
  (QD : D ⥤ HD) [QD.IsLocalization (weakEquivalences D)]

lemma cofibrant_derives (L : C ⥤ D) [IsLeftQuillen L] :
    (CofibrantObject.localizerMorphism C).Derives (L ⋙ QD) := by
  intro X Y f hf
  have : WeakEquivalence f.hom := (weakEquivalence_iff _).2 hf
  have : WeakEquivalence (L.map f.hom) := map_weakEquivalence_of_cofibrant L f.hom
  change IsIso (QD.map (L.map f.hom))
  exact Localization.inverts QD (weakEquivalences D) (L.map f.hom) (mem_weakEquivalences _)

lemma fibrant_derives (R : D ⥤ C) [IsRightQuillen R] :
    (FibrantObject.localizerMorphism D).Derives (R ⋙ QC) := by
  intro X Y f hf
  have : WeakEquivalence f.hom := (weakEquivalence_iff _).2 hf
  have : WeakEquivalence (R.map f.hom) := map_weakEquivalence_of_fibrant R f.hom
  change IsIso (QC.map (R.map f.hom))
  exact Localization.inverts QC (weakEquivalences C) (R.map f.hom) (mem_weakEquivalences _)

instance hasPointwiseLeftDerivedFunctor (L : C ⥤ D) [IsLeftQuillen L] :
    (L ⋙ QD).HasPointwiseLeftDerivedFunctor (weakEquivalences C) :=
  (cofibrant_derives QD L).hasPointwiseLeftDerivedFunctor

instance hasPointwiseRightDerivedFunctor (R : D ⥤ C) [IsRightQuillen R] :
    (R ⋙ QC).HasPointwiseRightDerivedFunctor (weakEquivalences D) :=
  (fibrant_derives QC R).hasPointwiseRightDerivedFunctor

section Left

variable {L : C ⥤ D} [IsLeftQuillen L] {LF : HC ⥤ HD}
  (α : QC ⋙ LF ⟶ L ⋙ QD) [LF.IsLeftDerivedFunctor α (weakEquivalences C)]

/-- Any left derived comparison computes the original functor on cofibrant objects. -/
lemma leftComparison_isIso (X : C) [IsCofibrant X] : IsIso (α.app X) :=
  (cofibrant_derives QD L).isIso' α (CofibrantObject.mk X)

variable {H : Type u₅} [Category.{v₅} H] (T : HD ⥤ H)

/-- Quillen left derived functors are absolute: arbitrary postcomposition
remains left derived. This supplies the hypotheses of `Adjunction.derived`. -/
lemma leftDerived_postcomp :
    (LF ⋙ T).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α T)
        (weakEquivalences C) := by
  have h : (CofibrantObject.localizerMorphism C).Derives ((L ⋙ QD) ⋙ T) := by
    intro X Y f hf
    have := (cofibrant_derives QD L) f hf
    change IsIso (QD.map (L.map f.hom)) at this
    change IsIso (T.map (QD.map (L.map f.hom)))
    infer_instance
  apply h.isLeftDerivedFunctor_of_isIso
  intro X
  have := leftComparison_isIso QC QD α ((CofibrantObject.localizerMorphism C).functor.obj X)
  dsimp
  infer_instance

end Left

section Right

variable {R : D ⥤ C} [IsRightQuillen R] {RF : HD ⥤ HC}
  (β : R ⋙ QC ⟶ QD ⋙ RF) [RF.IsRightDerivedFunctor β (weakEquivalences D)]

lemma rightComparison_isIso (Y : D) [IsFibrant Y] : IsIso (β.app Y) :=
  (fibrant_derives QC R).isIso_of_isRightDerivedFunctor β (FibrantObject.mk Y)

variable {H : Type u₅} [Category.{v₅} H] (T : HC ⥤ H)

lemma rightDerived_postcomp :
    (RF ⋙ T).IsRightDerivedFunctor
      (Functor.whiskerRight β T ≫ (Functor.associator _ _ _).hom)
        (weakEquivalences D) := by
  have h : (FibrantObject.localizerMorphism D).Derives ((R ⋙ QC) ⋙ T) := by
    intro X Y f hf
    have := (fibrant_derives QC R) f hf
    change IsIso (QC.map (R.map f.hom)) at this
    change IsIso (T.map (QC.map (R.map f.hom)))
    infer_instance
  apply h.isRightDerivedFunctor_of_isIso
  intro Y
  have := rightComparison_isIso QC QD β ((FibrantObject.localizerMorphism D).functor.obj Y)
  dsimp
  infer_instance

end Right

end SerrePositivity.Quillen
