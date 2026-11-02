module

public import SerrePositivity.Spectra.ModelCategory.LevelAcyclicity
public import SerrePositivity.Spectra.General.FreeLevelNaturality
public import SerrePositivity.Spectra.SymmetricSequence.FreeInductionNaturality
public import SerrePositivity.CategoryTheory.Limits
public import SerrePositivity.HomotopicalAlgebra.Monoidal.CofibrantTensor

/-! # Evaluated free generators in a monoidal model category

The induction indexing groupoid is thin. Its colimits preserve cofibrations
and trivial cofibrations because these classes are stable under coproducts.
The coefficients in the induction diagram are cofibrant tensor powers of K.
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra CategoryTheory.MonoidalCategory
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.Quillen

namespace SerrePositivity.SpectrumLevelModel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [ModelCategory C]
  [IsQuillenBifunctor (curriedTensor C)] [IsCofibrant (𝟙_ C)]
  (K : C) [IsCofibrant K]

lemma freeInductionInputMap_cofibration {X Y : C} (f : X ⟶ Y)
    [Cofibration f] (n m : ℕ) :
    cofibrations C
      (SymmetricSequence.freeInductionInputMap
        (SymmetricSequence.tensorPowerSequence K) n f m) := by
  let J := CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)
  have : (cofibrations C).IsStableUnderColimitsOfShape J :=
    ThinGroupoid.isStableUnderColimitsOfShape (cofibrations C)
  apply (cofibrations C).colimMap
  intro d
  have : IsCofibrant (TensorPowers.power K (FiniteBijection.card d.left)) :=
    tensorPower_isCofibrant K _
  have := tensorLeft_isLeftQuillen (TensorPowers.power K (FiniteBijection.card d.left))
  exact IsLeftQuillen.map_cofibrations
    (L := tensorLeft (TensorPowers.power K (FiniteBijection.card d.left))) _
    (mem_cofibrations f)

lemma evaluatedFree_cofibration {X Y : C} (f : X ⟶ Y)
    [Cofibration f] (n m : ℕ) :
    cofibrations C ((freeAt (K := K) n ⋙ evaluation m).map f) := by
  apply ((cofibrations C).arrow_mk_iso_iff
    (Arrow.isoMk (freeAtLevelIsoInduction (K := K) n X m)
      (freeAtLevelIsoInduction (K := K) n Y m) (freeAtLevelIsoInduction_input n f m).symm)).2
  exact freeInductionInputMap_cofibration K f n m

lemma freeInductionInputMap_trivialCofibration {X Y : C} (f : X ⟶ Y)
    [Cofibration f] [WeakEquivalence f] (n m : ℕ) :
    trivialCofibrations C
      (SymmetricSequence.freeInductionInputMap
        (SymmetricSequence.tensorPowerSequence K) n f m) := by
  let J := CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)
  have : (trivialCofibrations C).IsStableUnderColimitsOfShape J :=
    ThinGroupoid.isStableUnderColimitsOfShape (trivialCofibrations C)
  apply (trivialCofibrations C).colimMap
  intro d
  have : IsCofibrant (TensorPowers.power K (FiniteBijection.card d.left)) :=
    tensorPower_isCofibrant K _
  have := tensorLeft_isLeftQuillen (TensorPowers.power K (FiniteBijection.card d.left))
  exact IsLeftQuillen.map_trivialCofibrations
    (L := tensorLeft (TensorPowers.power K (FiniteBijection.card d.left))) _
    (mem_trivialCofibrations f)

lemma evaluatedFree_trivialCofibration {X Y : C} (f : X ⟶ Y)
    [Cofibration f] [WeakEquivalence f] (n m : ℕ) :
    trivialCofibrations C ((freeAt (K := K) n ⋙ evaluation m).map f) := by
  apply ((trivialCofibrations C).arrow_mk_iso_iff
    (Arrow.isoMk (freeAtLevelIsoInduction (K := K) n X m)
      (freeAtLevelIsoInduction (K := K) n Y m) (freeAtLevelIsoInduction_input n f m).symm)).2
  exact freeInductionInputMap_trivialCofibration K f n m
end SerrePositivity.SpectrumLevelModel
