module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowMaps
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceHom

/-! # The augmented bisimplicial word Hom diagram, natural in every outer operator -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRows
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarFixedSource
open OrdinaryBarWordRowMaps
variable (C : Type u) [Category.{v} C] (X Y : D C)

def targetRows : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} :=
  UniverseLift.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) ⋙ Functor.const SimplexCategoryᵒᵖ

def augmentation : rows C X Y ⟶ targetRows C X Y where
  app n := OrdinaryBarFixedRowWordHom.augmentation C n.unop.len X Y
  naturality {n m} θ := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro f
    change (OrdinaryBarFixedRowWordHom.augmentation C m.unop.len X Y).app k
        ((AmbientWords.map (literalMap C θ)
          (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k))).map f) =
      ULift.up ((literalMap C θ).map
        ((OrdinaryBarFixedRowWordHom.augmentation C n.unop.len X Y).app k f).down)
    rw [OrdinaryBarFixedRowWordHom.augmentation_app,
      OrdinaryBarFixedRowWordHom.augmentation_app]
    exact congrArg ULift.up (congr($(AmbientWords.map_augmentation (literalMap C θ)
      (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k))).map f))

lemma localized_augmentation_app (n : SimplexCategoryᵒᵖ) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((augmentation C X Y).app n)) :=
  OrdinaryBarFixedRowWordHom.localized_augmentation_isIso C n.unop.len X Y

def diagonal : SSet.{max u v} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (rows C X Y)

def targetDiagonal : SSet.{max u v} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (targetRows C X Y)

def diagonalAugmentation : diagonal C X Y ⟶ targetDiagonal C X Y :=
  CategoryTheory.Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
    (Functor.uncurry.map (augmentation C X Y))

def targetDiagonalIso : targetDiagonal C X Y ≅
    UniverseLift.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro f
    rfl)

def toSource : diagonal C X Y ⟶ UniverseLift.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) :=
  diagonalAugmentation C X Y ≫ (targetDiagonalIso C X Y).hom

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRows
