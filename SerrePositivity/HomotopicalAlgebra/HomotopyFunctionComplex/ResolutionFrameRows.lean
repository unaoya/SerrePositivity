module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionCategory
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingRows

/-! # Every actual outer-frame row is a resolution of the original base

The augmented row is obtained by composition of two trivial Reedy fibrations.
All row operators are actual maps over the identity of the same base.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionFrameRows
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := simplexModelCategory C

lemma rowAugmentation_trivial (X : ResolutionObject C) (n : SimplexCategory) :
    trivialFibrations (SimplexCategory ⥤ C) ((ResolutionLiftSpace.frame X).augmentation.app n) :=
  trivialFibration_app simplex (ResolutionLiftSpace.frame X).augmentation
    (ResolutionLiftSpace.frame X).trivial n

def row (X : ResolutionObject C) (n : SimplexCategory) : ResolutionObject C where
  base := X.base
  resolution :=
    { obj := (ResolutionLiftSpace.frame X).obj.obj n
      augmentation := (ResolutionLiftSpace.frame X).augmentation.app n ≫ X.resolution.augmentation
      cofibrant := DiagonalMappingRows.row_cofibrant (ResolutionLiftSpace.frame X) n
      trivial := by
        apply (reedyRight_trivialFibrations_iff simplex _).mpr
        exact (trivialFibrations (SimplexCategory ⥤ C)).comp_mem _ _
          (rowAugmentation_trivial X n)
          ((reedyRight_trivialFibrations_iff simplex _).mp X.resolution.trivial) }

/-- The same actual row augmentation, now a map of resolutions over the identity. -/
def augmentation (X : ResolutionObject C) (n : SimplexCategory) : row X n ⟶ X where
  base := 𝟙 X.base
  diagram := (ResolutionLiftSpace.frame X).augmentation.app n
  over := by
    change _ = _ ≫ (Functor.const SimplexCategory).map (𝟙 X.base)
    rw [(Functor.const SimplexCategory).map_id, Category.comp_id]
    rfl

lemma row_operator_augmentation (X : ResolutionObject C) {n m : SimplexCategory} (θ : n ⟶ m) :
    (ResolutionLiftSpace.frame X).obj.map θ ≫ (ResolutionLiftSpace.frame X).augmentation.app m =
      (ResolutionLiftSpace.frame X).augmentation.app n := by
  have h := (ResolutionLiftSpace.frame X).augmentation.naturality θ
  change _ = _ ≫ 𝟙 X.resolution.obj at h
  simpa only [Category.comp_id] using h

def rowMap (X : ResolutionObject C) {n m : SimplexCategory} (θ : n ⟶ m) : row X n ⟶ row X m where
  base := 𝟙 X.base
  diagram := (ResolutionLiftSpace.frame X).obj.map θ
  over := by
    change _ ≫ (_ ≫ X.resolution.augmentation) =
      (_ ≫ X.resolution.augmentation) ≫ (Functor.const SimplexCategory).map (𝟙 X.base)
    rw [(Functor.const SimplexCategory).map_id, Category.comp_id, ← Category.assoc,
      row_operator_augmentation]

def functor (X : ResolutionObject C) : SimplexCategory ⥤ ResolutionObject C where
  obj := row X
  map θ := rowMap X θ
  map_id n := by
    apply ResolutionObject.Hom.ext
    · rfl
    · exact (ResolutionLiftSpace.frame X).obj.map_id n
  map_comp θ σ := by
    apply ResolutionObject.Hom.ext
    · exact (Category.id_comp _).symm
    · exact (ResolutionLiftSpace.frame X).obj.map_comp θ σ

/-- The entire row diagram augments to the original resolution. -/
def comparison (X : ResolutionObject C) : functor X ⟶ (Functor.const SimplexCategory).obj X where
  app := augmentation X
  naturality {n m} θ := by
    apply ResolutionObject.Hom.ext
    · rfl
    · change _ = (ResolutionLiftSpace.frame X).augmentation.app n ≫ 𝟙 _
      rw [Category.comp_id]
      exact row_operator_augmentation X θ

lemma augmentation_base (X : ResolutionObject C) (n : SimplexCategory) :
    (augmentation X n).base = 𝟙 X.base := rfl

lemma rowMap_base (X : ResolutionObject C) {n m : SimplexCategory} (θ : n ⟶ m) :
    (rowMap X θ).base = 𝟙 X.base := rfl

end SerrePositivity.HomotopyFunctionComplex.ResolutionFrameRows
