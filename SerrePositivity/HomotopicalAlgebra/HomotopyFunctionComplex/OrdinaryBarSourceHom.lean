module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation

/-! # The actual outer source Hom simplicial set and its base augmentation -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceHom
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarFixedSource
variable (C : Type u) [Category.{v} C] (X Y : D C)

def hom : SSet.{max u v} where
  obj n := @Quiver.Hom ((diagram C).obj n) ((diagram C).obj n).str.toQuiver X Y
  map θ := ↾fun f => (literalMap C θ).map f
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congrArg Cat.Hom.toFunctor ((literal C).map_id n)
    exact congr($(h).map f)
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congrArg Cat.Hom.toFunctor ((literal C).map_comp θ φ)
    exact congr($(h).map f)

def augmentation : UniverseLift.obj.{max u v} (hom C X Y) ⟶
    OrdinaryBarDiagonalHomAugmentation.baseHom C X Y where
  app n := ↾fun f => ULift.up ((OrdinaryBarFixedAugmentation.sourceProjection C n).map f.down)
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congr($(OrdinaryBarFixedAugmentation.sourceProjection_naturality C θ).map f.down)
    exact congrArg ULift.up h

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceHom
