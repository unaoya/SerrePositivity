module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionRows
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarReindex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison

/-! # A strict ordinary-resolution bar with an actual comparison from the original framed bar

The original raw mapping spaces factor strictly through forgetting outer frames.
The natural comparison span retains its old source, middle, and left leg.
No weak equivalence of the new right leg is asserted here.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionBar
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev functor : Cᵒᵖ × C ⥤ SSet.{max u v} :=
  BarConstruction.relative (OrdinaryResolutionPairs.projection (C := C)) OrdinaryResolutionPairs.raw
abbrev framed : Cᵒᵖ × C ⥤ SSet.{max u v} :=
  BarConstruction.relative (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor

/-- Every original comma chain is sent by the actual forgetful functor, with its original labels. -/
def comparison : framed (C := C) ⟶ functor :=
  BarConstruction.reindex OrdinaryResolutionPairs.forgetFrames OrdinaryResolutionPairs.projection
    OrdinaryResolutionPairs.raw

lemma comparison_label (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ)
    (c : ((framed (C := C)).obj b).obj n) (i : Fin (n.unop.len + 1)) :
    ((((comparison (C := C)).app b).app n c).obj i).left.val = (c.obj i).left.val := rfl

abbrev middle : RightResolutionMapping.Index C ⥤ SSet.{max u v} :=
  BarConstruction.spanMiddle (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor
abbrev left : middle (C := C) ⟶ MixedBiresolutionComparison.functor ⋙
    SSet.uliftFunctor.{max u v, v} :=
  BarConstruction.spanLeft (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor

def right : middle (C := C) ⟶ RightResolutionMapping.projection ⋙ functor :=
  BarConstruction.spanRight (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor ≫
      Functor.whiskerLeft RightResolutionMapping.projection comparison

/-- The old left comparison remains the actual natural isomorphism after anodyne inversion. -/
abbrev leftAnodyneIso : middle (C := C) ⋙ AnodyneHomotopy.anodyneQ ≅
    (MixedBiresolutionComparison.functor ⋙ SSet.uliftFunctor.{max u v, v}) ⋙
      AnodyneHomotopy.anodyneQ :=
  BarConstruction.spanLeftAnodyneIso (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor

lemma leftAnodyneIso_hom (R : RightResolutionMapping.Index C) :
    (leftAnodyneIso (C := C)).hom.app R =
      AnodyneHomotopy.anodyneQ.map ((left (C := C)).app R) := rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionBar
