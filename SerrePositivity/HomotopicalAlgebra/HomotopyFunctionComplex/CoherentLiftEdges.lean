module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceMaps

/-! # Selected relative composition edges with exact endpoints

The interval parameters live in the actual relative choice spaces. Keeping
these parameters, rather than only their evaluated homotopies, allows
transport and gluing with their already specified endpoints retained.
No unit or associativity law for these independent choices is asserted.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev postLeftPoint (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :=
  RelativeChoiceSpace.ofExtension (vertexInclusion X Y f) (postBoundary X Y W f g)
    (postLeft hcof X Y W f g) (postLeft_vertices hcof X Y W f g)

abbrev postRightPoint (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :=
  RelativeChoiceSpace.ofExtension (vertexInclusion X Y f) (postBoundary X Y W f g)
    (postRight hcof X Y W f g) (postRight_vertices hcof X Y W f g)

def postEdge (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ postChoiceSpace X Y W f g :=
  (RelativeChoiceSpace.interval hcof hfib _ _ (ResolutionLiftSpace.projection X W (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f ≫ g.base))
    (postLeftPoint hcof X Y W f g) (postRightPoint hcof X Y W f g)).choose

@[reassoc (attr := simp)]
lemma postEdge_at_zero (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ postEdge hcof hfib X Y W f g = postLeftPoint hcof X Y W f g :=
  (RelativeChoiceSpace.interval hcof hfib _ _ (ResolutionLiftSpace.projection X W (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f ≫ g.base))
    (postLeftPoint hcof X Y W f g) (postRightPoint hcof X Y W f g)).choose_spec.1

@[reassoc (attr := simp)]
lemma postEdge_at_one (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ postEdge hcof hfib X Y W f g = postRightPoint hcof X Y W f g :=
  (RelativeChoiceSpace.interval hcof hfib _ _ (ResolutionLiftSpace.projection X W (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f ≫ g.base))
    (postLeftPoint hcof X Y W f g) (postRightPoint hcof X Y W f g)).choose_spec.2

abbrev preLeftPoint (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :=
  RelativeChoiceSpace.ofExtension (vertexInclusion Y W g) (preBoundary X Y W f g)
    (preLeft hcof X Y W f g φ) (preLeft_vertices hcof X Y W f g φ)

abbrev preRightPoint (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) :=
  RelativeChoiceSpace.ofExtension (vertexInclusion Y W g) (preBoundary X Y W f g)
    (preRight hcof X Y W f g) (preRight_vertices hcof X Y W f g)

def preEdge (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ preChoiceSpace X Y W f g :=
  (RelativeChoiceSpace.interval hcof hfib _ _ (ResolutionLiftSpace.projection X W (f.base ≫ g))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f.base ≫ g))
    (preLeftPoint hcof X Y W f g φ) (preRightPoint hcof X Y W f g)).choose

@[reassoc (attr := simp)]
lemma preEdge_at_zero (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ preEdge hcof hfib X Y W f g φ =
      preLeftPoint hcof X Y W f g φ :=
  (RelativeChoiceSpace.interval hcof hfib _ _ (ResolutionLiftSpace.projection X W (f.base ≫ g))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f.base ≫ g))
    (preLeftPoint hcof X Y W f g φ) (preRightPoint hcof X Y W f g)).choose_spec.1

@[reassoc (attr := simp)]
lemma preEdge_at_one (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ preEdge hcof hfib X Y W f g φ =
      preRightPoint hcof X Y W f g :=
  (RelativeChoiceSpace.interval hcof hfib _ _ (ResolutionLiftSpace.projection X W (f.base ≫ g))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f.base ≫ g))
    (preLeftPoint hcof X Y W f g φ) (preRightPoint hcof X Y W f g)).choose_spec.2

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative
