module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceBoundary

/-! # Higher comparison fillers from prescribed compatible composition faces

Individual face comparisons, agreeing on their actual intersections, are
glued and filled. The filler retains every prescribed face and fixes all
strict lift vertices throughout its higher parameter. No unprovided whole
boundary map is required as an input.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma post_fill_faces (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) (n : ℕ)
    (a : ∀ k, (BoundaryGluing.facet n k).toSSet ⟶ postChoiceSpace X Y W f g)
    (ha : BoundaryGluing.Compatible a) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ postChoiceSpace X Y W f g,
      (∀ k, (BoundaryGluing.facet n k).ι ≫ e = a k) ∧
      vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫
          RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y W f g) e =
        vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
          RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ postBoundary X Y W f g :=
  RelativeChoiceSpace.fill_faces hcof hfib _ _ (ResolutionLiftSpace.projection X W (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f ≫ g.base)) n a ha

include hcof hfib in
lemma pre_fill_faces (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) (n : ℕ)
    (a : ∀ k, (BoundaryGluing.facet n k).toSSet ⟶ preChoiceSpace X Y W f g)
    (ha : BoundaryGluing.Compatible a) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ preChoiceSpace X Y W f g,
      (∀ k, (BoundaryGluing.facet n k).ι ≫ e = a k) ∧
      vertexInclusion Y W g ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫
          RelativeChoiceSpace.family (vertexInclusion Y W g) (preBoundary X Y W f g) e =
        vertices Y W g ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
          RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ preBoundary X Y W f g :=
  RelativeChoiceSpace.fill_faces hcof hfib _ _ (ResolutionLiftSpace.projection X W (f.base ≫ g))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f.base ≫ g)) n a ha

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative
