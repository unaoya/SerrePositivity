module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitFamilies
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SelectedLoopContraction

/-! # Selected unit comparisons against actual standard degeneracies

After base transport, both selected identity comparisons are loops at the
chosen interpolation. A triangle retains that selected loop on one side
and the actual standard degeneracy on both other sides. The original
strict-lift vertex boundary stays fixed throughout the contraction.
This is unit comparison data, not a strict normalization of all choices.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftUnitComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)

abbrev postComparisonMap : postChoiceSpace X Y Y f (𝟙 Y) ⟶ CoherentLiftRelative.obj X Y f :=
  RelativeChoiceSpace.postMap (vertexInclusion X Y f) _ _ (postCast X Y f)
    (post_boundary_unit X Y f hcof)
abbrev postLoop := postEdge hcof hfib X Y Y f (𝟙 Y) ≫ postComparisonMap hcof X Y f

lemma postLoop_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ postLoop hcof hfib X Y f =
    chosenPoint hcof X Y f := by
  rw [postLoop, ← Category.assoc, postEdge_at_zero]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ RelativeChoiceSpace.postMap _ _ _ _ _ = _
  rw [RelativeChoiceSpace.postMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (post_left_unit X Y f hcof)

lemma postLoop_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ postLoop hcof hfib X Y f =
    chosenPoint hcof X Y f := by
  rw [postLoop, ← Category.assoc, postEdge_at_one]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ RelativeChoiceSpace.postMap _ _ _ _ _ = _
  rw [RelativeChoiceSpace.postMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (post_right_unit X Y f hcof)

abbrev preComparisonMap : preChoiceSpace X X Y (𝟙 X) f ⟶ CoherentLiftRelative.obj X Y f :=
  RelativeChoiceSpace.postMap (vertexInclusion X Y f) _ _ (preCast X Y f)
    (pre_boundary_unit X Y f hcof)
abbrev preLoop := preEdge hcof hfib X X Y (𝟙 X) f (ResolutionLiftPrecomposition.identity X) ≫
  preComparisonMap hcof X Y f

lemma preLoop_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ preLoop hcof hfib X Y f =
    chosenPoint hcof X Y f := by
  rw [preLoop, ← Category.assoc, preEdge_at_zero]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ RelativeChoiceSpace.postMap _ _ _ _ _ = _
  rw [RelativeChoiceSpace.postMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (pre_left_unit X Y f hcof)

lemma preLoop_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ preLoop hcof hfib X Y f =
    chosenPoint hcof X Y f := by
  rw [preLoop, ← Category.assoc, preEdge_at_one]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ RelativeChoiceSpace.postMap _ _ _ _ _ = _
  rw [RelativeChoiceSpace.postMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (pre_right_unit X Y f hcof)

abbrev loop (post : Bool) := if post then postLoop hcof hfib X Y f else preLoop hcof hfib X Y f

lemma loop_zero (post : Bool) : SSet.stdSimplex.δ (1 : Fin 2) ≫ loop hcof hfib X Y f post =
    chosenPoint hcof X Y f := by
  cases post
  · exact preLoop_zero hcof hfib X Y f
  · exact postLoop_zero hcof hfib X Y f

lemma loop_one (post : Bool) : SSet.stdSimplex.δ (0 : Fin 2) ≫ loop hcof hfib X Y f post =
    chosenPoint hcof X Y f := by
  cases post
  · exact preLoop_one hcof hfib X Y f
  · exact postLoop_one hcof hfib X Y f

abbrev data (post : Bool) := SelectedLoopContraction.data (chosenPoint hcof X Y f)
  (loop hcof hfib X Y f post) (loop_zero hcof hfib X Y f post) (loop_one hcof hfib X Y f post)

def triangle (post : Bool) := SelectedLoopContraction.fill hcof hfib (vertexInclusion X Y f)
  (vertexData X Y f) (ResolutionLiftSpace.projection X Y f)
  (ResolutionLiftSpace.projection_trivialFibration hcof X Y f) (chosenPoint hcof X Y f)
  (loop hcof hfib X Y f post) (loop_zero hcof hfib X Y f post) (loop_one hcof hfib X Y f post)

@[reassoc (attr := simp)]
lemma triangle_face (post : Bool) (k : Fin 3) :
    SSet.stdSimplex.δ k ≫ triangle hcof hfib X Y f post = (data hcof hfib X Y f post).faces k :=
  SelectedLoopContraction.fill_face hcof hfib _ _ _ _ _ _ _ _ k

lemma triangle_fixed_boundary (post : Bool) :
    vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ≫
        RelativeChoiceSpace.family (vertexInclusion X Y f) (vertexData X Y f)
          (triangle hcof hfib X Y f post) =
      vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ vertexData X Y f :=
  SelectedTriangle.fill_fixed_boundary hcof hfib (vertexInclusion X Y f) (vertexData X Y f)
    (ResolutionLiftSpace.projection X Y f)
    (ResolutionLiftSpace.projection_trivialFibration hcof X Y f)
    (data hcof hfib X Y f post)

lemma triangle_action_face (post : Bool) (Z : C)
    (t : CoherentLiftTuples.obj X Y f ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶
      (cosimplicialHom Y.resolution.obj).obj Z) (k : Fin 3) :
    CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.δ k ≫
        KanLiftAction.parameterized hcof hfib X Y f Z
          (RelativeChoiceSpace.family (vertexInclusion X Y f) (vertexData X Y f)
            (triangle hcof hfib X Y f post)) t =
      KanLiftAction.parameterized hcof hfib X Y f Z
        (RelativeChoiceSpace.family (vertexInclusion X Y f) (vertexData X Y f)
          ((data hcof hfib X Y f post).faces k))
        ((CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.δ k) ≫ t) := by
  rw [KanLiftAction.parameterized_naturality, ← RelativeChoiceSpace.family_naturality,
    triangle_face]

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftUnitComparison
