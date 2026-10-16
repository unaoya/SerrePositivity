module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameLiftSpace

/-! # Comparing the two actual framed paths of an inner commuting square

Equality is required only for the underlying resolution maps. The original
outer-frame composites supply points in one fixed derived comparison space.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.FrameSquareComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {A B D E : FramedResolution C} (s : A ⟶ B) (t : B ⟶ E) (u : A ⟶ D) (v : D ⟶ E)
  (h : (s ≫ t).map = (u ≫ v).map)
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev obj : SSet.{v} := FrameLiftSpace.obj (s ≫ t).map
abbrev leftFrame : ResolutionLiftPrecomposition.FrameMap (s ≫ t).map :=
  FramedResolution.frameMap (s ≫ t)
abbrev rightFrame : ResolutionLiftPrecomposition.FrameMap (s ≫ t).map :=
  FrameLiftSpace.changeMap (s ≫ t).map h (FramedResolution.frameMap (u ≫ v))
abbrev leftPoint : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj s t :=
  FrameLiftSpace.point _ (leftFrame s t)
abbrev rightPoint : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj s t :=
  FrameLiftSpace.point _ (rightFrame s t u v h)

lemma leftFrame_val : (leftFrame s t).val = s.frame ≫ t.frame := rfl
lemma rightFrame_val : (rightFrame s t u v h).val = u.frame ≫ v.frame :=
  FrameLiftSpace.changeMap_val _ h _

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma interval : ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ obj s t,
    SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ e = leftPoint s t ∧
    SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ e = rightPoint s t u v h :=
  FrameLiftSpace.interval _ hcof (leftFrame s t) (rightFrame s t u v h)

include hcof in
lemma extension {K L : SSet.{v}} (i : K ⟶ L) [Mono i] (boundary : K ⟶ obj s t) :
    ∃ e : L ⟶ obj s t, i ≫ e = boundary := FrameLiftSpace.extension _ hcof i boundary

end SerrePositivity.HomotopyFunctionComplex.FrameSquareComparison
