module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionCategory

/-! # Derived comparison spaces for actual outer-frame maps over a fixed inner map

Apply the existing lift-space construction in the canonical Reedy model of
cosimplicial diagrams. Original frame maps supply actual points. All value
spaces remain in the original Hom universe.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.FrameLiftSpace
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

variable {X Y : ResolutionObject C} (f : X ⟶ Y)

abbrev obj : SSet.{v} := ResolutionLiftSpace.obj (C := SimplexCategory ⥤ C)
  (ResolutionLiftPrecomposition.outer X) (ResolutionLiftPrecomposition.outer Y) f.diagram
abbrev projection : obj f ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) :=
  ResolutionLiftSpace.projection (C := SimplexCategory ⥤ C)
    (ResolutionLiftPrecomposition.outer X) (ResolutionLiftPrecomposition.outer Y) f.diagram

/-- The same actual frame map becomes an outer resolution morphism. -/
def outerMap (φ : ResolutionLiftPrecomposition.FrameMap f) :
    ResolutionLiftPrecomposition.outer X ⟶ ResolutionLiftPrecomposition.outer Y :=
  ⟨f.diagram, φ.val, φ.property⟩

def point (φ : ResolutionLiftPrecomposition.FrameMap f) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj f :=
  ResolutionLiftSpace.ofLift (C := SimplexCategory ⥤ C) (outerMap f φ)

lemma outerMap_diagram (φ : ResolutionLiftPrecomposition.FrameMap f) :
    (outerMap f φ).diagram = φ.val := rfl

def changeMap {g : X ⟶ Y} (h : f = g) (φ : ResolutionLiftPrecomposition.FrameMap g) :
    ResolutionLiftPrecomposition.FrameMap f := h.symm ▸ φ

lemma changeMap_val {g : X ⟶ Y} (h : f = g) (φ : ResolutionLiftPrecomposition.FrameMap g) :
    (changeMap f h φ).val = φ.val := by cases h; rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma projection_trivialFibration : trivialFibrations SSet.{v} (projection f) :=
  ResolutionLiftSpace.projection_trivialFibration (C := SimplexCategory ⥤ C) hcof
    (ResolutionLiftPrecomposition.outer X) (ResolutionLiftPrecomposition.outer Y) f.diagram

include hcof in
lemma extension {K L : SSet.{v}} (i : K ⟶ L) [Mono i] (s : K ⟶ obj f) :
    ∃ e : L ⟶ obj f, i ≫ e = s :=
  ResolutionLiftSpace.extension (C := SimplexCategory ⥤ C) hcof
    (ResolutionLiftPrecomposition.outer X) (ResolutionLiftPrecomposition.outer Y) f.diagram i s

include hcof in
lemma interval (φ ψ : ResolutionLiftPrecomposition.FrameMap f) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ obj f,
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ e = point f φ ∧
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ e = point f ψ :=
  ResolutionLiftSpace.interval (C := SimplexCategory ⥤ C) hcof
    (ResolutionLiftPrecomposition.outer X) (ResolutionLiftPrecomposition.outer Y) f.diagram
    (point f φ) (point f ψ)

include hcof in
lemma kanComplex (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp) :
    SSet.KanComplex (obj f) :=
  ResolutionLiftSpace.kanComplex (C := SimplexCategory ⥤ C) hcof hfib
    (ResolutionLiftPrecomposition.outer X) (ResolutionLiftPrecomposition.outer Y) f.diagram

end SerrePositivity.HomotopyFunctionComplex.FrameLiftSpace
