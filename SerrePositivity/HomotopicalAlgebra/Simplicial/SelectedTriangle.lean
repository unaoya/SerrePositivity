module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceBoundary

/-! # Filling a triangle from its specified edges and endpoints

Compatibility is derived from the six endpoint equations. The filler in
a fixed-boundary choice space retains all specified edges and keeps the
original boundary fixed throughout the whole triangle.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.SelectedTriangle

structure Boundary (P : SSet.{v}) where
  vertex0 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ P
  vertex1 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ P
  vertex2 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ P
  edge01 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ P
  edge12 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ P
  edge02 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ P
  edge01_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ edge01 = vertex0
  edge01_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ edge01 = vertex1
  edge12_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ edge12 = vertex1
  edge12_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ edge12 = vertex2
  edge02_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ edge02 = vertex0
  edge02_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ edge02 = vertex2

abbrev Boundary.faces {P : SSet.{v}} (d : Boundary P) :
    Fin 3 → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ P) :=
  ![d.edge12, d.edge02, d.edge01]

lemma Boundary.compatible {P : SSet.{v}} (d : Boundary P) :
    BoundaryGluing.StandardCompatible d.faces := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;> norm_num at hjk
  · exact d.edge12_one.trans d.edge02_one.symm
  · exact d.edge12_zero.trans d.edge01_one.symm
  · exact d.edge02_zero.trans d.edge01_zero.symm

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def fill {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (d : Boundary (RelativeChoiceSpace.obj i b)) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ RelativeChoiceSpace.obj i b :=
  (RelativeChoiceSpace.fill_standard_faces hcof hfib i b p hp 0 d.faces d.compatible).choose

@[reassoc (attr := simp)]
lemma fill_face {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (d : Boundary (RelativeChoiceSpace.obj i b)) (k : Fin 3) :
    SSet.stdSimplex.δ k ≫ fill hcof hfib i b p hp d = d.faces k :=
  (RelativeChoiceSpace.fill_standard_faces hcof hfib i b p hp 0
    d.faces d.compatible).choose_spec.1 k

lemma fill_fixed_boundary {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (d : Boundary (RelativeChoiceSpace.obj i b)) :
    i ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ≫
        RelativeChoiceSpace.family i b (fill hcof hfib i b p hp d) =
      V ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
        (ρ_ V).hom ≫ b :=
  (RelativeChoiceSpace.fill_standard_faces hcof hfib i b p hp 0 d.faces d.compatible).choose_spec.2

end SerrePositivity.SimplicialModel.SelectedTriangle
