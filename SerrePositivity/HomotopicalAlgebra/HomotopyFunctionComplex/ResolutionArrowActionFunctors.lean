module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingBifunctor

/-! # The two strict endpoint functors underlying actual resolution-lift actions -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex ResolutionArrowDiagram

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionFunctors
variable (C : Type u) [Category.{v} C] [ModelCategory C]

abbrev targetResolution : Index C ⥤ ResolutionObject C :=
  forget C ⋙ CategoryTheory.Prod.snd _ _
abbrev sourceResolution : Index C ⥤ (FramedResolution C)ᵒᵖ :=
  forget C ⋙ CategoryTheory.Prod.fst _ _

/-- Contravariant input transport is the actual resolution Hom functor. -/
abbrev input (Z : C) : (Index C)ᵒᵖ ⥤ SSet.{v} :=
  (targetResolution C).op ⋙ ResolutionObject.diagrams.op ⋙ cosimplicialHomBifunctor ⋙
    (evaluation C SSet.{v}).obj Z

lemma input_map {q r : Index C} (f : q ⟶ r) (Z : C) :
    (input C Z).map f.op = (cosimplicialHomMap f.hom.2.diagram).app Z := rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- Covariant output transport uses the same existing strict framed Kan Hom functor. -/
abbrev output (Z : C) : Index C ⥤ SSet.{v} :=
  sourceResolution C ⋙ FramedResolution.hom hcof hfib ⋙ (evaluation C SSet.{v}).obj Z

lemma output_map {q r : Index C} (f : q ⟶ r) (Z : C) :
    (output C hcof hfib Z).map f =
    ResolutionLiftPrecomposition.kanTargetMap hcof hfib f.hom.1.unop.map
      (FramedResolution.frameMap f.hom.1.unop) Z := rfl

/-- Both endpoint transports in the action are actual functor maps, with strict unit/composition. -/
lemma transport {q r : Index C} (f : q ⟶ r) (Z : C) {T : SSet.{v}}
    (s : T ⟶ (fibers C).obj q) (t : T ⟶ (input C Z).obj (Opposite.op r)) :
    ResolutionArrowActionTransport.kan C hcof hfib r Z (s ≫ (fibers C).map f) t =
    ResolutionArrowActionTransport.kan C hcof hfib q Z s (t ≫ (input C Z).map f.op) ≫
      (output C hcof hfib Z).map f :=
  ResolutionArrowActionTransport.kan_transport C hcof hfib f Z s t

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionFunctors
