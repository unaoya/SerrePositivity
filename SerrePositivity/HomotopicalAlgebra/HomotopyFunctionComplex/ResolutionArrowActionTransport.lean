module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftAction

/-! # Actual action transport along arbitrary simultaneous changes of centers and resolutions -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowDiagram

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionTransport
variable (C : Type u) [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev raw (q : Index C) (Z : C) {T : SSet.{v}} (s : T ⟶ (fibers C).obj q)
    (t : T ⟶ (cosimplicialHom (target C q).resolution.obj).obj Z) :=
  ResolutionLiftAction.parameterized (source C q).inner (target C q) (arrow C q) Z s t

/-- Every actual cube map transports the action by its two real resolution maps. -/
lemma raw_transport {q r : Index C} (f : q ⟶ r) (Z : C) {T : SSet.{v}}
    (s : T ⟶ (fibers C).obj q)
    (t : T ⟶ (cosimplicialHom (target C r).resolution.obj).obj Z) :
    raw C r Z (s ≫ (fibers C).map f) t =
    raw C q Z s (t ≫ (cosimplicialHomMap f.hom.2.diagram).app Z) ≫
      ResolutionLiftPrecomposition.rawTargetMap f.hom.1.unop.map
        (FramedResolution.frameMap f.hom.1.unop) Z := by
  change DiagonalHom.pairing _ _ _ ((s ≫ (fibers C).map f) ≫
    (FiberFunctor.inclusion (rawProjection C) (basepoint C)).app r) t = _
  rw [Category.assoc, map_inclusion, ← Category.assoc]
  change DiagonalHom.pairing _ _ _
    (((s ≫ (FiberFunctor.inclusion (rawProjection C) (basepoint C)).app q) ≫
      (cosimplicialHomMap f.hom.1.unop.frame).app (target C q).resolution.obj) ≫
        (cosimplicialHom (ResolutionLiftSpace.frame (source C r).inner).obj).map
          f.hom.2.diagram) t = _
  rw [DiagonalHom.pairing_middle_naturality, DiagonalHom.pairing_source_naturality]
  rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev kan (q : Index C) (Z : C) {T : SSet.{v}} (s : T ⟶ (fibers C).obj q)
    (t : T ⟶ (cosimplicialHom (target C q).resolution.obj).obj Z) :=
  KanLiftAction.parameterized hcof hfib (source C q).inner (target C q) (arrow C q) Z s t

lemma kan_transport {q r : Index C} (f : q ⟶ r) (Z : C) {T : SSet.{v}}
    (s : T ⟶ (fibers C).obj q)
    (t : T ⟶ (cosimplicialHom (target C r).resolution.obj).obj Z) :
    kan C hcof hfib r Z (s ≫ (fibers C).map f) t =
    kan C hcof hfib q Z s (t ≫ (cosimplicialHomMap f.hom.2.diagram).app Z) ≫
      ResolutionLiftPrecomposition.kanTargetMap hcof hfib f.hom.1.unop.map
        (FramedResolution.frameMap f.hom.1.unop) Z := by
  have hu := (KanReplacement.unit hcof hfib).naturality
    (ResolutionLiftPrecomposition.rawTargetMap f.hom.1.unop.map
      (FramedResolution.frameMap f.hom.1.unop) Z)
  change ResolutionLiftPrecomposition.rawTargetMap f.hom.1.unop.map
      (FramedResolution.frameMap f.hom.1.unop) Z ≫
      (KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target (source C r).inner Z) =
    (KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target (source C q).inner Z) ≫
      ResolutionLiftPrecomposition.kanTargetMap hcof hfib f.hom.1.unop.map
        (FramedResolution.frameMap f.hom.1.unop) Z at hu
  change raw C r Z (s ≫ (fibers C).map f) t ≫ _ = (raw C q Z s _ ≫ _) ≫ _
  rw [raw_transport, Category.assoc, hu, ← Category.assoc]

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionTransport
