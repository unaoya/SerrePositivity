module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance

/-! # A proved small finite-boundary kernel on the full presentation index

The relation is constructed, not an input certificate. Its base is the
category of actual resolution presentations. Descent to Cᵒᵖ × C is not
asserted, and no section of the presentation projection is chosen.
-/

@[expose] public section
universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.PresentationKernelQuotient
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev reference : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  MixedBiresolutionComparison.functor ⋙ AnodyneKanReplacement.functor

def referenceComparison : MixedBiresolutionComparison.functor (C := C) ⟶ reference :=
  Functor.whiskerLeft MixedBiresolutionComparison.functor AnodyneKanReplacement.unit

def toReference : OrdinaryResolutionBar.middle (C := C) ⟶
    reference ⋙ SSet.uliftFunctor.{max u v, v} :=
  OrdinaryResolutionBar.left ≫ Functor.whiskerRight referenceComparison SSet.uliftFunctor

lemma reference_kan (R : RightResolutionMapping.Index C) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (reference.obj R)) :=
  AnodyneKanReplacement.terminal_rlp _

lemma toReference_localized_isIso (R : RightResolutionMapping.Index C) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((toReference (C := C)).app R)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have : IsIso (Q.map ((OrdinaryResolutionBar.left (C := C)).app R)) := by
    change IsIso ((OrdinaryResolutionBar.leftAnodyneIso (C := C)).hom.app R)
    infer_instance
  have : IsIso (Q.map (SSet.uliftFunctor.{max u v, v}.map
      ((referenceComparison (C := C)).app R))) :=
    UniverseLift.anodyneQ_lift_inverts _ (AnodyneKanReplacement.unit_anodyne _)
  change IsIso (Q.map ((OrdinaryResolutionBar.left (C := C)).app R ≫
    SSet.uliftFunctor.{max u v, v}.map ((referenceComparison (C := C)).app R)))
  rw [Q.map_comp]
  infer_instance

abbrev enlarged : RightResolutionMapping.Index C ⥤ SSet.{max u v} :=
  SmallTargetKernelQuotient.middle (toReference (C := C))

abbrev relation : DiagramQuotient.Congruence (enlarged (C := C)) :=
  SmallTargetKernelQuotient.relation toReference

lemma quotient_small (R : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ) :
    Small.{v} (Quotient ((relation (C := C)).rel R n)) :=
  SmallTargetKernelQuotient.quotient_small toReference R n

lemma quotient_boundary_rlp (R : RightResolutionMapping.Index C) :
    SSet.modelCategoryQuillen.I.rlp ((DiagramQuotient.projection (relation (C := C))).app R) :=
  SmallTargetKernelQuotient.quotient_boundary_rlp toReference reference_kan
    toReference_localized_isIso R

abbrev functor : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  SmallDiagramQuotient.functor relation quotient_small

lemma terminal_rlp (R : RightResolutionMapping.Index C) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from ((functor (C := C)).obj R)) :=
  SmallDiagramQuotient.kan relation quotient_small quotient_boundary_rlp R
    (SmallTargetKernelQuotient.middle_kan toReference reference_kan R)

def left : OrdinaryResolutionBar.middle (C := C) ⟶
    functor ⋙ SSet.uliftFunctor.{max u v, v} :=
  SmallTargetKernelQuotient.unit toReference ≫
    SmallDiagramQuotient.projection relation quotient_small

lemma left_localized_isIso (R : RightResolutionMapping.Index C) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((left (C := C)).app R)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have : IsIso (Q.map ((SmallTargetKernelQuotient.unit (toReference (C := C))).app R)) :=
    Localization.inverts Q _ _ (SmallTargetKernelQuotient.unit_anodyne toReference R)
  have : IsIso (Q.map ((SmallDiagramQuotient.projection
      (relation (C := C)) quotient_small).app R)) :=
    MonoRightLiftingContraction.image_isIso _
      (SmallDiagramQuotient.projection_mono_rlp relation quotient_small quotient_boundary_rlp R)
      Q (Localization.inverts Q _)
  change IsIso (Q.map (_ ≫ _))
  rw [Q.map_comp]
  infer_instance

def leftImageIso {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    OrdinaryResolutionBar.middle (C := C) ⋙ L ≅
      (functor ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ L := by
  have (R : RightResolutionMapping.Index C) : IsIso ((Functor.whiskerRight
      (SmallTargetKernelQuotient.unit (toReference (C := C))) L).app R) :=
    hL _ (SmallTargetKernelQuotient.unit_anodyne toReference R)
  have : IsIso (Functor.whiskerRight (SmallTargetKernelQuotient.unit
      (toReference (C := C))) L) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerRight (SmallTargetKernelQuotient.unit toReference) L) ≪≫
    SmallDiagramQuotient.imageIso relation quotient_small quotient_boundary_rlp L hL

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def baseComparisonIso {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    (functor (C := C) ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
      (RightResolutionMapping.projection ⋙ OrdinaryResolutionBar.functor) ⋙ L := by
  have := OrdinaryBarMappingComparison.right_isIso (C := C) hcof hfib L hL
  exact (leftImageIso L hL).symm ≪≫
    asIso (Functor.whiskerRight OrdinaryResolutionBar.right L)

include hcof hfib in
lemma map_weakEquivalence {R S : RightResolutionMapping.Index C} (f : R ⟶ S)
    (hs : weakEquivalences C ((RightResolutionMapping.projection.map f).1.unop))
    (ht : weakEquivalences C ((RightResolutionMapping.projection.map f).2)) :
    weakEquivalences SSet.{v} ((functor (C := C)).map f) := by
  apply (UniverseLift.weakEquivalences_iff_lift_anodyneQ_isIso hcof hfib _).mpr
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  exact (NatIso.isIso_map_iff (baseComparisonIso hcof hfib Q (Localization.inverts Q _)) f).mpr
    (OrdinaryBarBaseInvariance.localized_map_isIso hcof hfib _ hs ht)

end SerrePositivity.HomotopyFunctionComplex.PresentationKernelQuotient
