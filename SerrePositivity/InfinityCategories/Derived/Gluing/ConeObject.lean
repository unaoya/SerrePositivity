module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeModule
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaKernelCone
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeRepresentative

/-! 代表 cone と同じ実比較射の移送から gluing の cone 対象候補を構成する。Hom の cone 表現可能性は別証明。 -/
@[expose] public section
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
  SerrePositivity.InfinityCategories
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (A B : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) A ⟶ ForgetEnrichment.of (Complex R) B)

def dgGluingConeLeftArrow :
    ForgetEnrichment.of (Complex R) (representable R A.left) ⟶
      ForgetEnrichment.of (Complex R) (representable R B.left) :=
  dgGluingCommaClosedReplacementMap R C D M
    (dgGluingCommaObject R C D M A) (dgGluingCommaObject R C D M B)
    ((dgGluingToComma R C D M).onClosed.map f)

def dgGluingConeRightArrow :
    ForgetEnrichment.of (Complex R) A.right ⟶ ForgetEnrichment.of (Complex R) B.right :=
  (dgFunctorCommaSource R D (RightModule R C) M.toFunctor).onClosed.map
    ((dgGluingToComma R C D M).onClosed.map f)

variable
  (p : DGGluingConeRepresentative R C A.left B.left (dgGluingConeLeftArrow R C D M A B f))
  (q : DGGluingConeRepresentative R D A.right B.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M A B f)))

def dgGluingConeAugmentation :
    ForgetEnrichment.of (Complex R) (representable R p.obj) ⟶
      ForgetEnrichment.of (Complex R) (M.rightAt q.obj) :=
  dgGluingConeRepresentativeInv R C A.left B.left (dgGluingConeLeftArrow R C D M A B f) p ≫
    dgGluingConeMorphism R C D M A B f ≫
    (dgGluingCommaKernelConeIso R C D M
      (dgGluingCommaObject R C D M A) (dgGluingCommaObject R C D M B)
      ((dgGluingToComma R C D M).onClosed.map f)).hom ≫
    (Morita.kernelTensor R D C M).onClosed.map
      (dgGluingConeRepresentativeHom R D A.right B.right
        ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M A B f)) q) ≫
    (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) q.obj)).hom

def dgGluingConeObjectFromRepresentatives : DGGluingObject R C D M where
  left := p.obj
  right := q.obj
  gluing := cycleFromUnit _
    (ForgetEnrichment.homTo (Complex R) (dgGluingConeAugmentation R C D M A B f p q) ≫
      (dgYonedaIso R p.obj (M.rightAt q.obj)).hom)

lemma dgGluingConeObject_augmentation :
    dgGluingAugmentation R C D M (dgGluingConeObjectFromRepresentatives R C D M A B f p q) =
      dgGluingConeAugmentation R C D M A B f p q := by
  change unitFromCycle _ (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex R) (dgGluingConeAugmentation R C D M A B f p q) ≫
      (dgYonedaIso R p.obj (M.rightAt q.obj)).hom)) ≫
        (dgYonedaIso R p.obj (M.rightAt q.obj)).inv = _
  rw [unitFromCycle_cycleFromUnit]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

def dgGluingConeObject (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    DGGluingObject R C D M :=
  dgGluingConeObjectFromRepresentatives R C D M A B f
    (dgGluingChooseConeRepresentative R C A.left B.left
      (dgGluingConeLeftArrow R C D M A B f) hC)
    (dgGluingChooseConeRepresentative R D A.right B.right
      ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M A B f)) hD)

def dgGluingConeObject_leftIso (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    (moduleToHomotopy R C).obj (moduleCone R C (dgGluingConeLeftArrow R C D M A B f)) ≅
    (moduleToHomotopy R C).obj (ForgetEnrichment.of (Complex R)
      (representable R (dgGluingConeObject R C D M A B f hC hD).left)) :=
  (dgGluingChooseConeRepresentative R C A.left B.left
    (dgGluingConeLeftArrow R C D M A B f) hC).comparison

def dgGluingConeObject_rightIso (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    (moduleToHomotopy R D).obj (moduleCone R D ((dgYoneda R D).onClosed.map
      (dgGluingConeRightArrow R C D M A B f))) ≅
    (moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R)
      (representable R (dgGluingConeObject R C D M A B f hC hD).right)) :=
  (dgGluingChooseConeRepresentative R D A.right B.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M A B f)) hD).comparison

end SerrePositivity.InfinityCategories
