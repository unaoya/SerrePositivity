module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ConeModule
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.CommaKernelCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ConeRepresentative

/-! 代表 cone と同じ実比較射の移送から gluing の cone 対象候補を構成する。Hom の cone 表現可能性は別証明。 -/
@[expose] public section
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
  SerrePositivity.InfinityCategories
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (A B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) A ⟶ ForgetEnrichment.of (Complex R) B)

def dgGluingConeLeftArrow :
    ForgetEnrichment.of (Complex R) (representable R A.left) ⟶
      ForgetEnrichment.of (Complex R) (representable R B.left) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M B)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)

def dgGluingConeRightArrow :
    ForgetEnrichment.of (Complex R) A.right ⟶ ForgetEnrichment.of (Complex R) B.right :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R D (RightModule R C) M.toFunctor).onClosed.map
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)

variable
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C A.left B.left (dgGluingConeLeftArrow R C D M A B f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D A.right B.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M A B f)))

def dgGluingConeAugmentation :
    ForgetEnrichment.of (Complex R) (representable R p.obj) ⟶
      ForgetEnrichment.of (Complex R) (M.rightAt q.obj) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeInv R C A.left B.left (dgGluingConeLeftArrow R C D M A B f) p ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeMorphism R C D M A B f ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelConeIso R C D M
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M B)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)).hom ≫
    (Morita.kernelTensor R D C M).onClosed.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeHom R D A.right B.right
        ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M A B f)) q) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) q.obj)).hom

def dgGluingConeObjectFromRepresentatives : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M where
  left := p.obj
  right := q.obj
  gluing := cycleFromUnit _
    (ForgetEnrichment.homTo (Complex R) (dgGluingConeAugmentation R C D M A B f p q) ≫
      (dgYonedaIso R p.obj (M.rightAt q.obj)).hom)

lemma dgGluingConeObject_augmentation :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M (dgGluingConeObjectFromRepresentatives R C D M A B f p q) =
      dgGluingConeAugmentation R C D M A B f p q := by
  change unitFromCycle _ (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex R) (dgGluingConeAugmentation R C D M A B f p q) ≫
      (dgYonedaIso R p.obj (M.rightAt q.obj)).hom)) ≫
        (dgYonedaIso R p.obj (M.rightAt q.obj)).inv = _
  rw [unitFromCycle_cycleFromUnit]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

def dgGluingConeObject (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M :=
  dgGluingConeObjectFromRepresentatives R C D M A B f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseConeRepresentative R C A.left B.left
      (dgGluingConeLeftArrow R C D M A B f) hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseConeRepresentative R D A.right B.right
      ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M A B f)) hD)

def dgGluingConeObject_leftIso (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    (moduleToHomotopy R C).obj (moduleCone R C (dgGluingConeLeftArrow R C D M A B f)) ≅
    (moduleToHomotopy R C).obj (ForgetEnrichment.of (Complex R)
      (representable R (dgGluingConeObject R C D M A B f hC hD).left)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseConeRepresentative R C A.left B.left
    (dgGluingConeLeftArrow R C D M A B f) hC).comparison

def dgGluingConeObject_rightIso (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    (moduleToHomotopy R D).obj (moduleCone R D ((dgYoneda R D).onClosed.map
      (dgGluingConeRightArrow R C D M A B f))) ≅
    (moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R)
      (representable R (dgGluingConeObject R C D M A B f hC hD).right)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseConeRepresentative R D A.right B.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M A B f)) hD).comparison

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
