module
public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction
public import SerrePositivity.DifferentialGraded.Derived.PairedRestrictionIdentification
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionRightUnit

/-! # 既存の同時導来制限に沿う対角bimoduleの比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- Hom写像を局所化し、既存の同時導来制限表示へ送る対角比較射。 -/
def derivedDiagonalRestrictionMap :
    (bimoduleToDerived A D D).obj (rightKFlatDiagonal A D).obj ⟶
      (derivedBimoduleRestriction A D D E E F F).obj
        ((bimoduleToDerived A E E).obj (rightKFlatDiagonal A E).obj) :=
  (bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D E F) ≫
    (pairedRestrictionDerivedIso A E E D D F F).hom.app (rightKFlatDiagonal A E).obj

/-- Homがすべて準同型なら、対角比較は既存の導来bimodule圏上の同型。 -/
def derivedDiagonalRestrictionIso (hF : HomQuasiIso F) :
    (bimoduleToDerived A D D).obj (rightKFlatDiagonal A D).obj ≅
      (derivedBimoduleRestriction A D D E E F F).obj
        ((bimoduleToDerived A E E).obj (rightKFlatDiagonal A E).obj) :=
  bimoduleDerivedIso A D D (Bimodule.diagonalRestrictionMap A D E F)
      ((Bimodule.diagonalRestrictionMap_quasiIso_iff A D E F).2 hF) ≪≫
    (pairedRestrictionDerivedIso A E E D D F F).app (rightKFlatDiagonal A E).obj

lemma derivedDiagonalRestrictionIso_hom (hF : HomQuasiIso F) :
    (derivedDiagonalRestrictionIso A D E F hF).hom = derivedDiagonalRestrictionMap A D E F := rfl

lemma derivedDiagonalRestrictionMap_isIso (hF : HomQuasiIso F) :
    IsIso (derivedDiagonalRestrictionMap A D E F) := by
  rw [← derivedDiagonalRestrictionIso_hom A D E F hF]
  infer_instance

end SerrePositivity.DifferentialGraded.BimoduleTensor
