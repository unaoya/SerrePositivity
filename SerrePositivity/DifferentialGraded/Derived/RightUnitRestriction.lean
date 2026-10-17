module
public import SerrePositivity.DifferentialGraded.Tensor.RightUnitRestriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparison
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionRightUnit
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionFamily

/-! # 対角の解像度で計算する導来中間比較と右単位子の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)
  (hD : localHomKFlat A D) (hF : HomQuasiIso F)

local notation "QF" => Functor.obj (rightKFlatLeftRestriction A C C D F)
  (rightKFlatDiagonal A C)
local notation "qF" => Bimodule.diagonalRestrictionMap A D C F
local notation "hqF" => Iff.mpr (Bimodule.diagonalRestrictionMap_quasiIso_iff A D C F) hF
local notation "LP" P => Functor.obj
  (BimoduleCategory.middleLeftRestrictionFunctor A B C D F) P

/-- Hom準同型性により対角を制限後の解像度に選ぶと、増大と計算同型が打ち消し合う。 -/
lemma rightUnitRestriction_source_computation (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B D D hD).map
        ((bimoduleToDerived A D D).map qF)).app ((bimoduleToDerived A B D).obj (LP P)) ≫
      (middleRestrictionSourceComputation A B C D D F hD P (QF).obj
        (rightKFlatDiagonal A D) qF hqF).hom =
    (derivedBimoduleComposeKFlatValueIso A B D D hD (rightKFlatDiagonal A D) (LP P)).hom := by
  have h := congrArg (fun k => k.app ((bimoduleToDerived A B D).obj (LP P)))
    (derivedBimoduleComposeResolutionComputation_fac A B D D hD _
      (rightKFlatDiagonal A D) qF hqF)
  change _ ≫ (_ ≫ 𝟙 _) = _
  rw [Category.comp_id]
  exact h

/-- 実際の導来中間比較を対角解像度で計算した右単位square。Cの局所Hom条件は不要。 -/
lemma derivedRightUnitRestriction_model (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B D D hD).map
        ((bimoduleToDerived A D D).map qF)).app ((bimoduleToDerived A B D).obj (LP P)) ≫
      derivedMiddleRestrictionComparison A B C D D F hD P QF
        (rightKFlatDiagonal A D) qF hqF ≫
      (derivedBimoduleComposeKFlatValueIso A B C D hD QF P).hom ≫
      (bimoduleToDerived A B D).map
        (composeLeftRestrictionIso A B C C D F P (rightKFlatDiagonal A C).obj).hom ≫
      (bimoduleToDerived A B D).map
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map
          (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom) =
    (derivedBimoduleRightUnitIso A B D hD).hom.app ((bimoduleToDerived A B D).obj (LP P)) := by
  unfold derivedMiddleRestrictionComparison
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, rightUnitRestriction_source_computation A B C D F hD hF P]
  rw [derivedBimoduleRightUnitIso_base_app]
  rw [← (bimoduleToDerived A B D).map_comp,
    ← (bimoduleToDerived A B D).map_comp]
  have h := rightUnitRestriction A B C D F P
  rw [← Category.assoc (composeMap A B D D (𝟙 (LP P)) qF)] at h
  change middleRestrictionResolvedMap A B C D D F P (QF).obj (rightKFlatDiagonal A D).obj qF ≫
      (composeLeftRestrictionIso A B C C D F P (rightKFlatDiagonal A C).obj).hom ≫
      (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map
        (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom =
    (rightBimoduleUnitIso A B D (BimoduleCategory.underlying A B D (LP P))).hom at h
  rw [h]

end SerrePositivity.DifferentialGraded.BimoduleTensor
